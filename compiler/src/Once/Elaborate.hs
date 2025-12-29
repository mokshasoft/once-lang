module Once.Elaborate
  ( elaborate
  , elaborateWithEnv
  , elaborateExpr
  , elaborateType
  , ElabError (..)
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T

import MAlonzo.RTE (coe)
import Once.IR (IR (..))
import Once.Syntax (Expr (..), SType (..), Name, Decl (..), ModuleName, BinOp (..), UnaryOp (..))
import Once.Type (Type (..))
import Once.Module (ModuleEnv, lookupQualified, DeclInfo (..), ModuleError)
import qualified MAlonzo.Code.Once.Arith.IR as MA
import qualified MAlonzo.Code.Once.Arith.Type as MT

-- | Helper: empty context for MAlonzo ArithIR (erased at runtime)
emptyCtx :: [MA.T_Binding_6]
emptyCtx = MA.d_'8709'_20

-- | Helper: check if NumType is float
isFloat :: MT.T_NumType_6 -> Bool
isFloat MT.C_F32_16 = True
isFloat MT.C_F64_18 = True
isFloat _           = False

-- | Helper: get bitwidth of NumType
bitwidth :: MT.T_NumType_6 -> Integer
bitwidth = MT.d_bitwidth_20

-- | Elaboration errors
data ElabError
  = UnboundVariable Name
  | NotAFunction Name
  | TypeMismatch String
  | UnsupportedExpr String
  | QualifiedNotResolved Name [Name]  -- ^ name@Module.Path not yet resolved
  | ModuleResolutionError ModuleError -- ^ Error resolving qualified name
  deriving (Eq, Show)

-- | Elaborate a surface expression to IR
--
-- For now, this handles the simple case of generator applications
-- like `pair snd fst`. Full elaboration with type inference comes later.
elaborate :: Expr -> Either ElabError IR
elaborate = elaborateExpr' Set.empty

-- | Elaborate with module environment for qualified name resolution
elaborateWithEnv :: ModuleEnv -> Expr -> Either ElabError IR
elaborateWithEnv modEnv = elaborateExprWithEnv modEnv Set.empty

-- | Public interface (backwards compatible)
elaborateExpr :: Expr -> Either ElabError IR
elaborateExpr = elaborateExpr' Set.empty

-- | Elaborate an expression to IR, tracking local variables
elaborateExpr' :: Set Name -> Expr -> Either ElabError IR
elaborateExpr' locals expr = case expr of
  -- Generators (0-ary, need type arguments filled in later)
  EVar "id" -> Right $ Id placeholder
  EVar "fst" -> Right $ Fst placeholder placeholder
  EVar "snd" -> Right $ Snd placeholder placeholder
  EVar "inl" -> Right $ Inl placeholder placeholder
  EVar "inr" -> Right $ Inr placeholder placeholder
  EVar "terminal" -> Right $ Terminal placeholder
  EVar "initial" -> Right $ Initial placeholder
  EVar "apply" -> Right $ Apply placeholder placeholder
  -- Recursive type generators
  EVar "fold" -> Right $ Fold placeholder
  EVar "unfold" -> Right $ Unfold placeholder

  -- Generators that take IR arguments
  EVar "compose" -> Right $ Var "compose"  -- needs 2 args
  EVar "pair" -> Right $ Var "pair"        -- needs 2 args
  EVar "curry" -> Right $ Var "curry"      -- needs 1 arg
  EVar "arr" -> Right $ Var "arr"          -- needs 1 arg (D032: lift pure to effectful)
  EVar "effCompose" -> Right $ Var "effCompose"  -- needs 2 args (D032: Kleisli composition)
  EVar "pure" -> Right $ Var "pure"              -- needs 1 arg (D032: lift value to effect)

  -- Check if variable is a local binding from let
  EVar name | Set.member name locals -> Right $ LocalVar name

  -- Regular variables (including primitives and user-defined names)
  -- The type checker ensures these are valid; we just pass them through
  EVar name -> Right $ Var name

  -- Qualified access (name@Module.Path)
  -- TODO: Implement module resolution to look up the actual definition
  EQualified name modPath -> Left $ QualifiedNotResolved name modPath

  -- Application: handle generator applications specially
  EApp f arg -> elaborateApp locals f arg

  -- Pair literal: (a, b) becomes Pair a' b'
  -- In C: (OncePair){ .fst = a', .snd = b' }
  EPair a b -> do
    a' <- elaborateExpr' locals a
    b' <- elaborateExpr' locals b
    Right $ Pair a' b'

  -- Unit literal
  EUnit -> Right $ Terminal placeholder  -- () elaborates to terminal

  -- Integer literal - represented as a primitive constant
  EInt n -> Right $ Prim ("__int_" <> tshow n) TUnit TInt

  -- String literal - represented as StringLit IR node
  EStringLit s -> Right $ StringLit s

  -- Let binding: let x = e1 in e2
  -- x becomes a local variable in e2
  ELet x e1 e2 -> do
    e1' <- elaborateExpr' locals e1
    e2' <- elaborateExpr' (Set.insert x locals) e2
    Right $ Let x e1' e2'

  -- Lambda: \x -> e becomes Curry x e' (D039)
  -- The body is elaborated with x in locals (becomes LocalVar x)
  -- The C backend handles LocalVar inside Curry by generating snd access
  ELam x body -> do
    body' <- elaborateExpr' (Set.insert x locals) body
    Right $ Curry x body'

  -- Case expressions: case scrutinee of { Left x -> e1; Right y -> e2 }
  -- Elaborates to: Compose (Case (Curry x e1') (Curry y e2')) scrutinee'
  ECase scrutinee x e1 y e2 -> do
    scrutinee' <- elaborateExpr' locals scrutinee
    e1' <- elaborateExpr' (Set.insert x locals) e1
    e2' <- elaborateExpr' (Set.insert y locals) e2
    Right $ Compose (Case (Curry x e1') (Curry y e2')) scrutinee'

  EAnnot e _ -> elaborateExpr' locals e  -- ignore annotation for now

  -- Binary operators (OCP-0002): a + b, x * y, etc.
  EBinOp op a b -> do
    case (toArithIR locals a, toArithIR locals b) of
      (Just (t1, a'), Just (t2, b')) ->
        -- Both operands are arithmetic - build ArithIR directly
        case promoteNumTypes t1 t2 of
          Left err -> Left $ TypeMismatch err
          Right resultTy ->
            let a'' = promoteIfNeeded t1 resultTy a'
                b'' = promoteIfNeeded t2 resultTy b'
            in Right $ Arith resultTy (binOpToArith op a'' b'')
      _ -> do
        -- Fallback to categorical IR
        a' <- elaborateExpr' locals a
        b' <- elaborateExpr' locals b
        -- Desugar to primitive call with default I64 type
        let primName = binOpToPrimName op MT.C_I64_14
        Right $ Compose (Var primName) (Pair a' b')

  -- Unary operators (OCP-0002): -x
  EUnaryOp OpNeg e -> do
    case toArithIR locals e of
      Just (t, e') -> Right $ Arith t (MA.C_Neg_130 e')
      Nothing -> do
        e' <- elaborateExpr' locals e
        Right $ Compose (Var "neg_i64") e'

-- | Show for Text
tshow :: Show a => a -> Name
tshow = T.pack . show

-- | Elaborate function application
elaborateApp :: Set Name -> Expr -> Expr -> Either ElabError IR
elaborateApp locals f arg = case f of
  -- Check for arithmetic primitive first (OCP-0001)
  EVar name
    | Just op <- binaryArithPrim name
    -> case arg of
        EPair a b ->
          case (toArithIR locals a, toArithIR locals b) of
            (Just (_, a'), Just (_, b')) -> Right $ Arith (binOpType op) (binOpMake op a' b')
            _ -> do
              -- Fallback to categorical IR if sub-expressions aren't arithmetic
              a' <- elaborateExpr' locals a
              b' <- elaborateExpr' locals b
              Right $ Compose (Var name) (Pair a' b')
        _ -> do
          -- Non-pair argument, fall through to normal elaboration
          f' <- elaborateExpr' locals (EVar name)
          arg' <- elaborateArg locals arg
          Right $ Compose f' arg'

  -- Unary arithmetic primitive
  EVar name
    | Just op <- unaryArithPrim name
    -> case toArithIR locals arg of
        Just (_, arg') -> Right $ Arith (unaryOpType op) (unaryOpMake op arg')
        Nothing -> do
          f' <- elaborateExpr' locals (EVar name)
          arg' <- elaborateExpr' locals arg
          Right $ Compose f' arg'

  -- pair f g => Pair f' g'
  EApp (EVar "pair") f1 -> do
    f1' <- elaborateExpr' locals f1
    arg' <- elaborateExpr' locals arg
    Right $ Pair f1' arg'

  -- compose g f => Compose g' f'
  EApp (EVar "compose") g -> do
    g' <- elaborateExpr' locals g
    f' <- elaborateExpr' locals arg
    Right $ Compose g' f'

  -- effCompose g f => Compose g' f' (D032: Eff is type-only, same IR as compose)
  EApp (EVar "effCompose") g -> do
    g' <- elaborateExpr' locals g
    f' <- elaborateExpr' locals arg
    Right $ Compose g' f'

  -- curry f => Curry f'
  EVar "curry" -> do
    f' <- elaborateExpr' locals arg
    Right $ Curry "_" f'  -- generator curry, no specific var name

  -- arr f => f (D032: arr is identity at IR level - Eff is type-only distinction)
  -- At runtime, Eff A B compiles to the same code as A -> B
  EVar "arr" -> elaborateExpr' locals arg

  -- pure x => x (D032: values already act as constant morphisms in C backend)
  EVar "pure" -> elaborateExpr' locals arg

  -- case branches - not yet
  EApp (EVar "case") _ -> Left $ UnsupportedExpr "Case not yet supported"

  -- Nested application: ((f x) y)
  -- Elaborate f first, then compose with arg
  EApp innerF innerArg -> do
    -- Elaborate the inner application
    innerResult <- elaborateApp locals innerF innerArg
    -- Elaborate the outer argument
    arg' <- elaborateExpr' locals arg
    -- Compose: (inner result) applied to arg
    Right $ Compose innerResult arg'

  -- Generator or function applied to argument (e.g., fst x, thread_spawn worker)
  EVar name -> do
    f' <- elaborateExpr' locals (EVar name)
    -- Check if arg is a function being passed as a value (not called)
    -- This happens when arg is a variable name that's not a generator or local
    arg' <- elaborateArg locals arg
    Right $ Compose f' arg'

  _ -> Left $ UnsupportedExpr "Complex application not yet supported"

-- | Elaborate an argument expression
-- If the argument is a plain variable (not a generator or local), it's likely
-- a function being passed as a value, so we use FunRef instead of Var.
elaborateArg :: Set Name -> Expr -> Either ElabError IR
elaborateArg locals expr = case expr of
  -- If it's a variable that's not a generator and not a local, treat as function reference
  EVar name
    | not (isGenerator name) && not (Set.member name locals) ->
        Right $ FunRef name
  -- Otherwise, elaborate normally
  _ -> elaborateExpr' locals expr

-- | Check if a name is a generator (built-in categorical primitive)
isGenerator :: Name -> Bool
isGenerator name = name `elem`
  [ "id", "compose", "fst", "snd", "pair", "inl", "inr", "case"
  , "terminal", "initial", "curry", "apply", "fold", "unfold"
  , "arr"         -- D032: arrow generator for lifting pure to effectful
  , "effCompose"  -- D032: Kleisli composition for Eff
  , "pure"        -- D032: lift value to constant effect
  ]

------------------------------------------------------------------------
-- Arithmetic recognition at sugar level (OCP-0001)
------------------------------------------------------------------------

-- | Binary arithmetic operation info
data BinaryArithOp = BinaryArithOp
  { binOpMake :: MA.T_ArithIR_72 -> MA.T_ArithIR_72 -> MA.T_ArithIR_72
  , binOpType :: MT.T_NumType_6
  }

-- | Unary arithmetic operation info
data UnaryArithOp = UnaryArithOp
  { unaryOpMake :: MA.T_ArithIR_72 -> MA.T_ArithIR_72
  , unaryOpType :: MT.T_NumType_6
  }

-- | Recognize binary arithmetic primitive names
--
-- Pattern: add_i64, mul_f32, lt_i8, etc.
binaryArithPrim :: Name -> Maybe BinaryArithOp
binaryArithPrim name = case name of
  -- Integer add
  "add_i8"  -> Just $ BinaryArithOp maAdd MT.C_I8_8
  "add_i16" -> Just $ BinaryArithOp maAdd MT.C_I16_10
  "add_i32" -> Just $ BinaryArithOp maAdd MT.C_I32_12
  "add_i64" -> Just $ BinaryArithOp maAdd MT.C_I64_14
  "add_f32" -> Just $ BinaryArithOp maAdd MT.C_F32_16
  "add_f64" -> Just $ BinaryArithOp maAdd MT.C_F64_18

  -- Subtract
  "sub_i8"  -> Just $ BinaryArithOp maSub MT.C_I8_8
  "sub_i16" -> Just $ BinaryArithOp maSub MT.C_I16_10
  "sub_i32" -> Just $ BinaryArithOp maSub MT.C_I32_12
  "sub_i64" -> Just $ BinaryArithOp maSub MT.C_I64_14
  "sub_f32" -> Just $ BinaryArithOp maSub MT.C_F32_16
  "sub_f64" -> Just $ BinaryArithOp maSub MT.C_F64_18

  -- Multiply
  "mul_i8"  -> Just $ BinaryArithOp maMul MT.C_I8_8
  "mul_i16" -> Just $ BinaryArithOp maMul MT.C_I16_10
  "mul_i32" -> Just $ BinaryArithOp maMul MT.C_I32_12
  "mul_i64" -> Just $ BinaryArithOp maMul MT.C_I64_14
  "mul_f32" -> Just $ BinaryArithOp maMul MT.C_F32_16
  "mul_f64" -> Just $ BinaryArithOp maMul MT.C_F64_18

  -- Divide
  "div_i8"  -> Just $ BinaryArithOp maDiv MT.C_I8_8
  "div_i16" -> Just $ BinaryArithOp maDiv MT.C_I16_10
  "div_i32" -> Just $ BinaryArithOp maDiv MT.C_I32_12
  "div_i64" -> Just $ BinaryArithOp maDiv MT.C_I64_14
  "div_f32" -> Just $ BinaryArithOp maDiv MT.C_F32_16
  "div_f64" -> Just $ BinaryArithOp maDiv MT.C_F64_18

  -- Modulo (integer only)
  "mod_i8"  -> Just $ BinaryArithOp maMod MT.C_I8_8
  "mod_i16" -> Just $ BinaryArithOp maMod MT.C_I16_10
  "mod_i32" -> Just $ BinaryArithOp maMod MT.C_I32_12
  "mod_i64" -> Just $ BinaryArithOp maMod MT.C_I64_14

  -- Comparisons
  "lt_i8"  -> Just $ BinaryArithOp (maCmp MA.C_CmpLt_60) MT.C_I8_8
  "lt_i16" -> Just $ BinaryArithOp (maCmp MA.C_CmpLt_60) MT.C_I16_10
  "lt_i32" -> Just $ BinaryArithOp (maCmp MA.C_CmpLt_60) MT.C_I32_12
  "lt_i64" -> Just $ BinaryArithOp (maCmp MA.C_CmpLt_60) MT.C_I64_14
  "lt_f32" -> Just $ BinaryArithOp (maCmp MA.C_CmpLt_60) MT.C_F32_16
  "lt_f64" -> Just $ BinaryArithOp (maCmp MA.C_CmpLt_60) MT.C_F64_18

  "le_i8"  -> Just $ BinaryArithOp (maCmp MA.C_CmpLe_62) MT.C_I8_8
  "le_i16" -> Just $ BinaryArithOp (maCmp MA.C_CmpLe_62) MT.C_I16_10
  "le_i32" -> Just $ BinaryArithOp (maCmp MA.C_CmpLe_62) MT.C_I32_12
  "le_i64" -> Just $ BinaryArithOp (maCmp MA.C_CmpLe_62) MT.C_I64_14
  "le_f32" -> Just $ BinaryArithOp (maCmp MA.C_CmpLe_62) MT.C_F32_16
  "le_f64" -> Just $ BinaryArithOp (maCmp MA.C_CmpLe_62) MT.C_F64_18

  "gt_i8"  -> Just $ BinaryArithOp (maCmp MA.C_CmpGt_64) MT.C_I8_8
  "gt_i16" -> Just $ BinaryArithOp (maCmp MA.C_CmpGt_64) MT.C_I16_10
  "gt_i32" -> Just $ BinaryArithOp (maCmp MA.C_CmpGt_64) MT.C_I32_12
  "gt_i64" -> Just $ BinaryArithOp (maCmp MA.C_CmpGt_64) MT.C_I64_14
  "gt_f32" -> Just $ BinaryArithOp (maCmp MA.C_CmpGt_64) MT.C_F32_16
  "gt_f64" -> Just $ BinaryArithOp (maCmp MA.C_CmpGt_64) MT.C_F64_18

  "ge_i8"  -> Just $ BinaryArithOp (maCmp MA.C_CmpGe_66) MT.C_I8_8
  "ge_i16" -> Just $ BinaryArithOp (maCmp MA.C_CmpGe_66) MT.C_I16_10
  "ge_i32" -> Just $ BinaryArithOp (maCmp MA.C_CmpGe_66) MT.C_I32_12
  "ge_i64" -> Just $ BinaryArithOp (maCmp MA.C_CmpGe_66) MT.C_I64_14
  "ge_f32" -> Just $ BinaryArithOp (maCmp MA.C_CmpGe_66) MT.C_F32_16
  "ge_f64" -> Just $ BinaryArithOp (maCmp MA.C_CmpGe_66) MT.C_F64_18

  "eq_i8"  -> Just $ BinaryArithOp (maCmp MA.C_CmpEq_68) MT.C_I8_8
  "eq_i16" -> Just $ BinaryArithOp (maCmp MA.C_CmpEq_68) MT.C_I16_10
  "eq_i32" -> Just $ BinaryArithOp (maCmp MA.C_CmpEq_68) MT.C_I32_12
  "eq_i64" -> Just $ BinaryArithOp (maCmp MA.C_CmpEq_68) MT.C_I64_14
  "eq_f32" -> Just $ BinaryArithOp (maCmp MA.C_CmpEq_68) MT.C_F32_16
  "eq_f64" -> Just $ BinaryArithOp (maCmp MA.C_CmpEq_68) MT.C_F64_18

  "ne_i8"  -> Just $ BinaryArithOp (maCmp MA.C_CmpNe_70) MT.C_I8_8
  "ne_i16" -> Just $ BinaryArithOp (maCmp MA.C_CmpNe_70) MT.C_I16_10
  "ne_i32" -> Just $ BinaryArithOp (maCmp MA.C_CmpNe_70) MT.C_I32_12
  "ne_i64" -> Just $ BinaryArithOp (maCmp MA.C_CmpNe_70) MT.C_I64_14
  "ne_f32" -> Just $ BinaryArithOp (maCmp MA.C_CmpNe_70) MT.C_F32_16
  "ne_f64" -> Just $ BinaryArithOp (maCmp MA.C_CmpNe_70) MT.C_F64_18

  _ -> Nothing
  where
    -- Helper functions for MAlonzo ArithIR constructors with empty contexts
    maAdd e1 e2 = MA.C_Add_92 emptyCtx emptyCtx e1 e2
    maSub e1 e2 = MA.C_Sub_100 emptyCtx emptyCtx e1 e2
    maMul e1 e2 = MA.C_Mul_108 emptyCtx emptyCtx e1 e2
    maDiv e1 e2 = MA.C_Div_116 emptyCtx emptyCtx e1 e2
    maMod e1 e2 = MA.C_Mod_124 emptyCtx emptyCtx e1 e2
    maCmp op e1 e2 = MA.C_Cmp_138 emptyCtx emptyCtx op e1 e2

-- | Recognize unary arithmetic primitive names
unaryArithPrim :: Name -> Maybe UnaryArithOp
unaryArithPrim name = case name of
  "neg_i8"  -> Just $ UnaryArithOp MA.C_Neg_130 MT.C_I8_8
  "neg_i16" -> Just $ UnaryArithOp MA.C_Neg_130 MT.C_I16_10
  "neg_i32" -> Just $ UnaryArithOp MA.C_Neg_130 MT.C_I32_12
  "neg_i64" -> Just $ UnaryArithOp MA.C_Neg_130 MT.C_I64_14
  "neg_f32" -> Just $ UnaryArithOp MA.C_Neg_130 MT.C_F32_16
  "neg_f64" -> Just $ UnaryArithOp MA.C_Neg_130 MT.C_F64_18
  _ -> Nothing

-- | Try to elaborate an expression to ArithIR
--
-- Returns Nothing if the expression contains non-arithmetic constructs
-- Returns Just (numType, arithIR) for pure arithmetic expressions
toArithIR :: Set Name -> Expr -> Maybe (MT.T_NumType_6, MA.T_ArithIR_72)
toArithIR locals expr = case expr of
  -- Integer literal
  EInt n -> Just (MT.C_I64_14, MA.C_Lit_76 (coe n))

  -- Variables (locals become Var)
  EVar name
    | Set.member name locals -> Just (MT.C_I64_14, MA.C_Var_84 name MA.C_here_40)

  -- Application of arithmetic primitive to pair
  EApp (EVar name) (EPair a b)
    | Just op <- binaryArithPrim name
    -> do
        (_, a') <- toArithIR locals a
        (_, b') <- toArithIR locals b
        Just (binOpType op, binOpMake op a' b')

  -- Application of unary arithmetic primitive
  EApp (EVar name) arg
    | Just op <- unaryArithPrim name
    -> do
        (_, arg') <- toArithIR locals arg
        Just (unaryOpType op, unaryOpMake op arg')

  -- Nested binary arithmetic: add_i64 (mul_i64 (x, y), z)
  EApp (EVar name) arg
    | Just op <- binaryArithPrim name
    -> case arg of
        EPair a b -> do
          (_, a') <- toArithIR locals a
          (_, b') <- toArithIR locals b
          Just (binOpType op, binOpMake op a' b')
        _ -> Nothing

  -- Infix binary operators (OCP-0002): a + b, x * y, etc.
  EBinOp op a b -> do
    (t1, a') <- toArithIR locals a
    (t2, b') <- toArithIR locals b
    case promoteNumTypes t1 t2 of
      Left _ -> Nothing  -- Type mismatch - can't be pure arithmetic
      Right resultTy ->
        let a'' = promoteIfNeeded t1 resultTy a'
            b'' = promoteIfNeeded t2 resultTy b'
        in Just (resultTy, binOpToArith op a'' b'')

  -- Unary negation (OCP-0002): -x
  EUnaryOp OpNeg e -> do
    (t, e') <- toArithIR locals e
    Just (t, MA.C_Neg_130 e')

  _ -> Nothing

-- | Check if expression can be compiled as pure arithmetic
isArithExpr :: Set Name -> Expr -> Bool
isArithExpr locals expr = case toArithIR locals expr of
  Just _  -> True
  Nothing -> False

------------------------------------------------------------------------
-- Type promotion for infix operators (OCP-0002)
------------------------------------------------------------------------

-- | Determine the promoted type for two numeric types
--
-- Rules:
-- 1. Same domain required: int+int or float+float
-- 2. Within domain: promote to wider type
-- 3. Error on cross-domain (int+float)
promoteNumTypes :: MT.T_NumType_6 -> MT.T_NumType_6 -> Either String MT.T_NumType_6
promoteNumTypes t1 t2
  | isFloat t1 /= isFloat t2 = Left "Cannot mix integer and float types in arithmetic"
  | otherwise = Right (if bitwidth t1 >= bitwidth t2 then t1 else t2)

-- | Insert Conv if types differ
promoteIfNeeded :: MT.T_NumType_6 -> MT.T_NumType_6 -> MA.T_ArithIR_72 -> MA.T_ArithIR_72
promoteIfNeeded fromTy toTy expr
  | numTypeEq fromTy toTy = expr
  | otherwise = MA.C_Conv_146 toTy expr

-- | Check NumType equality (MAlonzo types lack Eq instance)
numTypeEq :: MT.T_NumType_6 -> MT.T_NumType_6 -> Bool
numTypeEq MT.C_I8_8   MT.C_I8_8   = True
numTypeEq MT.C_I16_10 MT.C_I16_10 = True
numTypeEq MT.C_I32_12 MT.C_I32_12 = True
numTypeEq MT.C_I64_14 MT.C_I64_14 = True
numTypeEq MT.C_F32_16 MT.C_F32_16 = True
numTypeEq MT.C_F64_18 MT.C_F64_18 = True
numTypeEq _           _           = False

-- | Convert BinOp to ArithIR constructor
binOpToArith :: BinOp -> MA.T_ArithIR_72 -> MA.T_ArithIR_72 -> MA.T_ArithIR_72
binOpToArith OpAdd = \e1 e2 -> MA.C_Add_92 emptyCtx emptyCtx e1 e2
binOpToArith OpSub = \e1 e2 -> MA.C_Sub_100 emptyCtx emptyCtx e1 e2
binOpToArith OpMul = \e1 e2 -> MA.C_Mul_108 emptyCtx emptyCtx e1 e2
binOpToArith OpDiv = \e1 e2 -> MA.C_Div_116 emptyCtx emptyCtx e1 e2
binOpToArith OpMod = \e1 e2 -> MA.C_Mod_124 emptyCtx emptyCtx e1 e2
binOpToArith OpLt  = \e1 e2 -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpLt_60 e1 e2
binOpToArith OpLe  = \e1 e2 -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpLe_62 e1 e2
binOpToArith OpGt  = \e1 e2 -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpGt_64 e1 e2
binOpToArith OpGe  = \e1 e2 -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpGe_66 e1 e2
binOpToArith OpEq  = \e1 e2 -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpEq_68 e1 e2
binOpToArith OpNe  = \e1 e2 -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpNe_70 e1 e2

-- | Convert BinOp to primitive name (for fallback when not pure arithmetic)
binOpToPrimName :: BinOp -> MT.T_NumType_6 -> Name
binOpToPrimName OpAdd MT.C_I64_14 = "add_i64"
binOpToPrimName OpSub MT.C_I64_14 = "sub_i64"
binOpToPrimName OpMul MT.C_I64_14 = "mul_i64"
binOpToPrimName OpDiv MT.C_I64_14 = "div_i64"
binOpToPrimName OpMod MT.C_I64_14 = "mod_i64"
binOpToPrimName OpLt  MT.C_I64_14 = "lt_i64"
binOpToPrimName OpLe  MT.C_I64_14 = "le_i64"
binOpToPrimName OpGt  MT.C_I64_14 = "gt_i64"
binOpToPrimName OpGe  MT.C_I64_14 = "ge_i64"
binOpToPrimName OpEq  MT.C_I64_14 = "eq_i64"
binOpToPrimName OpNe  MT.C_I64_14 = "ne_i64"
-- Default to I64 for other types (type checker will refine later)
binOpToPrimName op _ = binOpToPrimName op MT.C_I64_14

-- | Placeholder type for type inference to fill in later
placeholder :: Type
placeholder = TVar "_"

-- | Convert surface type to internal type
elaborateType :: SType -> Type
elaborateType sty = case sty of
  STVar name -> TVar name
  STUnit -> TUnit
  STVoid -> TVoid
  STInt -> TInt
  STFloat -> TFloat
  STBuffer -> TBuffer
  STString enc -> TString enc
  STProduct a b -> TProduct (elaborateType a) (elaborateType b)
  STSum a b -> TSum (elaborateType a) (elaborateType b)
  STArrow a b -> TArrow (elaborateType a) (elaborateType b)
  STEff a b -> TEff (elaborateType a) (elaborateType b)
  STQuant _ t -> elaborateType t  -- ignore quantity for now
  STApp name args -> TApp name (map elaborateType args)
  STFix t -> TFix (elaborateType t)

------------------------------------------------------------------------
-- Module-aware elaboration
------------------------------------------------------------------------

-- | Elaborate an expression with module environment for qualified names
elaborateExprWithEnv :: ModuleEnv -> Set Name -> Expr -> Either ElabError IR
elaborateExprWithEnv modEnv locals expr = case expr of
  -- Generators (0-ary, need type arguments filled in later)
  EVar "id" -> Right $ Id placeholder
  EVar "fst" -> Right $ Fst placeholder placeholder
  EVar "snd" -> Right $ Snd placeholder placeholder
  EVar "inl" -> Right $ Inl placeholder placeholder
  EVar "inr" -> Right $ Inr placeholder placeholder
  EVar "terminal" -> Right $ Terminal placeholder
  EVar "initial" -> Right $ Initial placeholder
  EVar "apply" -> Right $ Apply placeholder placeholder
  EVar "fold" -> Right $ Fold placeholder
  EVar "unfold" -> Right $ Unfold placeholder

  -- Generators that take IR arguments
  EVar "compose" -> Right $ Var "compose"
  EVar "pair" -> Right $ Var "pair"
  EVar "curry" -> Right $ Var "curry"
  EVar "arr" -> Right $ Var "arr"
  EVar "effCompose" -> Right $ Var "effCompose"
  EVar "pure" -> Right $ Var "pure"

  -- Check if variable is a local binding from let
  EVar name | Set.member name locals -> Right $ LocalVar name

  -- Regular variables
  EVar name -> Right $ Var name

  -- Qualified access - resolve using module environment
  EQualified name modPath -> do
    case lookupQualified name modPath modEnv of
      Left modErr -> Left (ModuleResolutionError modErr)
      Right declInfo -> case diDecl declInfo of
        -- For function definitions, inline the elaborated expression
        FunDef _ _ bodyExpr -> elaborateExprWithEnv modEnv locals bodyExpr
        -- For primitives, generate a Prim node
        Primitive pname sty -> Right $ Prim pname (elaborateType sty) placeholder
        -- For type signatures without definition, just use Var
        TypeSig _ _ -> Right $ Var name
        -- Type aliases shouldn't appear here
        TypeAlias {} -> Left $ UnsupportedExpr "Type alias in qualified access"

  -- Application
  EApp f arg -> elaborateAppWithEnv modEnv locals f arg

  -- Pair literal: (a, b) becomes Pair a' b'
  EPair a b -> do
    a' <- elaborateExprWithEnv modEnv locals a
    b' <- elaborateExprWithEnv modEnv locals b
    Right $ Pair a' b'

  -- Unit literal
  EUnit -> Right $ Terminal placeholder

  -- Integer literal
  EInt n -> Right $ Prim ("__int_" <> tshow n) TUnit TInt

  -- String literal
  EStringLit s -> Right $ StringLit s

  -- Let binding
  ELet x e1 e2 -> do
    e1' <- elaborateExprWithEnv modEnv locals e1
    e2' <- elaborateExprWithEnv modEnv (Set.insert x locals) e2
    Right $ Let x e1' e2'

  -- Lambda: \x -> e becomes Curry x e' (D039)
  ELam x body -> do
    body' <- elaborateExprWithEnv modEnv (Set.insert x locals) body
    Right $ Curry x body'

  -- Case expressions
  ECase scrutinee x e1 y e2 -> do
    scrutinee' <- elaborateExprWithEnv modEnv locals scrutinee
    e1' <- elaborateExprWithEnv modEnv (Set.insert x locals) e1
    e2' <- elaborateExprWithEnv modEnv (Set.insert y locals) e2
    Right $ Compose (Case (Curry x e1') (Curry y e2')) scrutinee'

  EAnnot e _ -> elaborateExprWithEnv modEnv locals e

  -- Binary operators (OCP-0002): a + b, x * y, etc.
  EBinOp op a b -> do
    case (toArithIR locals a, toArithIR locals b) of
      (Just (t1, a'), Just (t2, b')) ->
        case promoteNumTypes t1 t2 of
          Left err -> Left $ TypeMismatch err
          Right resultTy ->
            let a'' = promoteIfNeeded t1 resultTy a'
                b'' = promoteIfNeeded t2 resultTy b'
            in Right $ Arith resultTy (binOpToArith op a'' b'')
      _ -> do
        a' <- elaborateExprWithEnv modEnv locals a
        b' <- elaborateExprWithEnv modEnv locals b
        let primName = binOpToPrimName op MT.C_I64_14
        Right $ Compose (Var primName) (Pair a' b')

  -- Unary operators (OCP-0002): -x
  EUnaryOp OpNeg e -> do
    case toArithIR locals e of
      Just (t, e') -> Right $ Arith t (MA.C_Neg_130 e')
      Nothing -> do
        e' <- elaborateExprWithEnv modEnv locals e
        Right $ Compose (Var "neg_i64") e'

-- | Elaborate function application with module environment
elaborateAppWithEnv :: ModuleEnv -> Set Name -> Expr -> Expr -> Either ElabError IR
elaborateAppWithEnv modEnv locals f arg = case f of
  -- Check for arithmetic primitive first (OCP-0001)
  EVar name
    | Just op <- binaryArithPrim name
    -> case arg of
        EPair a b ->
          case (toArithIR locals a, toArithIR locals b) of
            (Just (_, a'), Just (_, b')) -> Right $ Arith (binOpType op) (binOpMake op a' b')
            _ -> do
              -- Fallback to categorical IR if sub-expressions aren't arithmetic
              a' <- elaborateExprWithEnv modEnv locals a
              b' <- elaborateExprWithEnv modEnv locals b
              Right $ Compose (Var name) (Pair a' b')
        _ -> do
          f' <- elaborateExprWithEnv modEnv locals (EVar name)
          arg' <- elaborateArgWithEnv modEnv locals arg
          Right $ Compose f' arg'

  -- Unary arithmetic primitive
  EVar name
    | Just op <- unaryArithPrim name
    -> case toArithIR locals arg of
        Just (_, arg') -> Right $ Arith (unaryOpType op) (unaryOpMake op arg')
        Nothing -> do
          f' <- elaborateExprWithEnv modEnv locals (EVar name)
          arg' <- elaborateExprWithEnv modEnv locals arg
          Right $ Compose f' arg'

  -- pair f g => Pair f' g'
  EApp (EVar "pair") f1 -> do
    f1' <- elaborateExprWithEnv modEnv locals f1
    arg' <- elaborateExprWithEnv modEnv locals arg
    Right $ Pair f1' arg'

  -- compose g f => Compose g' f'
  EApp (EVar "compose") g -> do
    g' <- elaborateExprWithEnv modEnv locals g
    f' <- elaborateExprWithEnv modEnv locals arg
    Right $ Compose g' f'

  -- effCompose g f => Compose g' f' (D032: Eff is type-only, same IR as compose)
  EApp (EVar "effCompose") g -> do
    g' <- elaborateExprWithEnv modEnv locals g
    f' <- elaborateExprWithEnv modEnv locals arg
    Right $ Compose g' f'

  -- curry f => Curry f'
  EVar "curry" -> do
    f' <- elaborateExprWithEnv modEnv locals arg
    Right $ Curry "_" f'  -- generator curry, no specific var name

  -- arr f => f (D032: arr is identity at IR level)
  EVar "arr" -> elaborateExprWithEnv modEnv locals arg

  -- pure x => x (D032: values already act as constant morphisms in C backend)
  EVar "pure" -> elaborateExprWithEnv modEnv locals arg

  -- case branches
  EApp (EVar "case") _ -> Left $ UnsupportedExpr "Case not yet supported"

  -- Nested application
  EApp innerF innerArg -> do
    innerResult <- elaborateAppWithEnv modEnv locals innerF innerArg
    arg' <- elaborateExprWithEnv modEnv locals arg
    Right $ Compose innerResult arg'

  -- Generator or function applied to argument
  EVar name -> do
    f' <- elaborateExprWithEnv modEnv locals (EVar name)
    arg' <- elaborateArgWithEnv modEnv locals arg
    Right $ Compose f' arg'

  -- Qualified name applied to argument
  EQualified name modPath -> do
    f' <- elaborateExprWithEnv modEnv locals (EQualified name modPath)
    arg' <- elaborateArgWithEnv modEnv locals arg
    Right $ Compose f' arg'

  _ -> Left $ UnsupportedExpr "Complex application not yet supported"

-- | Elaborate an argument with module environment
elaborateArgWithEnv :: ModuleEnv -> Set Name -> Expr -> Either ElabError IR
elaborateArgWithEnv modEnv locals expr = case expr of
  EVar name
    | not (isGenerator name) && not (Set.member name locals) ->
        Right $ FunRef name
  _ -> elaborateExprWithEnv modEnv locals expr
