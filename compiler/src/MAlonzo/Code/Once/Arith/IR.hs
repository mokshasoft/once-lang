{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Once.Arith.IR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Arith.Type

-- Once.Arith.IR.Binding
d_Binding_6 = ()
data T_Binding_6
  = C__'8758'__16 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  MAlonzo.Code.Once.Arith.Type.T_NumType_6
-- Once.Arith.IR.Binding.name
d_name_12 ::
  T_Binding_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_name_12 v0
  = case coe v0 of
      C__'8758'__16 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.IR.Binding.type
d_type_14 ::
  T_Binding_6 -> MAlonzo.Code.Once.Arith.Type.T_NumType_6
d_type_14 v0
  = case coe v0 of
      C__'8758'__16 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.IR.Ctx
d_Ctx_18 :: ()
d_Ctx_18 = erased
-- Once.Arith.IR.∅
d_'8709'_20 :: [T_Binding_6]
d_'8709'_20 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.Arith.IR.singleton
d_singleton_22 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 -> [T_Binding_6]
d_singleton_22 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C__'8758'__16 (coe v0) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Arith.IR._⊕_
d__'8853'__28 :: [T_Binding_6] -> [T_Binding_6] -> [T_Binding_6]
d__'8853'__28 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v1)
-- Once.Arith.IR._∈_
d__'8712'__34 a0 a1 = ()
data T__'8712'__34 = C_here_40 | C_there_48 T__'8712'__34
-- Once.Arith.IR.lookup-type
d_lookup'45'type_54 ::
  T_Binding_6 ->
  [T_Binding_6] ->
  T__'8712'__34 -> MAlonzo.Code.Once.Arith.Type.T_NumType_6
d_lookup'45'type_54 v0 ~v1 ~v2 = du_lookup'45'type_54 v0
du_lookup'45'type_54 ::
  T_Binding_6 -> MAlonzo.Code.Once.Arith.Type.T_NumType_6
du_lookup'45'type_54 v0 = coe d_type_14 (coe v0)
-- Once.Arith.IR.CmpOp
d_CmpOp_58 = ()
data T_CmpOp_58
  = C_CmpLt_60 | C_CmpLe_62 | C_CmpGt_64 | C_CmpGe_66 | C_CmpEq_68 |
    C_CmpNe_70
-- Once.Arith.IR.ArithIR
d_ArithIR_72 a0 a1 = ()
data T_ArithIR_72
  = C_Lit_76 AgdaAny |
    C_Var_84 MAlonzo.Code.Agda.Builtin.String.T_String_6
             T__'8712'__34 |
    C_Add_92 [T_Binding_6] [T_Binding_6] T_ArithIR_72 T_ArithIR_72 |
    C_Sub_100 [T_Binding_6] [T_Binding_6] T_ArithIR_72 T_ArithIR_72 |
    C_Mul_108 [T_Binding_6] [T_Binding_6] T_ArithIR_72 T_ArithIR_72 |
    C_Div_116 [T_Binding_6] [T_Binding_6] T_ArithIR_72 T_ArithIR_72 |
    C_Mod_124 [T_Binding_6] [T_Binding_6] T_ArithIR_72 T_ArithIR_72 |
    C_Neg_130 T_ArithIR_72 |
    C_Cmp_138 [T_Binding_6] [T_Binding_6] T_CmpOp_58 T_ArithIR_72
              T_ArithIR_72 |
    C_Conv_146 MAlonzo.Code.Once.Arith.Type.T_NumType_6 T_ArithIR_72
-- Once.Arith.IR.size
d_size_152 ::
  [T_Binding_6] ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 -> T_ArithIR_72 -> Integer
d_size_152 ~v0 ~v1 v2 = du_size_152 v2
du_size_152 :: T_ArithIR_72 -> Integer
du_size_152 v0
  = case coe v0 of
      C_Lit_76 v2 -> coe (1 :: Integer)
      C_Var_84 v1 v4 -> coe (1 :: Integer)
      C_Add_92 v1 v2 v4 v5
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_size_152 (coe v4)))
             (coe du_size_152 (coe v5))
      C_Sub_100 v1 v2 v4 v5
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_size_152 (coe v4)))
             (coe du_size_152 (coe v5))
      C_Mul_108 v1 v2 v4 v5
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_size_152 (coe v4)))
             (coe du_size_152 (coe v5))
      C_Div_116 v1 v2 v4 v5
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_size_152 (coe v4)))
             (coe du_size_152 (coe v5))
      C_Mod_124 v1 v2 v4 v5
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_size_152 (coe v4)))
             (coe du_size_152 (coe v5))
      C_Neg_130 v3
        -> coe addInt (coe (1 :: Integer)) (coe du_size_152 (coe v3))
      C_Cmp_138 v1 v2 v4 v5 v6
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_size_152 (coe v5)))
             (coe du_size_152 (coe v6))
      C_Conv_146 v2 v4
        -> coe addInt (coe (1 :: Integer)) (coe du_size_152 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.IR.varCount
d_varCount_186 ::
  [T_Binding_6] ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 -> T_ArithIR_72 -> Integer
d_varCount_186 ~v0 ~v1 v2 = du_varCount_186 v2
du_varCount_186 :: T_ArithIR_72 -> Integer
du_varCount_186 v0
  = case coe v0 of
      C_Lit_76 v2 -> coe (0 :: Integer)
      C_Var_84 v1 v4 -> coe (1 :: Integer)
      C_Add_92 v1 v2 v4 v5
        -> coe
             addInt (coe du_varCount_186 (coe v4))
             (coe du_varCount_186 (coe v5))
      C_Sub_100 v1 v2 v4 v5
        -> coe
             addInt (coe du_varCount_186 (coe v4))
             (coe du_varCount_186 (coe v5))
      C_Mul_108 v1 v2 v4 v5
        -> coe
             addInt (coe du_varCount_186 (coe v4))
             (coe du_varCount_186 (coe v5))
      C_Div_116 v1 v2 v4 v5
        -> coe
             addInt (coe du_varCount_186 (coe v4))
             (coe du_varCount_186 (coe v5))
      C_Mod_124 v1 v2 v4 v5
        -> coe
             addInt (coe du_varCount_186 (coe v4))
             (coe du_varCount_186 (coe v5))
      C_Neg_130 v3 -> coe du_varCount_186 (coe v3)
      C_Cmp_138 v1 v2 v4 v5 v6
        -> coe
             addInt (coe du_varCount_186 (coe v5))
             (coe du_varCount_186 (coe v6))
      C_Conv_146 v2 v4 -> coe du_varCount_186 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
