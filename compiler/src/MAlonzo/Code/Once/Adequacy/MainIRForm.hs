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

module MAlonzo.Code.Once.Adequacy.MainIRForm where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.MainIRForm.EffUU
d_EffUU_6 :: MAlonzo.Code.Once.Internal.Type.T_Type_8
d_EffUU_6
  = coe
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
      (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
      (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
-- Once.Adequacy.MainIRForm.validateMain-at-sub
d_validateMain'45'at'45'sub_12 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
d_validateMain'45'at'45'sub_12 ~v0 v1 ~v2
  = du_validateMain'45'at'45'sub_12 v1
du_validateMain'45'at'45'sub_12 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
du_validateMain'45'at'45'sub_12 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> coe
             seq (coe v1)
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v3 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.validateMain-sub
d_validateMain'45'sub_22 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
d_validateMain'45'sub_22 v0 ~v1 = du_validateMain'45'sub_22 v0
du_validateMain'45'sub_22 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
du_validateMain'45'sub_22 v0
  = coe
      du_validateMain'45'at'45'sub_12
      (coe
         MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v0)
         (coe d_EffUU_6))
-- Once.Adequacy.MainIRForm.compileFun-main-sub
d_compileFun'45'main'45'sub_40 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
d_compileFun'45'main'45'sub_40 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_compileFun'45'main'45'sub_40 v3
du_compileFun'45'main'45'sub_40 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
du_compileFun'45'main'45'sub_40 v0
  = let v1
          = MAlonzo.Code.Once.Compile.d_validateMain'45'at_14
              (coe v0)
              (coe
                 MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v0)
                 (coe MAlonzo.Code.Once.Compile.d_mainType_10)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
           -> coe seq (coe v2) (coe du_validateMain'45'sub_22 (coe v0))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.MainIRForm.compileFunI-main-sub
d_compileFunI'45'main'45'sub_104 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
d_compileFunI'45'main'45'sub_104 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_compileFunI'45'main'45'sub_104 v3
du_compileFunI'45'main'45'sub_104 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
du_compileFunI'45'main'45'sub_104 v0
  = coe
      du_go_126 (coe v0)
      (coe MAlonzo.Code.Once.Compile.d_validateMain_20 (coe v0))
-- Once.Adequacy.MainIRForm._.go
d_go_126 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
d_go_126 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 = du_go_126 v3 v7
du_go_126 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
du_go_126 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe seq (coe v2) (coe du_validateMain'45'sub_22 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.compileFunM-main-sub
d_compileFunM'45'main'45'sub_144 ::
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
d_compileFunM'45'main'45'sub_144 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 v4 v5 v6 v7 v8 -> coe du_compileFun'45'main'45'sub_40 v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 v3 v4 v5 v6 v7 ->
                coe du_compileFunI'45'main'45'sub_104 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.findMain-here-no
d_findMain'45'here'45'no_154 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_524 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'here'45'no_154 = erased
-- Once.Adequacy.MainIRForm.bare-injective
d_bare'45'injective_168 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bare'45'injective_168 = erased
-- Once.Adequacy.MainIRForm.findMain-skip
d_findMain'45'skip_174 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_524 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'skip_174 = erased
