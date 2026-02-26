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

module MAlonzo.Code.Once.Semantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.SemanticBase
import qualified MAlonzo.Code.Once.Type

-- Once.Semantics.Closure-η
d_Closure'45'η_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.Closure-\951"
-- Once.Semantics.eval
d_eval_16 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> AgdaAny -> AgdaAny
d_eval_16 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_14 -> coe v3
      MAlonzo.Code.Once.IR.C__'8728'__22 v5 v7 v8
        -> coe
             d_eval_16 (coe v5) (coe v1) (coe v7)
             (coe d_eval_16 (coe v0) (coe v5) (coe v8) (coe v3))
      MAlonzo.Code.Once.IR.C_fst_28
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7 -> coe v6
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_34
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7 -> coe v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_eval_16 (coe v0) (coe v10) (coe v7) (coe v3))
                    (coe d_eval_16 (coe v0) (coe v11) (coe v8) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v6
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v3)
      MAlonzo.Code.Once.IR.C_inr_54 v6
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> coe d_eval_16 (coe v9) (coe v1) (coe v7) (coe v11)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> coe d_eval_16 (coe v10) (coe v1) (coe v8) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_curry_80 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.SemanticBase.C_constructor_36
                    (coe MAlonzo.Code.Once.SemanticBase.d_encode_98 (coe v0) (coe v3))
                    (coe
                       (\ v13 ->
                          d_eval_16
                            (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v10))
                            (coe v12) (coe v8)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v13))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_88
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe MAlonzo.Code.Once.SemanticBase.d_semantics_34 v7 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fold_92
        -> coe MAlonzo.Code.Once.SemanticBase.C_wrap_14 (coe v3)
      MAlonzo.Code.Once.IR.C_unfold_96
        -> coe MAlonzo.Code.Once.SemanticBase.d_unwrap_12 (coe v3)
      MAlonzo.Code.Once.IR.C_arr_102 -> coe v3
      MAlonzo.Code.Once.IR.C_Prim_108 v6
        -> coe MAlonzo.Code.Once.SemanticBase.d_evalPrim_94 v0 v1 v6 v3
      _ -> MAlonzo.RTE.mazUnreachableError
