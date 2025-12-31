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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Size
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Semantics.⟦Fix⟧
d_'10214'Fix'10215'_6 a0 = ()
newtype T_'10214'Fix'10215'_6 = C_wrap_14 AgdaAny
-- Once.Semantics.⟦Fix⟧.unwrap
d_unwrap_12 :: T_'10214'Fix'10215'_6 -> AgdaAny
d_unwrap_12 v0
  = case coe v0 of
      C_wrap_14 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Closure
d_Closure_20 a0 a1 = ()
data T_Closure_20
  = C_constructor_40 Integer Integer (AgdaAny -> AgdaAny)
-- Once.Semantics.⟦_⟧
d_'10214'_'10215'_22 :: MAlonzo.Code.Once.Type.T_Type_32 -> ()
d_'10214'_'10215'_22 = erased
-- Once.Semantics.Closure.env-addr
d_env'45'addr_34 :: T_Closure_20 -> Integer
d_env'45'addr_34 v0
  = case coe v0 of
      C_constructor_40 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Closure.code-ptr
d_code'45'ptr_36 :: T_Closure_20 -> Integer
d_code'45'ptr_36 v0
  = case coe v0 of
      C_constructor_40 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Closure.semantics
d_semantics_38 :: T_Closure_20 -> AgdaAny -> AgdaAny
d_semantics_38 v0
  = case coe v0 of
      C_constructor_40 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.encode-pair-addr
d_encode'45'pair'45'addr_66
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.encode-pair-addr"
-- Once.Semantics.encode-inl-addr
d_encode'45'inl'45'addr_72
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.encode-inl-addr"
-- Once.Semantics.encode-inr-addr
d_encode'45'inr'45'addr_78
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.encode-inr-addr"
-- Once.Semantics.encode-closure-addr
d_encode'45'closure'45'addr_84
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.encode-closure-addr"
-- Once.Semantics.encode-int
d_encode'45'int_86
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.encode-int"
-- Once.Semantics.encode-float
d_encode'45'float_88
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.encode-float"
-- Once.Semantics.encode-str
d_encode'45'str_90
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.encode-str"
-- Once.Semantics.encode-buffer
d_encode'45'buffer_92
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.encode-buffer"
-- Once.Semantics.encode
d_encode_96 ::
  MAlonzo.Code.Once.Type.T_Type_32 -> AgdaAny -> Integer
d_encode_96 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_34
        -> coe seq (coe v1) (coe (0 :: Integer))
      MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe d_encode'45'pair'45'addr_66 v2 v3 v4 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe d_encode'45'inl'45'addr_72 v2 v3 v4
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe d_encode'45'inr'45'addr_78 v2 v3 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
        -> coe d_encode'45'closure'45'addr_84 v2 v4 v1
      MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
        -> coe d_encode'45'closure'45'addr_84 v2 v3 v1
      MAlonzo.Code.Once.Type.C_Fix_46 v2
        -> case coe v1 of
             C_wrap_14 v3 -> coe d_encode_96 (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_48 -> coe d_encode'45'int_86 v1
      MAlonzo.Code.Once.Type.C_Float_50 -> coe d_encode'45'float_88 v1
      MAlonzo.Code.Once.Type.C_Str_52 -> coe d_encode'45'str_90 v1
      MAlonzo.Code.Once.Type.C_Buffer_54 -> coe d_encode'45'buffer_92 v1
      MAlonzo.Code.Once.Type.C_TVar_56 v2 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.encode-unit
d_encode'45'unit_144 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_encode'45'unit_144 = erased
-- Once.Semantics.encode-fix-wrap
d_encode'45'fix'45'wrap_150 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_encode'45'fix'45'wrap_150 = erased
-- Once.Semantics.encode-fix-unwrap
d_encode'45'fix'45'unwrap_158 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_'10214'Fix'10215'_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_encode'45'fix'45'unwrap_158 = erased
-- Once.Semantics.encode-arr-identity
d_encode'45'arr'45'identity_168 ::
  T_Closure_20 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_encode'45'arr'45'identity_168 = erased
-- Once.Semantics.eval
d_eval_178 ::
  MAlonzo.Code.Agda.Builtin.Size.T_Size_8 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> AgdaAny -> AgdaAny
d_eval_178 ~v0 v1 v2 v3 v4 = du_eval_178 v1 v2 v3 v4
du_eval_178 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_4 -> AgdaAny -> AgdaAny
du_eval_178 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_10 -> coe v3
      MAlonzo.Code.Once.IR.C__'8728'__20 v6 v8 v9
        -> coe
             du_eval_178 (coe v6) (coe v1) (coe v8)
             (coe du_eval_178 (coe v0) (coe v6) (coe v9) (coe v3))
      MAlonzo.Code.Once.IR.C_fst_28
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8 -> coe v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_36
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8 -> coe v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_eval_178 (coe v0) (coe v10) (coe v8) (coe v3))
                    (coe du_eval_178 (coe v0) (coe v11) (coe v9) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v3)
      MAlonzo.Code.Once.IR.C_inr_62
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe du_eval_178 (coe v10) (coe v1) (coe v8) (coe v12)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> coe du_eval_178 (coe v11) (coe v1) (coe v9) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_78
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_curry_94 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> coe
                    C_constructor_40 (coe d_encode_96 (coe v0) (coe v3))
                    (coe (0 :: Integer))
                    (coe
                       (\ v12 ->
                          coe
                            du_eval_178
                            (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                            (coe v11) (coe v8)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v12))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_102
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe d_semantics_38 v7 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fold_108 -> coe C_wrap_14 (coe v3)
      MAlonzo.Code.Once.IR.C_unfold_114 -> coe d_unwrap_12 (coe v3)
      MAlonzo.Code.Once.IR.C_arr_122 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
