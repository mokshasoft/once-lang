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

module MAlonzo.Code.Once.SemanticBase where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Type

-- Once.SemanticBase.⟦Fix⟧
d_'10214'Fix'10215'_6 a0 = ()
newtype T_'10214'Fix'10215'_6 = C_wrap_14 AgdaAny
-- Once.SemanticBase.⟦Fix⟧.unwrap
d_unwrap_12 :: T_'10214'Fix'10215'_6 -> AgdaAny
d_unwrap_12 v0
  = case coe v0 of
      C_wrap_14 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SemanticBase.Closure
d_Closure_20 a0 a1 = ()
data T_Closure_20 = C_constructor_36 Integer (AgdaAny -> AgdaAny)
-- Once.SemanticBase.⟦_⟧
d_'10214'_'10215'_22 :: MAlonzo.Code.Once.Type.T_Type_32 -> ()
d_'10214'_'10215'_22 = erased
-- Once.SemanticBase.Closure.env-addr
d_env'45'addr_32 :: T_Closure_20 -> Integer
d_env'45'addr_32 v0
  = case coe v0 of
      C_constructor_36 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SemanticBase.Closure.semantics
d_semantics_34 :: T_Closure_20 -> AgdaAny -> AgdaAny
d_semantics_34 v0
  = case coe v0 of
      C_constructor_36 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SemanticBase.encode-pair-addr
d_encode'45'pair'45'addr_62
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SemanticBase.encode-pair-addr"
-- Once.SemanticBase.encode-inl-addr
d_encode'45'inl'45'addr_68
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SemanticBase.encode-inl-addr"
-- Once.SemanticBase.encode-inr-addr
d_encode'45'inr'45'addr_74
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SemanticBase.encode-inr-addr"
-- Once.SemanticBase.encode-closure-addr
d_encode'45'closure'45'addr_80
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SemanticBase.encode-closure-addr"
-- Once.SemanticBase.encode-int
d_encode'45'int_82
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SemanticBase.encode-int"
-- Once.SemanticBase.encode-float
d_encode'45'float_84
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SemanticBase.encode-float"
-- Once.SemanticBase.encode-str
d_encode'45'str_86
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SemanticBase.encode-str"
-- Once.SemanticBase.encode-buffer
d_encode'45'buffer_88
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SemanticBase.encode-buffer"
-- Once.SemanticBase.evalPrim
d_evalPrim_94
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.SemanticBase.evalPrim"
-- Once.SemanticBase.encode
d_encode_98 ::
  MAlonzo.Code.Once.Type.T_Type_32 -> AgdaAny -> Integer
d_encode_98 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_34
        -> coe seq (coe v1) (coe (0 :: Integer))
      MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe d_encode'45'pair'45'addr_62 v2 v3 v4 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe d_encode'45'inl'45'addr_68 v2 v3 v4
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe d_encode'45'inr'45'addr_74 v2 v3 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
        -> coe d_encode'45'closure'45'addr_80 v2 v4 v1
      MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
        -> coe d_encode'45'closure'45'addr_80 v2 v3 v1
      MAlonzo.Code.Once.Type.C_Fix_46 v2
        -> case coe v1 of
             C_wrap_14 v3 -> coe d_encode_98 (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_48 -> coe d_encode'45'int_82 v1
      MAlonzo.Code.Once.Type.C_Float_50 -> coe d_encode'45'float_84 v1
      MAlonzo.Code.Once.Type.C_Str_52 -> coe d_encode'45'str_86 v1
      MAlonzo.Code.Once.Type.C_Buffer_54 -> coe d_encode'45'buffer_88 v1
      MAlonzo.Code.Once.Type.C_TVar_56 v2 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SemanticBase.encode-unit
d_encode'45'unit_146 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_encode'45'unit_146 = erased
-- Once.SemanticBase.encode-fix-wrap
d_encode'45'fix'45'wrap_152 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_encode'45'fix'45'wrap_152 = erased
-- Once.SemanticBase.encode-fix-unwrap
d_encode'45'fix'45'unwrap_160 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_'10214'Fix'10215'_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_encode'45'fix'45'unwrap_160 = erased
-- Once.SemanticBase.encode-arr-identity
d_encode'45'arr'45'identity_170 ::
  T_Closure_20 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_encode'45'arr'45'identity_170 = erased
