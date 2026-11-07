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

module MAlonzo.Code.Once.Spec.Boundary where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Word

-- Once.Spec.Boundary.patternAt
d_patternAt_6 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_patternAt_6 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Once.Spec.Float.Dyadic.d_width_46
            (coe
               MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))))
-- Once.Spec.Boundary.readAt
d_readAt_14 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6 -> AgdaAny -> AgdaAny
d_readAt_14 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Signature.C_unit_8 -> coe v2
      MAlonzo.Code.Once.Spec.Signature.C_void_10 -> coe v2
      MAlonzo.Code.Once.Spec.Signature.C_int_12
        -> coe
             MAlonzo.Code.Once.Spec.Word.d_norm_18
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
             (coe v2)
      MAlonzo.Code.Once.Spec.Signature.C_float_14
        -> coe d_patternAt_6 (coe v0) (coe v2)
      MAlonzo.Code.Once.Spec.Signature.C__'42'__16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_readAt_14 (coe v0) (coe v3) (coe v5))
                    (coe d_readAt_14 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Signature.C__'43'__18 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_readAt_14 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_readAt_14 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
