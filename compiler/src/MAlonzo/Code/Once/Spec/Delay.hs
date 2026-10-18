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

module MAlonzo.Code.Once.Spec.Delay where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Sum.Base

-- Once.Spec.Delay.Delay
d_Delay_8 a0 = ()
data T_Delay_8
  = C_constructor_16 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
-- Once.Spec.Delay.Delay.step
d_step_14 :: T_Delay_8 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_step_14 v0
  = case coe v0 of
      C_constructor_16 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Delay.now
d_now_20 :: () -> AgdaAny -> T_Delay_8
d_now_20 ~v0 v1 = du_now_20 v1
du_now_20 :: AgdaAny -> T_Delay_8
du_now_20 v0
  = coe
      C_constructor_16
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0))
-- Once.Spec.Delay._⇓_
d__'8659'__30 a0 a1 a2 = ()
data T__'8659'__30
  = C_now'8659'_38 | C_later'8659'_42 T_Delay_8 T__'8659'__30
-- Once.Spec.Delay._≈⟨_⟩_
d__'8776''10216'_'10217'__48 ::
  () ->
  () -> T_Delay_8 -> (AgdaAny -> AgdaAny -> ()) -> T_Delay_8 -> ()
d__'8776''10216'_'10217'__48 = erased
