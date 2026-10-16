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

module MAlonzo.Code.Once.Metatheory.Grade where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Metatheory.Grade.+q-assoc
d_'43'q'45'assoc_12 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'assoc_12 = erased
-- Once.Metatheory.Grade.+q-comm
d_'43'q'45'comm_30 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'comm_30 = erased
-- Once.Metatheory.Grade.+q-identityˡ
d_'43'q'45'identity'737'_34 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'identity'737'_34 = erased
-- Once.Metatheory.Grade.+q-identityʳ
d_'43'q'45'identity'691'_40 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'identity'691'_40 = erased
-- Once.Metatheory.Grade.*q-assoc
d_'42'q'45'assoc_48 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'assoc_48 = erased
-- Once.Metatheory.Grade.*q-comm
d_'42'q'45'comm_62 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'comm_62 = erased
-- Once.Metatheory.Grade.*q-identityˡ
d_'42'q'45'identity'737'_66 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'identity'737'_66 = erased
-- Once.Metatheory.Grade.*q-identityʳ
d_'42'q'45'identity'691'_70 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'identity'691'_70 = erased
-- Once.Metatheory.Grade.*q-zeroˡ
d_'42'q'45'zero'737'_74 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'zero'737'_74 = erased
-- Once.Metatheory.Grade.*q-zeroʳ
d_'42'q'45'zero'691'_80 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'zero'691'_80 = erased
-- Once.Metatheory.Grade.*q-distribʳ
d_'42'q'45'distrib'691'_88 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'distrib'691'_88 = erased
-- Once.Metatheory.Grade.*q-distribˡ
d_'42'q'45'distrib'737'_96 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'distrib'737'_96 = erased
-- Once.Metatheory.Grade.quantity-isCommutativeSemiring
d_quantity'45'isCommutativeSemiring_116 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_quantity'45'isCommutativeSemiring_116
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_1740
         (coe
            MAlonzo.Code.Algebra.Structures.C_constructor_1630
            (coe
               MAlonzo.Code.Algebra.Structures.C_constructor_820
               (coe
                  MAlonzo.Code.Algebra.Structures.C_constructor_758
                  (coe
                     MAlonzo.Code.Algebra.Structures.C_constructor_522
                     (coe
                        MAlonzo.Code.Algebra.Structures.C_constructor_210
                        (coe
                           MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
                        erased)
                     erased)
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
               erased)
            erased erased
            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
      erased
-- Once.Metatheory.Grade.⊔q-assoc
d_'8852'q'45'assoc_124 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'q'45'assoc_124 = erased
-- Once.Metatheory.Grade.⊔q-comm
d_'8852'q'45'comm_142 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'q'45'comm_142 = erased
-- Once.Metatheory.Grade.⊔q-idem
d_'8852'q'45'idem_146 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'q'45'idem_146 = erased
-- Once.Metatheory.Grade.quantity-⊔-isCommutativeBand
d_quantity'45''8852''45'isCommutativeBand_148 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_quantity'45''8852''45'isCommutativeBand_148
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_660
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_564
         (coe
            MAlonzo.Code.Algebra.Structures.C_constructor_522
            (coe
               MAlonzo.Code.Algebra.Structures.C_constructor_210
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
               erased)
            erased)
         erased)
      erased
-- Once.Metatheory.Grade.≤q'-refl
d_'8804'q'''45'refl_152 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162
d_'8804'q'''45'refl_152 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> coe MAlonzo.Code.Once.Lang.Context.C_z'8804'z_164
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> coe MAlonzo.Code.Once.Lang.Context.C_o'8804'o_170
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> coe MAlonzo.Code.Once.Lang.Context.C_m'8804'm_174
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Grade.≤q'-trans
d_'8804'q'''45'trans_160 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162
d_'8804'q'''45'trans_160 ~v0 ~v1 ~v2 v3 v4
  = du_'8804'q'''45'trans_160 v3 v4
du_'8804'q'''45'trans_160 ::
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162
du_'8804'q'''45'trans_160 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Context.C_z'8804'z_164 -> coe v1
      MAlonzo.Code.Once.Lang.Context.C_z'8804'o_166
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Context.C_o'8804'o_170 -> coe v0
             MAlonzo.Code.Once.Lang.Context.C_o'8804'm_172
               -> coe MAlonzo.Code.Once.Lang.Context.C_z'8804'm_168
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Context.C_z'8804'm_168
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Context.C_o'8804'o_170 -> coe v1
      MAlonzo.Code.Once.Lang.Context.C_o'8804'm_172
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Context.C_m'8804'm_174
        -> coe seq (coe v1) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Grade.≤q'-antisym
d_'8804'q'''45'antisym_170 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'''45'antisym_170 = erased
-- Once.Metatheory.Grade.≤q'-total
d_'8804'q'''45'total_176 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804'q'''45'total_176 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'z_164)
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'o_166)
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'm_168)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'o_166)
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Lang.Context.C_o'8804'o_170)
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Lang.Context.C_o'8804'm_172)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'm_168)
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Once.Lang.Context.C_o'8804'm_172)
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Lang.Context.C_m'8804'm_174)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Grade._≤q'?_
d__'8804'q'''63'__182 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804'q'''63'__182 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'z_164))
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'o_166))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Lang.Context.C_z'8804'm_168))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Lang.Context.C_o'8804'o_170))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Lang.Context.C_o'8804'm_172))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Lang.Context.C_m'8804'm_174))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Grade.quantity-≤-isDecTotalOrder
d_quantity'45''8804''45'isDecTotalOrder_184 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_quantity'45''8804''45'isDecTotalOrder_184
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
         (coe
            MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
            (coe
               MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
               (coe (\ v0 v1 v2 -> d_'8804'q'''45'refl_152 (coe v0)))
               (\ v0 v1 v2 v3 v4 -> coe du_'8804'q'''45'trans_160 v3 v4))
            erased)
         (coe d_'8804'q'''45'total_176))
      (coe MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'q__8)
      (coe d__'8804'q'''63'__182)
-- Once.Metatheory.Grade.≤q-sound
d_'8804'q'45'sound_192 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162
d_'8804'q'45'sound_192 v0 v1 ~v2 = du_'8804'q'45'sound_192 v0 v1
du_'8804'q'45'sound_192 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162
du_'8804'q'45'sound_192 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe MAlonzo.Code.Once.Lang.Context.C_z'8804'z_164
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe MAlonzo.Code.Once.Lang.Context.C_z'8804'o_166
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe MAlonzo.Code.Once.Lang.Context.C_z'8804'm_168
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe MAlonzo.Code.Once.Lang.Context.C_o'8804'o_170
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe MAlonzo.Code.Once.Lang.Context.C_o'8804'm_172
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Lang.Context.C_m'8804'm_174)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Grade.≤q-complete
d_'8804'q'45'complete_198 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'45'complete_198 = erased
-- Once.Metatheory.Grade.⊔p-assoc
d_'8852'p'45'assoc_206 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'p'45'assoc_206 = erased
-- Once.Metatheory.Grade.⊔p-comm
d_'8852'p'45'comm_212 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'p'45'comm_212 = erased
-- Once.Metatheory.Grade.⊔p-idem
d_'8852'p'45'idem_216 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'p'45'idem_216 = erased
-- Once.Metatheory.Grade.⊔p-zeroʳ
d_'8852'p'45'zero'691'_220 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'p'45'zero'691'_220 = erased
-- Once.Metatheory.Grade.⊔p-upperˡ
d_'8852'p'45'upper'737'_226 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8852'p'45'upper'737'_226 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Grade.⊔p-upperʳ
d_'8852'p'45'upper'691'_232 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8852'p'45'upper'691'_232 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Grade.⊔p-least
d_'8852'p'45'least_240 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'8852'p'45'least_240 ~v0 ~v1 ~v2 v3 v4
  = du_'8852'p'45'least_240 v3 v4
du_'8852'p'45'least_240 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
du_'8852'p'45'least_240 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Grade.·p-assoc
d_'183'p'45'assoc_248 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'183'p'45'assoc_248 = erased
-- Once.Metatheory.Grade.·p-identityʳ
d_'183'p'45'identity'691'_252 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'183'p'45'identity'691'_252 = erased
-- Once.Metatheory.Grade.·p-mono
d_'183'p'45'mono_262 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
d_'183'p'45'mono_262 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'183'p'45'mono_262 v4 v5
du_'183'p'45'mono_262 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8
du_'183'p'45'mono_262 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
               -> coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20 -> coe v0
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'g_22 -> coe v1
             MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ge_24 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Grade.·p-comm
d_'183'p'45'comm_268 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'183'p'45'comm_268 = erased
-- Once.Metatheory.Grade.purity-isCommutativeMonoid
d_purity'45'isCommutativeMonoid_270 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_purity'45'isCommutativeMonoid_270
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_758
         (coe
            MAlonzo.Code.Algebra.Structures.C_constructor_522
            (coe
               MAlonzo.Code.Algebra.Structures.C_constructor_210
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
               erased)
            erased)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
      erased
-- Once.Metatheory.Grade.purity-⊔-isCommutativeBand
d_purity'45''8852''45'isCommutativeBand_274 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_purity'45''8852''45'isCommutativeBand_274
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_660
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_564
         (coe
            MAlonzo.Code.Algebra.Structures.C_constructor_522
            (coe
               MAlonzo.Code.Algebra.Structures.C_constructor_210
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
               erased)
            erased)
         erased)
      erased
