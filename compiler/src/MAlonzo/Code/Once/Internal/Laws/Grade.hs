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

module MAlonzo.Code.Once.Internal.Laws.Grade where

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
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Internal.Laws.Grade.+q-assoc
d_'43'q'45'assoc_14 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'assoc_14 = erased
-- Once.Internal.Laws.Grade.+q-comm
d_'43'q'45'comm_32 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'comm_32 = erased
-- Once.Internal.Laws.Grade.+q-identityˡ
d_'43'q'45'identity'737'_36 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'identity'737'_36 = erased
-- Once.Internal.Laws.Grade.+q-identityʳ
d_'43'q'45'identity'691'_42 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'identity'691'_42 = erased
-- Once.Internal.Laws.Grade.*q-assoc
d_'42'q'45'assoc_50 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'assoc_50 = erased
-- Once.Internal.Laws.Grade.*q-comm
d_'42'q'45'comm_64 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'comm_64 = erased
-- Once.Internal.Laws.Grade.*q-identityˡ
d_'42'q'45'identity'737'_68 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'identity'737'_68 = erased
-- Once.Internal.Laws.Grade.*q-identityʳ
d_'42'q'45'identity'691'_72 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'identity'691'_72 = erased
-- Once.Internal.Laws.Grade.*q-zeroˡ
d_'42'q'45'zero'737'_76 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'zero'737'_76 = erased
-- Once.Internal.Laws.Grade.*q-zeroʳ
d_'42'q'45'zero'691'_82 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'zero'691'_82 = erased
-- Once.Internal.Laws.Grade.*q-distribʳ
d_'42'q'45'distrib'691'_90 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'distrib'691'_90 = erased
-- Once.Internal.Laws.Grade.*q-distribˡ
d_'42'q'45'distrib'737'_98 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'q'45'distrib'737'_98 = erased
-- Once.Internal.Laws.Grade.quantity-isCommutativeSemiring
d_quantity'45'isCommutativeSemiring_118 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_quantity'45'isCommutativeSemiring_118
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
-- Once.Internal.Laws.Grade.⊔q-assoc
d_'8852'q'45'assoc_126 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'q'45'assoc_126 = erased
-- Once.Internal.Laws.Grade.⊔q-comm
d_'8852'q'45'comm_144 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'q'45'comm_144 = erased
-- Once.Internal.Laws.Grade.⊔q-idem
d_'8852'q'45'idem_148 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'q'45'idem_148 = erased
-- Once.Internal.Laws.Grade.quantity-⊔-isCommutativeBand
d_quantity'45''8852''45'isCommutativeBand_150 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_quantity'45''8852''45'isCommutativeBand_150
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
-- Once.Internal.Laws.Grade.≤q'-refl
d_'8804'q'''45'refl_154 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162
d_'8804'q'''45'refl_154 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe MAlonzo.Code.Once.Internal.Context.C_z'8804'z_164
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe MAlonzo.Code.Once.Internal.Context.C_o'8804'o_170
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe MAlonzo.Code.Once.Internal.Context.C_m'8804'm_174
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.Grade.≤q'-trans
d_'8804'q'''45'trans_162 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162
d_'8804'q'''45'trans_162 ~v0 ~v1 ~v2 v3 v4
  = du_'8804'q'''45'trans_162 v3 v4
du_'8804'q'''45'trans_162 ::
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162
du_'8804'q'''45'trans_162 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Context.C_z'8804'z_164 -> coe v1
      MAlonzo.Code.Once.Internal.Context.C_z'8804'o_166
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Context.C_o'8804'o_170 -> coe v0
             MAlonzo.Code.Once.Internal.Context.C_o'8804'm_172
               -> coe MAlonzo.Code.Once.Internal.Context.C_z'8804'm_168
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Context.C_z'8804'm_168
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Internal.Context.C_o'8804'o_170 -> coe v1
      MAlonzo.Code.Once.Internal.Context.C_o'8804'm_172
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Internal.Context.C_m'8804'm_174
        -> coe seq (coe v1) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.Grade.≤q'-antisym
d_'8804'q'''45'antisym_172 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'''45'antisym_172 = erased
-- Once.Internal.Laws.Grade.≤q'-total
d_'8804'q'''45'total_178 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804'q'''45'total_178 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Internal.Context.C_z'8804'z_164)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Internal.Context.C_z'8804'o_166)
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Internal.Context.C_z'8804'm_168)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Once.Internal.Context.C_z'8804'o_166)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Internal.Context.C_o'8804'o_170)
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Internal.Context.C_o'8804'm_172)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Once.Internal.Context.C_z'8804'm_168)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Once.Internal.Context.C_o'8804'm_172)
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.Internal.Context.C_m'8804'm_174)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.Grade._≤q'?_
d__'8804'q'''63'__184 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804'q'''63'__184 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Internal.Context.C_z'8804'z_164))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Internal.Context.C_z'8804'o_166))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Internal.Context.C_z'8804'm_168))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Internal.Context.C_o'8804'o_170))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Internal.Context.C_o'8804'm_172))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Once.Internal.Context.C_m'8804'm_174))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.Grade.quantity-≤-isDecTotalOrder
d_quantity'45''8804''45'isDecTotalOrder_186 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_quantity'45''8804''45'isDecTotalOrder_186
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
               (coe (\ v0 v1 v2 -> d_'8804'q'''45'refl_154 (coe v0)))
               (\ v0 v1 v2 v3 v4 -> coe du_'8804'q'''45'trans_162 v3 v4))
            erased)
         (coe d_'8804'q'''45'total_178))
      (coe MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'q__8)
      (coe d__'8804'q'''63'__184)
-- Once.Internal.Laws.Grade.≤q-sound
d_'8804'q'45'sound_194 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162
d_'8804'q'45'sound_194 v0 v1 ~v2 = du_'8804'q'45'sound_194 v0 v1
du_'8804'q'45'sound_194 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162
du_'8804'q'45'sound_194 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Once.Internal.Context.C_z'8804'z_164
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Internal.Context.C_z'8804'o_166
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Internal.Context.C_z'8804'm_168
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Internal.Context.C_o'8804'o_170
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Internal.Context.C_o'8804'm_172
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Once.Internal.Context.C_m'8804'm_174)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.Grade.≤q-complete
d_'8804'q'45'complete_200 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T__'8804'q''__162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'45'complete_200 = erased
-- Once.Internal.Laws.Grade.⊔p-assoc
d_'8852'p'45'assoc_208 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'p'45'assoc_208 = erased
-- Once.Internal.Laws.Grade.⊔p-comm
d_'8852'p'45'comm_214 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'p'45'comm_214 = erased
-- Once.Internal.Laws.Grade.⊔p-idem
d_'8852'p'45'idem_218 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'p'45'idem_218 = erased
-- Once.Internal.Laws.Grade.⊔p-zeroʳ
d_'8852'p'45'zero'691'_222 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852'p'45'zero'691'_222 = erased
-- Once.Internal.Laws.Grade.⊔p-upperˡ
d_'8852'p'45'upper'737'_228 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8852'p'45'upper'737'_228 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
                      -> coe
                           seq (coe v3) (coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58)
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
               -> coe
                    seq (coe v2) (coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62)
             MAlonzo.Code.Once.Spec.Grade.C_eff_44
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.Grade.⊔p-upperʳ
d_'8852'p'45'upper'691'_234 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8852'p'45'upper'691'_234 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
                    MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                      -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_eff_44
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.Grade.⊔p-least
d_'8852'p'45'least_242 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'8852'p'45'least_242 ~v0 ~v1 ~v2 v3 v4
  = du_'8852'p'45'least_242 v3 v4
du_'8852'p'45'least_242 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
du_'8852'p'45'least_242 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
        -> coe seq (coe v1) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.Grade.·p-assoc
d_'183'p'45'assoc_250 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'183'p'45'assoc_250 = erased
-- Once.Internal.Laws.Grade.·p-identityʳ
d_'183'p'45'identity'691'_254 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'183'p'45'identity'691'_254 = erased
-- Once.Internal.Laws.Grade.·p-mono
d_'183'p'45'mono_264 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
d_'183'p'45'mono_264 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'183'p'45'mono_264 v4 v5
du_'183'p'45'mono_264 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
du_'183'p'45'mono_264 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
               -> coe MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
        -> coe seq (coe v1) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Laws.Grade.·p-comm
d_'183'p'45'comm_270 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'183'p'45'comm_270 = erased
-- Once.Internal.Laws.Grade.purity-isCommutativeMonoid
d_purity'45'isCommutativeMonoid_272 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_purity'45'isCommutativeMonoid_272
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
-- Once.Internal.Laws.Grade.purity-⊔-isCommutativeBand
d_purity'45''8852''45'isCommutativeBand_276 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_purity'45''8852''45'isCommutativeBand_276
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
