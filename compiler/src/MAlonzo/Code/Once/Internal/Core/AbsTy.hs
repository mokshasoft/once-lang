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

module MAlonzo.Code.Once.Internal.Core.AbsTy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Internal.Core.PolyTy
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Internal.Core.AbsTy.ar-kind
d_ar'45'kind_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_TKind_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16
d_ar'45'kind_18 ~v0 ~v1 v2 v3 v4 v5 = du_ar'45'kind_18 v2 v3 v4 v5
du_ar'45'kind_18 ::
  MAlonzo.Code.Once.Internal.Type.T_TKind_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16
du_ar'45'kind_18 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_var_24 (coe v2))
             else coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Once.Internal.Core.PolyTy.C_rigid_44 (coe v0)
                       (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.AbsTy.ar-bound
d_ar'45'bound_44 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_TKind_10 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16
d_ar'45'bound_44 ~v0 v1 v2 v3 v4 = du_ar'45'bound_44 v1 v2 v3 v4
du_ar'45'bound_44 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_TKind_10 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16
du_ar'45'bound_44 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       du_ar'45'kind_18 (coe v1) (coe v2)
                       (coe MAlonzo.Code.Data.Fin.Base.du_fromℕ'60'_52 (coe v2))
                       (coe
                          MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'tk__194
                          (coe v0 (coe MAlonzo.Code.Data.Fin.Base.du_fromℕ'60'_52 (coe v2)))
                          (coe v1)))
             else coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Once.Internal.Core.PolyTy.C_rigid_44 (coe v1)
                       (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.AbsTy.absRigid
d_absRigid_68 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_TKind_10 ->
  Integer -> MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16
d_absRigid_68 v0 v1 v2 v3
  = coe
      du_ar'45'bound_44 (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v3)
         (coe v0))
-- Once.Internal.Core.AbsTy.absTy
d_absTy_82 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16
d_absTy_82 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_Unit_26
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_Void_28
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Core.PolyTy.C__'42'__34
             (coe d_absTy_82 (coe v0) (coe v1) (coe v3))
             (coe d_absTy_82 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Core.PolyTy.C__'43'__36
             (coe d_absTy_82 (coe v0) (coe v1) (coe v3))
             (coe d_absTy_82 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Internal.Core.PolyTy.C__'8658''91'_'93'__38
             (coe d_absTy_82 (coe v0) (coe v1) (coe v3)) (coe v4)
             (coe d_absTy_82 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
        -> coe
             MAlonzo.Code.Once.Internal.Core.PolyTy.C_μ'45'type_40
             (coe d_absF_88 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Core.PolyTy.C_ν'45'type_42
             (coe d_absF_88 (coe v0) (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_Int_30
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_Float_32
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
        -> coe d_absRigid_68 (coe v0) (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.AbsTy.absF
d_absF_88 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Fun_20
d_absF_88 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v3
        -> coe
             MAlonzo.Code.Once.Internal.Core.PolyTy.C_K_48
             (coe d_absTy_82 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Internal.Type.C_Id_14
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_Id_50
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Core.PolyTy.C__'8853'__52
             (coe d_absF_88 (coe v0) (coe v1) (coe v3))
             (coe d_absF_88 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Core.PolyTy.C__'8855'__54
             (coe d_absF_88 (coe v0) (coe v1) (coe v3))
             (coe d_absF_88 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.AbsTy.absTy-⟦⟧
d_absTy'45''10214''10215'_160 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absTy'45''10214''10215'_160 = erased
-- Once.Internal.Core.AbsTy.absTy-ground
d_absTy'45'ground_194 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absTy'45'ground_194 = erased
-- Once.Internal.Core.AbsTy.absF-ground
d_absF'45'ground_202 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFreeF_70 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absF'45'ground_202 = erased
-- Once.Internal.Core.AbsTy.base-ar-kind
d_base'45'ar'45'kind_276 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Base_670
d_base'45'ar'45'kind_276 ~v0 ~v1 ~v2 ~v3 v4
  = du_base'45'ar'45'kind_276 v4
du_base'45'ar'45'kind_276 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Base_670
du_base'45'ar'45'kind_276 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_b'45'var_678)
             else coe
                    seq (coe v2)
                    (coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_b'45'rigid_690)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.AbsTy.base-ar-bound
d_base'45'ar'45'bound_300 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Base_670
d_base'45'ar'45'bound_300 ~v0 v1 v2 v3
  = du_base'45'ar'45'bound_300 v1 v2 v3
du_base'45'ar'45'bound_300 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Base_670
du_base'45'ar'45'bound_300 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       du_base'45'ar'45'kind_276
                       (coe
                          MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'tk__194
                          (coe v0 (coe MAlonzo.Code.Data.Fin.Base.du_fromℕ'60'_52 (coe v1)))
                          (coe MAlonzo.Code.Once.Internal.Type.C_k'45'base_40)))
             else coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_b'45'rigid_690)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.AbsTy.abs-base
d_abs'45'base_318 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Base_670
d_abs'45'base_318 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_b'45'Unit_680
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Void_12
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_b'45'Void_682
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Int_14
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_b'45'Int_684
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Float_16
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_b'45'Float_686
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Prod_22 v6 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v8 v9
               -> coe
                    MAlonzo.Code.Once.Internal.Core.PolyTy.C_b'45'Prod_696
                    (d_abs'45'base_318 (coe v0) (coe v1) (coe v8) (coe v6))
                    (d_abs'45'base_318 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Sum_28 v6 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v8 v9
               -> coe
                    MAlonzo.Code.Once.Internal.Core.PolyTy.C_b'45'Sum_702
                    (d_abs'45'base_318 (coe v0) (coe v1) (coe v8) (coe v6))
                    (d_abs'45'base_318 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'rigid_32
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v5 v6
               -> coe
                    du_base'45'ar'45'bound_300 (coe v1) (coe v6)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v6)
                       (coe v0))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.AbsTy.abs-wf
d_abs'45'wf_352 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_WFFun_708
d_abs'45'wf_352 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v5
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C_K_12 v6
               -> coe
                    MAlonzo.Code.Once.Internal.Core.PolyTy.C_wf'45'K_716
                    (d_abs'45'base_318 (coe v0) (coe v1) (coe v6) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54
        -> coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_wf'45'Id_718
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v6 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v8 v9
               -> coe
                    MAlonzo.Code.Once.Internal.Core.PolyTy.C_wf'45'Sum_724
                    (d_abs'45'wf_352 (coe v0) (coe v1) (coe v8) (coe v6))
                    (d_abs'45'wf_352 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v6 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v8 v9
               -> coe
                    MAlonzo.Code.Once.Internal.Core.PolyTy.C_wf'45'Prod_730
                    (d_abs'45'wf_352 (coe v0) (coe v1) (coe v8) (coe v6))
                    (d_abs'45'wf_352 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.AbsTy.ConstFree
d_ConstFree_374 a0 a1 = ()
data T_ConstFree_374
  = C_cf'45'var_384 | C_cf'45'Unit_386 | C_cf'45'Void_388 |
    C_cf'45'Int_390 | C_cf'45'Float_392 |
    C_cf'45''42'_398 T_ConstFree_374 T_ConstFree_374 |
    C_cf'45''43'_404 T_ConstFree_374 T_ConstFree_374 |
    C_cf'45''8658'_412 T_ConstFree_374 T_ConstFree_374 |
    C_cf'45'μ_416 T_ConstFreeF_378 | C_cf'45'ν_422 T_ConstFreeF_378
-- Once.Internal.Core.AbsTy.ConstFreeF
d_ConstFreeF_378 a0 a1 = ()
data T_ConstFreeF_378
  = C_cf'45'K_428 T_ConstFree_374 | C_cf'45'Id_430 |
    C_cf'45''8853'_436 T_ConstFreeF_378 T_ConstFreeF_378 |
    C_cf'45''8855'_442 T_ConstFreeF_378 T_ConstFreeF_378
-- Once.Internal.Core.AbsTy.abs-⟪⟫
d_abs'45''10218''10219'_456 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  T_ConstFree_374 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45''10218''10219'_456 = erased
-- Once.Internal.Core.AbsTy.absF-⟪⟫
d_absF'45''10218''10219'_470 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Fun_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  T_ConstFreeF_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absF'45''10218''10219'_470 = erased
