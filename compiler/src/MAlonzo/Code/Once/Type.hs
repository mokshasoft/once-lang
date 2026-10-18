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

module MAlonzo.Code.Once.Type where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly

-- Once.Type.showQuantity
d_showQuantity_4 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showQuantity_4 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> coe ("0" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> coe ("1" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> coe ("\969" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPurity
d_showPurity_6 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPurity_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe ("pure" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe ("act" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe ("eff" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showArrowKind
d_showArrowKind_8 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showArrowKind_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showQuantity_4 (coe v1))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("," :: Data.Text.Text) (d_showPurity_6 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.NatF
d_NatF_14 :: MAlonzo.Code.Once.Lang.Type.T_Functor_6
d_NatF_14
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16
      (coe
         MAlonzo.Code.Once.Lang.Type.C_K_12
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe MAlonzo.Code.Once.Lang.Type.C_Id_14)
-- Once.Type.ListF
d_ListF_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6
d_ListF_16 v0
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16
      (coe
         MAlonzo.Code.Once.Lang.Type.C_K_12
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8855'__18
         (coe MAlonzo.Code.Once.Lang.Type.C_K_12 (coe v0))
         (coe MAlonzo.Code.Once.Lang.Type.C_Id_14))
-- Once.Type.TreeF
d_TreeF_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6
d_TreeF_20 v0
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16
      (coe MAlonzo.Code.Once.Lang.Type.C_K_12 (coe v0))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8855'__18
         (coe MAlonzo.Code.Once.Lang.Type.C_Id_14)
         (coe MAlonzo.Code.Once.Lang.Type.C_Id_14))
-- Once.Type.FitsInReg
d_FitsInReg_24 a0 = ()
data T_FitsInReg_24 = C_fits'45'int_26 | C_fits'45'float_28
-- Once.Type.fits-in-reg?
d_fits'45'in'45'reg'63'_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Maybe T_FitsInReg_24
d_fits'45'in'45'reg'63'_32 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Type.C_Int_34
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'int_26)
         MAlonzo.Code.Once.Lang.Type.C_Float_36
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'float_28)
         _ -> coe v1)
-- Once.Type.showType
d_showType_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_34 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe ("Unit" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe ("Void" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_34 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_34 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_34 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_34 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_34 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (d_showQuantity_4 (coe v4))
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("\8594 " :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          (d_showType_34 (coe v3)) (")" :: Data.Text.Text))))))
                    MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("Act " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_34 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text) (d_showType_34 (coe v3))))
                    MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("Eff " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_34 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text) (d_showType_34 (coe v3))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_36 (coe v1))
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 " :: Data.Text.Text) (d_showFunctor_36 (coe v1))
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 (Act " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showFunctor_36 (coe v1)) (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe ("Int" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe ("Float" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C_k'45'base_40
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("'b" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             MAlonzo.Code.Once.Lang.Type.C_k'45'any_42
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("'a" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_36 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_34 (coe v1)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe ("Id" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_36 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_36 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_36 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_36 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.both-ground
d_both'45'ground_84 ::
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_both'45'ground_84 ~v0 ~v1 v2 v3 = du_both'45'ground_84 v2 v3
du_both'45'ground_84 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_both'45'ground_84 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGroundF
d_isGroundF_92 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGroundF_92 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v1
        -> coe d_isGround_96 (coe v1)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v1 v2
        -> coe
             du_both'45'ground_84 (coe d_isGroundF_92 (coe v1))
             (coe d_isGroundF_92 (coe v2))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v1 v2
        -> coe
             du_both'45'ground_84 (coe d_isGroundF_92 (coe v1))
             (coe d_isGroundF_92 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGround
d_isGround_96 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGround_96 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v1 v2
        -> coe
             du_both'45'ground_84 (coe d_isGround_96 (coe v1))
             (coe d_isGround_96 (coe v2))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v1 v2
        -> coe
             du_both'45'ground_84 (coe d_isGround_96 (coe v1))
             (coe d_isGround_96 (coe v2))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v1 v2 v3
        -> coe
             du_both'45'ground_84 (coe d_isGround_96 (coe v1))
             (coe d_isGround_96 (coe v3))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v1 v2
        -> coe
             du_both'45'ground_84 (coe d_isGround_96 (coe v1))
             (coe d_isGround_96 (coe v2))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v1 v2
        -> coe
             du_both'45'ground_84 (coe d_isGround_96 (coe v1))
             (coe d_isGround_96 (coe v2))
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v1
        -> coe d_isGroundF_92 (coe v1)
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v1 v2
        -> coe d_isGroundF_92 (coe v1)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PFloat_40
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_132 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_132 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20
        -> coe ("Unit" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22
        -> coe ("Void" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_132 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_132 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_132 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_132 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_132 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showQuantity_4 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\8594 " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_showPolyType_132 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_132 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_132 (coe v2))))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Act " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_132 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_132 (coe v2))))
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_134 (coe v1))
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 " :: Data.Text.Text) (d_showPolyFunctor_134 (coe v1))
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 (Act " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showPolyFunctor_134 (coe v1)) (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38
        -> coe ("Int" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PFloat_40
        -> coe ("Float" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_134 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_134 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_132 (coe v1)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
        -> coe ("Id" :: Data.Text.Text)
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_134 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_134 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_134 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_134 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.purityEqBool
d_purityEqBool_176 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 -> Bool
d_purityEqBool_176 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
           -> case coe v1 of
                MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
           -> case coe v1 of
                MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
           -> case coe v1 of
                MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
