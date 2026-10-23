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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Type.showQuantity
d_showQuantity_4 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showQuantity_4 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe ("0" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe ("1" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe ("\969" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPurity
d_showPurity_6 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPurity_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe ("pure" :: Data.Text.Text)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe ("act" :: Data.Text.Text)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe ("eff" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showArrowKind
d_showArrowKind_8 ::
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showArrowKind_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showQuantity_4 (coe v1))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("," :: Data.Text.Text) (d_showPurity_6 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.NatF
d_NatF_14 :: MAlonzo.Code.Once.Spec.Type.T_Fun_12
d_NatF_14
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42
      (coe
         MAlonzo.Code.Once.Spec.Type.C_K_38
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
      (coe MAlonzo.Code.Once.Spec.Type.C_Id_40)
-- Once.Type.ListF
d_ListF_16 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12
d_ListF_16 v0
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42
      (coe
         MAlonzo.Code.Once.Spec.Type.C_K_38
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8855'__44
         (coe MAlonzo.Code.Once.Spec.Type.C_K_38 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Type.C_Id_40))
-- Once.Type.TreeF
d_TreeF_20 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12
d_TreeF_20 v0
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42
      (coe MAlonzo.Code.Once.Spec.Type.C_K_38 (coe v0))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8855'__44
         (coe MAlonzo.Code.Once.Spec.Type.C_Id_40)
         (coe MAlonzo.Code.Once.Spec.Type.C_Id_40))
-- Once.Type.FitsInReg
d_FitsInReg_24 a0 = ()
data T_FitsInReg_24 = C_fits'45'int_26 | C_fits'45'float_28
-- Once.Type.fits-in-reg?
d_fits'45'in'45'reg'63'_32 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe T_FitsInReg_24
d_fits'45'in'45'reg'63'_32 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Int_32
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'int_26)
         MAlonzo.Code.Once.Spec.Type.C_Float_34
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'float_28)
         _ -> coe v1)
-- Once.Type.showType
d_showType_36 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_36 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("'a" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.Nat.Show.d_show_56
                (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2)))
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe ("Unit" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe ("Void" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_36 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_36 (coe v0) (coe v3)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_36 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_36 (coe v0) (coe v3)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v7
                      -> case coe v7 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("(" :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_showType_36 (coe v0) (coe v2))
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (" " :: Data.Text.Text)
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           (d_showQuantity_4 (coe v5))
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("\8594 " :: Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 (d_showType_36 (coe v0) (coe v4))
                                                 (")" :: Data.Text.Text))))))
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("Act " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (d_showType_36 (coe v0) (coe v2))
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (" " :: Data.Text.Text) (d_showType_36 (coe v0) (coe v4))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("Eff " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_36 (coe v0) (coe v2))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text) (d_showType_36 (coe v0) (coe v4))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_40 (coe v0) (coe v2))
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 " :: Data.Text.Text) (d_showFunctor_40 (coe v0) (coe v2))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 (Act " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showFunctor_40 (coe v0) (coe v2)) (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe ("Int" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe ("Float" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_40 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_40 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_36 (coe v0) (coe v2)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe ("Id" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_40 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_40 (coe v0) (coe v3)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_40 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_40 (coe v0) (coe v3)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.both-ground
d_both'45'ground_86 ::
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_both'45'ground_86 ~v0 ~v1 v2 v3 = du_both'45'ground_86 v2 v3
du_both'45'ground_86 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_both'45'ground_86 v0 v1
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
d_isGroundF_94 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGroundF_94 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v1
        -> coe d_isGround_98 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v1 v2
        -> coe
             du_both'45'ground_86 (coe d_isGroundF_94 (coe v1))
             (coe d_isGroundF_94 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v1 v2
        -> coe
             du_both'45'ground_86 (coe d_isGroundF_94 (coe v1))
             (coe d_isGroundF_94 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGround
d_isGround_98 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGround_98 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v1 v2
        -> coe
             du_both'45'ground_86 (coe d_isGround_98 (coe v1))
             (coe d_isGround_98 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v1 v2
        -> coe
             du_both'45'ground_86 (coe d_isGround_98 (coe v1))
             (coe d_isGround_98 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v1 v2 v3
        -> coe
             du_both'45'ground_86 (coe d_isGround_98 (coe v1))
             (coe d_isGround_98 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v1 v2
        -> coe
             du_both'45'ground_86 (coe d_isGround_98 (coe v1))
             (coe d_isGround_98 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v1 v2
        -> coe
             du_both'45'ground_86 (coe d_isGround_98 (coe v1))
             (coe d_isGround_98 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v1
        -> coe d_isGroundF_94 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v1 v2
        -> coe d_isGroundF_94 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_134 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_134 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe ("Unit" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe ("Void" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe ("Int" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe ("Float" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_134 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_134 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_134 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_134 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_134 (coe v1))
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
                            (d_showPolyType_134 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Act " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_134 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_134 (coe v2))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_134 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_134 (coe v2))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_136 (coe v1))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 " :: Data.Text.Text) (d_showPolyFunctor_136 (coe v1))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 (Act " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showPolyFunctor_136 (coe v1)) (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_136 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_136 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_134 (coe v1)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe ("Id" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_136 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_136 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_136 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_136 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
