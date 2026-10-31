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

module MAlonzo.Code.Once.CCC.Machine.MuRep where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.IRTy

-- Once.CCC.Machine.MuRep.MuRep
d_MuRep_8 = ()
data T_MuRep_8 = C_mu'45'box_10 | C_mu'45'unit_12 | C_mu'45'ptr_14
-- Once.CCC.Machine.MuRep.mu-rep
d_mu'45'rep_16 :: MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> T_MuRep_8
d_mu'45'rep_16 v0
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_K_8 v1
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_Unit_16 -> coe C_mu'45'unit_12
             MAlonzo.Code.Once.IRTy.C_Void_18 -> coe C_mu'45'ptr_14
             MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3 -> coe C_mu'45'ptr_14
             MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3 -> coe C_mu'45'ptr_14
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v2 v3 -> coe C_mu'45'ptr_14
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2 -> coe C_mu'45'ptr_14
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v2 -> coe C_mu'45'ptr_14
             MAlonzo.Code.Once.IRTy.C_Int_30 -> coe C_mu'45'box_10
             MAlonzo.Code.Once.IRTy.C_Float_32 -> coe C_mu'45'box_10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Id_10 -> coe C_mu'45'ptr_14
      MAlonzo.Code.Once.IRTy.C__'8853'__12 v1 v2 -> coe C_mu'45'ptr_14
      MAlonzo.Code.Once.IRTy.C__'8855'__14 v1 v2 -> coe C_mu'45'ptr_14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.MuRep.NotBox
d_NotBox_42 :: T_MuRep_8 -> ()
d_NotBox_42 = erased
-- Once.CCC.Machine.MuRep.Unboxed
d_Unboxed_44 :: MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> ()
d_Unboxed_44 = erased
-- Once.CCC.Machine.MuRep.BoxView
d_BoxView_48 a0 = ()
newtype T_BoxView_48
  = C_bv_52 MAlonzo.Code.Once.IRTy.T_FitsInRegI_514
-- Once.CCC.Machine.MuRep.box-view
d_box'45'view_56 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_BoxView_48
d_box'45'view_56 v0 ~v1 = du_box'45'view_56 v0
du_box'45'view_56 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> T_BoxView_48
du_box'45'view_56 v0
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_K_8 v1
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_Int_30
               -> coe C_bv_52 (coe MAlonzo.Code.Once.IRTy.C_fits'45'int_516)
             MAlonzo.Code.Once.IRTy.C_Float_32
               -> coe C_bv_52 (coe MAlonzo.Code.Once.IRTy.C_fits'45'float_518)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.MuRep.box-fit
d_box'45'fit_84 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_514
d_box'45'fit_84 v0 ~v1 = du_box'45'fit_84 v0
du_box'45'fit_84 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_514
du_box'45'fit_84 v0
  = let v1 = coe du_box'45'view_56 (coe v0) in
    coe
      (case coe v1 of
         C_bv_52 v3 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.MuRep.box-not-unboxed
d_box'45'not'45'unboxed_102 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_box'45'not'45'unboxed_102 = erased
-- Once.CCC.Machine.MuRep.fit-not-unit
d_fit'45'not'45'unit_110 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fit'45'not'45'unit_110 = erased
