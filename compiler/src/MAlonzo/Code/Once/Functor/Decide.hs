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

module MAlonzo.Code.Once.Functor.Decide where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Concrete

-- Once.Functor.Decide.isBaseType?
d_isBaseType'63'_8 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84
d_isBaseType'63'_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> let v3 = d_isBaseType'63'_8 (coe v1) in
           coe
             (let v4 = d_isBaseType'63'_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> let v3 = d_isBaseType'63'_8 (coe v1) in
           coe
             (let v4 = d_isBaseType'63'_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide.isConcrete?
d_isConcrete'63'_52 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6
d_isConcrete'63'_52 v0
  = let v1
          = let v1 = d_isBaseType'63'_8 (coe v0) in
            coe
              (case coe v1 of
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                   -> coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v2)
                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> let v5 = d_isBaseType'63'_8 (coe v2) in
              coe
                (let v6 = d_isBaseType'63'_8 (coe v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v7 v8)
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         _ -> coe v1)
-- Once.Functor.Decide.isBaseType?-complete
d_isBaseType'63''45'complete_90 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isBaseType'63''45'complete_90 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> let v8 = d_isBaseType'63''45'complete_90 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_isBaseType'63''45'complete_90 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v10 v12)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> let v8 = d_isBaseType'63''45'complete_90 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_isBaseType'63''45'complete_90 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v10 v12)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide.isConcrete?-complete
d_isConcrete'63''45'complete_152 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isConcrete'63''45'complete_152 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v3) erased
             MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v3) erased
             MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v3) erased
             MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v3) erased
             MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v6 v7
               -> case coe v0 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v8 v9
                      -> let v10
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe d_isBaseType'63''45'complete_90 (coe v8) (coe v6)) in
                         coe
                           (let v11
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe d_isBaseType'63''45'complete_90 (coe v9) (coe v7)) in
                            coe
                              (let v12
                                     = coe MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v10 v11 in
                               coe
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v12)
                                    erased)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v6 v7
               -> case coe v0 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v8 v9
                      -> let v10
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe d_isBaseType'63''45'complete_90 (coe v8) (coe v6)) in
                         coe
                           (let v11
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe d_isBaseType'63''45'complete_90 (coe v9) (coe v7)) in
                            coe
                              (let v12
                                     = coe MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v10 v11 in
                               coe
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v12)
                                    erased)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> let v10 = d_isBaseType'63''45'complete_90 (coe v7) (coe v5) in
                  coe
                    (let v11 = d_isBaseType'63''45'complete_90 (coe v9) (coe v6) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v12 v14)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide.wellFormedF?
d_wellFormedF'63'_224 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118
d_wellFormedF'63'_224 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v1
        -> let v2 = d_isBaseType'63'_8 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Spec.Type.C_wf'45'K_126 v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C_Id_40
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_wf'45'Id_128)
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v1 v2
        -> let v3 = d_wellFormedF'63'_224 (coe v1) in
           coe
             (let v4 = d_wellFormedF'63'_224 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Spec.Type.C_wf'45''8853'_134 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v1 v2
        -> let v3 = d_wellFormedF'63'_224 (coe v1) in
           coe
             (let v4 = d_wellFormedF'63'_224 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Spec.Type.C_wf'45''8855'_140 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide.base-var?
d_base'45'var'63'_286 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Kind_70 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'45'var'63'_286 ~v0 ~v1 ~v2 v3 ~v4
  = du_base'45'var'63'_286 v3
du_base'45'var'63'_286 ::
  MAlonzo.Code.Once.Spec.Type.T_Kind_70 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84
du_base'45'var'63'_286 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_base_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_b'45'var_92)
      MAlonzo.Code.Once.Spec.Type.C_any_74
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide.base?
d_base'63'_304 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'63'_304 ~v0 v1 v2 = du_base'63'_304 v1 v2
du_base'63'_304 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84
du_base'63'_304 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v2
        -> coe du_base'45'var'63'_286 (coe v0 v2)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
        -> let v4 = coe du_base'63'_304 (coe v0) (coe v2) in
           coe
             (let v5 = coe du_base'63'_304 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v6 v7)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
        -> let v4 = coe du_base'63'_304 (coe v0) (coe v2) in
           coe
             (let v5 = coe du_base'63'_304 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v6 v7)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide.base?-complete
d_base'63''45'complete_384 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_base'63''45'complete_384 ~v0 v1 v2 v3
  = du_base'63''45'complete_384 v1 v2 v3
du_base'63''45'complete_384 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_base'63''45'complete_384 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'var_92
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v5
               -> coe du_go_402 (coe v0 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> let v9
                        = coe du_base'63''45'complete_384 (coe v0) (coe v7) (coe v5) in
                  coe
                    (let v10
                           = coe du_base'63''45'complete_384 (coe v0) (coe v8) (coe v6) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                            -> case coe v10 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v11 v13)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> let v9
                        = coe du_base'63''45'complete_384 (coe v0) (coe v7) (coe v5) in
                  coe
                    (let v10
                           = coe du_base'63''45'complete_384 (coe v0) (coe v8) (coe v6) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                            -> case coe v10 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v11 v13)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide._.go
d_go_402 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Kind_70 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_402 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_go_402 v4
du_go_402 ::
  MAlonzo.Code.Once.Spec.Type.T_Kind_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_402 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Once.Spec.Type.C_b'45'var_92) erased)
-- Once.Functor.Decide.wfFun?
d_wfFun'63'_468 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118
d_wfFun'63'_468 ~v0 v1 v2 = du_wfFun'63'_468 v1 v2
du_wfFun'63'_468 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118
du_wfFun'63'_468 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2
        -> let v3 = coe du_base'63'_304 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Spec.Type.C_wf'45'K_126 v4)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C_Id_40
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Type.C_wf'45'Id_128)
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> let v4 = coe du_wfFun'63'_468 (coe v0) (coe v2) in
           coe
             (let v5 = coe du_wfFun'63'_468 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Spec.Type.C_wf'45''8853'_134 v6 v7)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> let v4 = coe du_wfFun'63'_468 (coe v0) (coe v2) in
           coe
             (let v5 = coe du_wfFun'63'_468 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Spec.Type.C_wf'45''8855'_140 v6 v7)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
