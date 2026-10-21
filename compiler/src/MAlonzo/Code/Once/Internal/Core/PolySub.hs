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

module MAlonzo.Code.Once.Internal.Core.PolySub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Internal.Core.PolyTy
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Internal.Core.PolySub._<:ₚ_
d__'60''58''8346'__10 a0 a1 a2 = ()
data T__'60''58''8346'__10
  = C_sub'45'var_16 | C_sub'45'void_20 | C_sub'45'unit_22 |
    C_sub'45'int_24 | C_sub'45'float_26 | C_sub'45'rigid_32 |
    C_sub'45'arr_48 T__'60''58''8346'__10 T__'60''58''8346'__10
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_sub'45'prod_58 T__'60''58''8346'__10 T__'60''58''8346'__10 |
    C_sub'45'sum_68 T__'60''58''8346'__10 T__'60''58''8346'__10 |
    C_sub'45'μ_72 |
    C_sub'45'ν_80 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
-- Once.Internal.Core.PolySub.<:ₚ-⟪⟫
d_'60''58''8346''45''10218''10219'_90 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  T__'60''58''8346'__10 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
d_'60''58''8346''45''10218''10219'_90 ~v0 v1 v2 v3 v4
  = du_'60''58''8346''45''10218''10219'_90 v1 v2 v3 v4
du_'60''58''8346''45''10218''10219'_90 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  T__'60''58''8346'__10 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12
du_'60''58''8346''45''10218''10219'_90 v0 v1 v2 v3
  = let v4
          = case coe v3 of
              C_sub'45'void_20
                -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'void_16
              C_sub'45'unit_22
                -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
              C_sub'45'int_24
                -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
              C_sub'45'float_26
                -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Core.PolyTy.C_var_24 v5
           -> case coe v3 of
                C_sub'45'var_16
                  -> case coe v1 of
                       MAlonzo.Code.Once.Internal.Core.PolyTy.C_var_24 v7
                         -> coe
                              MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                              (coe v2 v5)
                       _ -> coe v4
                C_sub'45'void_20
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'void_16
                C_sub'45'unit_22
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
                C_sub'45'int_24
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
                C_sub'45'float_26
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Core.PolyTy.C__'42'__34 v5 v6
           -> case coe v3 of
                C_sub'45'void_20
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'void_16
                C_sub'45'unit_22
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
                C_sub'45'int_24
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
                C_sub'45'float_26
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
                C_sub'45'prod_58 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Internal.Core.PolyTy.C__'42'__34 v13 v14
                         -> coe
                              MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48
                              (coe
                                 du_'60''58''8346''45''10218''10219'_90 (coe v5) (coe v13) (coe v2)
                                 (coe v11))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_90 (coe v6) (coe v14) (coe v2)
                                 (coe v12))
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Core.PolyTy.C__'43'__36 v5 v6
           -> case coe v3 of
                C_sub'45'void_20
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'void_16
                C_sub'45'unit_22
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
                C_sub'45'int_24
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
                C_sub'45'float_26
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
                C_sub'45'sum_68 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Internal.Core.PolyTy.C__'43'__36 v13 v14
                         -> coe
                              MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'sum_58
                              (coe
                                 du_'60''58''8346''45''10218''10219'_90 (coe v5) (coe v13) (coe v2)
                                 (coe v11))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_90 (coe v6) (coe v14) (coe v2)
                                 (coe v12))
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Core.PolyTy.C__'8658''91'_'93'__38 v5 v6 v7
           -> case coe v3 of
                C_sub'45'void_20
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'void_16
                C_sub'45'unit_22
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
                C_sub'45'int_24
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
                C_sub'45'float_26
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
                C_sub'45'arr_48 v15 v16 v17
                  -> case coe v1 of
                       MAlonzo.Code.Once.Internal.Core.PolyTy.C__'8658''91'_'93'__38 v18 v19 v20
                         -> coe
                              MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                              (coe
                                 du_'60''58''8346''45''10218''10219'_90 (coe v18) (coe v5) (coe v2)
                                 (coe v15))
                              (coe
                                 du_'60''58''8346''45''10218''10219'_90 (coe v7) (coe v20) (coe v2)
                                 (coe v16))
                              v17
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Core.PolyTy.C_μ'45'type_40 v5
           -> case coe v3 of
                C_sub'45'void_20
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'void_16
                C_sub'45'unit_22
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
                C_sub'45'int_24
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
                C_sub'45'float_26
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
                C_sub'45'μ_72
                  -> case coe v1 of
                       MAlonzo.Code.Once.Internal.Core.PolyTy.C_μ'45'type_40 v7
                         -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'μ_62
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Core.PolyTy.C_ν'45'type_42 v5 v6
           -> case coe v3 of
                C_sub'45'void_20
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'void_16
                C_sub'45'unit_22
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
                C_sub'45'int_24
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
                C_sub'45'float_26
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
                C_sub'45'ν_80 v10
                  -> case coe v1 of
                       MAlonzo.Code.Once.Internal.Core.PolyTy.C_ν'45'type_42 v11 v12
                         -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'ν_70 v10
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Core.PolyTy.C_rigid_44 v5 v6
           -> case coe v3 of
                C_sub'45'void_20
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'void_16
                C_sub'45'unit_22
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
                C_sub'45'int_24
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
                C_sub'45'float_26
                  -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
                C_sub'45'rigid_32
                  -> case coe v1 of
                       MAlonzo.Code.Once.Internal.Core.PolyTy.C_rigid_44 v9 v10
                         -> coe MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'rigid_76
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v4)
