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

module MAlonzo.Code.Once.Denotation.ValueDomain where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.Denotation.ValueDomain.⟦_⟧ᴰ
d_'10214'_'10215''7472'_6 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''7472'_6 = erased
-- Once.Denotation.ValueDomain.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_38 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_38 = erased
-- Once.Denotation.ValueDomain.cohᴰ
d_coh'7472'_44 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coh'7472'_44 = erased
-- Once.Denotation.ValueDomain.forget
d_forget_88 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_forget_88 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_forget_88 (coe v2) (coe v4))
                    (coe d_forget_88 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_forget_88 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_forget_88 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           (\ v7 ->
                              d_forget_88
                                (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70 (coe v1 v7)
                                   (coe (0 :: Integer))))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           (\ v7 ->
                              d_forget_88
                                (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                   (coe v1 (d_inject_92 (coe v2) (coe v7))) (coe (0 :: Integer))))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           (\ v7 ->
                              d_forget_88
                                (coe v4)
                                (coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                   (coe v1 (d_inject_92 (coe v2) (coe v7))) (coe (0 :: Integer))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Int_132 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_134 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_136 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_138 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.inject
d_inject_92 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_inject_92 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_inject_92 (coe v2) (coe v4))
                    (coe d_inject_92 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_inject_92 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_inject_92 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           (\ v7 v8 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                (coe d_inject_92 (coe v4) (coe v1 v7)))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           (\ v7 v8 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                (coe
                                   d_inject_92 (coe v4) (coe v1 (d_forget_88 (coe v2) (coe v7)))))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           (\ v7 v8 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                (coe
                                   d_inject_92 (coe v4) (coe v1 (d_forget_88 (coe v2) (coe v7)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Int_132 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_134 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_136 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_138 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.emit-D
d_emit'45'D_234 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_emit'45'D_234 v0 ~v1 v2 v3 = du_emit'45'D_234 v0 v2 v3
du_emit'45'D_234 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_emit'45'D_234 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.SigOp.Info.du_go_228
              (coe MAlonzo.Code.Once.SigOp.Info.d_sem_176 (coe v1)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.SigOp.Info.C_Pure_124
           -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         MAlonzo.Code.Once.SigOp.Info.C_Emits_126
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Denotation.Trace.du_mkEvent_142 (coe v0) (coe v1)
                   (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         MAlonzo.Code.Once.SigOp.Info.C_Halts_128
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Denotation.Trace.du_mkEvent_142 (coe v0) (coe v1)
                   (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.ValueDomain.coerce-functor⁻¹-D
d_coerce'45'functor'8315''185''45'D_260 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185''45'D_260 v0 ~v1 v2
  = du_coerce'45'functor'8315''185''45'D_260 v0 v2
du_coerce'45'functor'8315''185''45'D_260 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185''45'D_260 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2
        -> coe d_inject_92 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_Id_112 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'8315''185''45'D_260 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'8315''185''45'D_260 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'8315''185''45'D_260 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'8315''185''45'D_260 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
