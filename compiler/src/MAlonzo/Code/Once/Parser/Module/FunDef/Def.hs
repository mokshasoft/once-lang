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

module MAlonzo.Code.Once.Parser.Module.FunDef.Def where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Module.Alloc
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Body
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Params
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Parser.Module.FunDef.Def.parseFunDefB
d_parseFunDefB_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunDefB_12 v0 v1
  = coe
      du_pfd'45'alloc_20 (coe v0)
      (coe MAlonzo.Code.Once.Parser.Module.Alloc.d_tryAllocB_64 (coe v1))
-- Once.Parser.Module.FunDef.Def.pfd-alloc
d_pfd'45'alloc_20 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pfd'45'alloc_20 v0 ~v1 v2 = du_pfd'45'alloc_20 v0 v2
du_pfd'45'alloc_20 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pfd'45'alloc_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_pfd'45'params_36 (coe v0) (coe v2) (coe v5)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.FunDef.Params.d_parseParamsB_36
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.FunDef.Def.pfd-params
d_pfd'45'params_36 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pfd'45'params_36 v0 ~v1 v2 ~v3 v4 v5
  = du_pfd'45'params_36 v0 v2 v4 v5
du_pfd'45'params_36 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pfd'45'params_36 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    du_pfd'45'body_52
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v7)
                       (coe v2))
                    (coe
                       MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_parseFunBodyB_24
                       (coe v0) (coe v1) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.FunDef.Def.pfd-body
d_pfd'45'body_52 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pfd'45'body_52 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_pfd'45'body_52 v5 v6
du_pfd'45'body_52 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pfd'45'body_52 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                    (coe v6) (coe v0))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.FunDef.Def.parseFunDef
d_parseFunDef_114 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunDef_114 v0 v1
  = let v2
          = coe
              du_pfd'45'body_52
              (coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          MAlonzo.Code.Once.Parser.Module.FunDef.Params.du_pp'45'aw_58
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                         (coe v1))))))
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                            (coe v1))))))))))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                (coe v1)))))))
              (coe
                 MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_pfb'45'eq_34 (coe v0)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12 (coe v1)))))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Once.Parser.Module.FunDef.Params.du_pp'45'aw_58
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                      (coe v1))))))
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                         (coe v1)))))))))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          MAlonzo.Code.Once.Parser.Module.FunDef.Params.du_pp'45'aw_58
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                         (coe v1))))))
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                            (coe v1))))))))))
                 (coe
                    MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_eqHead_10
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Parser.Module.FunDef.Params.du_pp'45'aw_58
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                            (coe v1))))))
                             (coe
                                MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.Alloc.d_tab_70 (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Parser.Module.Alloc.d_pab_34 (coe v1)
                                            (coe
                                               MAlonzo.Code.Once.Parser.Module.Alloc.d_allocStrat_12
                                               (coe v1)))))))))))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v6))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
