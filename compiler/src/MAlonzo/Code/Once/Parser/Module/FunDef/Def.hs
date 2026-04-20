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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Module.Alloc
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Body
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Params
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Parser.Module.FunDef.Def.parseFunDefB
d_parseFunDefB_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunDefB_12 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Module.Alloc.d_parseAllocB_10
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8
                                  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4) in
                            coe
                              (let v9
                                     = coe
                                         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                         (coe v7) in
                               coe
                                 (let v10
                                        = MAlonzo.Code.Once.Parser.Module.FunDef.Params.d_parseParamsB_26
                                            (coe v6) in
                                  coe
                                    (case coe v10 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                         -> case coe v12 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                -> let v15
                                                         = MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_parseFunBodyB_12
                                                             (coe v0) (coe v8) (coe v11)
                                                             (coe v13) in
                                                   coe
                                                     (case coe v15 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                          -> case coe v16 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                 -> case coe v18 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                        -> coe
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v17)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe v19)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                                                                      (coe
                                                                                         MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                                                                         (coe v20)
                                                                                         (coe v14))
                                                                                      (coe v9))))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> coe v15
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3
                    = MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                        (coe
                           MAlonzo.Code.Data.List.Base.du_foldr_216
                           (coe (\ v3 v4 -> addInt (coe (1 :: Integer)) (coe v4)))
                           (coe (0 :: Integer)) (coe v1)) in
              coe
                (let v4
                       = MAlonzo.Code.Once.Parser.Module.FunDef.Params.d_parseParamsB_26
                           (coe v1) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> let v9
                                        = MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_parseFunBodyB_12
                                            (coe v0) (coe v2) (coe v5) (coe v7) in
                                  coe
                                    (case coe v9 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                         -> case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                -> case coe v12 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                       -> coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v11)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe v13)
                                                                  (coe
                                                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                                                        (coe v14) (coe v8))
                                                                     (coe v3))))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.FunDef.Def.parseFunDef
d_parseFunDef_94 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseFunDef_94 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_parseFunBodyB_12
              (coe v0)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (let v2
                        = MAlonzo.Code.Once.Parser.Module.Alloc.d_parseAllocB_10
                            (coe v1) in
                  coe
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                         -> case coe v3 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                -> case coe v5 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                  (coe v7)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                       (coe (\ v3 v4 -> addInt (coe (1 :: Integer)) (coe v4)))
                                       (coe (0 :: Integer)) (coe v1))))
                       _ -> MAlonzo.RTE.mazUnreachableError)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.Parser.Module.FunDef.Params.d_parseParamsB_26
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (let v2
                                 = MAlonzo.Code.Once.Parser.Module.Alloc.d_parseAllocB_10
                                     (coe v1) in
                           coe
                             (case coe v2 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                                  -> case coe v3 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                         -> case coe v5 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                        (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v6)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                           (coe v7)))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                (coe
                                                   (\ v3 v4 ->
                                                      addInt (coe (1 :: Integer)) (coe v4)))
                                                (coe (0 :: Integer)) (coe v1))))
                                _ -> MAlonzo.RTE.mazUnreachableError))))))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe
                       MAlonzo.Code.Once.Parser.Module.FunDef.Params.d_parseParamsB_26
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (let v2
                                    = MAlonzo.Code.Once.Parser.Module.Alloc.d_parseAllocB_10
                                        (coe v1) in
                              coe
                                (case coe v2 of
                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                                     -> case coe v3 of
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                            -> case coe v5 of
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                                   -> coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                           (coe v4))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v6)
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                              (coe v7)))
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     -> coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                                   (coe
                                                      (\ v3 v4 ->
                                                         addInt (coe (1 :: Integer)) (coe v4)))
                                                   (coe (0 :: Integer)) (coe v1))))
                                   _ -> MAlonzo.RTE.mazUnreachableError))))))) in
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
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                        (coe v6))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
