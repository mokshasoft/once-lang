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

module MAlonzo.Code.Once.Parser.Module.FunDef.Params where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Parser.Module.FunDef.Params.wrapLams
d_wrapLams_10 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_wrapLams_10 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 (coe v2)
             (coe d_wrapLams_10 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.FunDef.Params.parseParamsB
d_parseParamsB_26 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseParamsB_26 v0
  = let v1
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                 (coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))) in
    coe
      (case coe v0 of
         []
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)))
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
                  -> case coe v3 of
                       (:) v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Parser.Token.C_TWord_8 v7
                                -> let v8 = d_parseParamsB_26 (coe v3) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe v4) (coe v9))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                            (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                     (coe
                                                                        (\ v13 v14 ->
                                                                           addInt
                                                                             (coe (1 :: Integer))
                                                                             (coe v14)))
                                                                     (coe (0 :: Integer))
                                                                     (coe v6))))))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Once.Parser.Token.C_TEquals_24
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                           (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)))
                              _ -> coe v1
                       _ -> coe v1
                _ -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.FunDef.Params.parseParams
d_parseParams_56 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseParams_56 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_parseParamsB_26 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_parseParamsB_26 (coe v0))))
