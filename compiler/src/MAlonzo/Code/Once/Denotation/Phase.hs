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

module MAlonzo.Code.Once.Denotation.Phase where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type

-- Once.Denotation.Phase.lookupᴰUsed
d_lookup'7472'Used_12 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
d_lookup'7472'Used_12 ~v0 v1 v2 v3
  = du_lookup'7472'Used_12 v1 v2 v3
du_lookup'7472'Used_12 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
du_lookup'7472'Used_12 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v4 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v8
               -> coe du_lookup'7472'Used_12 (coe v4) (coe v8) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Phase.restrictᴰ
d_restrict'7472'_40 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> AgdaAny
d_restrict'7472'_40 ~v0 v1 v2 v3 v4 v5
  = du_restrict'7472'_40 v1 v2 v3 v4 v5
du_restrict'7472'_40 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> AgdaAny
du_restrict'7472'_40 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C_'8709'_8
        -> coe seq (coe v3) (coe v4)
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v6 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Context.C__'8849''8759'__290 v14 v15
               -> case coe v1 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v20 v21
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Surface.Context.C_z'8804'z_262
                                    -> coe
                                         du_restrict'7472'_40 (coe v6) (coe v18) (coe v21) (coe v15)
                                         (coe v4)
                                  MAlonzo.Code.Once.Surface.Context.C_z'8804'o_264
                                    -> coe
                                         du_restrict'7472'_40 (coe v6) (coe v18) (coe v21) (coe v15)
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
                                  MAlonzo.Code.Once.Surface.Context.C_z'8804'm_266
                                    -> coe
                                         du_restrict'7472'_40 (coe v6) (coe v18) (coe v21) (coe v15)
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
                                  MAlonzo.Code.Once.Surface.Context.C_o'8804'o_268
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_restrict'7472'_40 (coe v6) (coe v18) (coe v21)
                                            (coe v15)
                                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
                                  MAlonzo.Code.Once.Surface.Context.C_o'8804'm_270
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_restrict'7472'_40 (coe v6) (coe v18) (coe v21)
                                            (coe v15)
                                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
                                  MAlonzo.Code.Once.Surface.Context.C_m'8804'm_272
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_restrict'7472'_40 (coe v6) (coe v18) (coe v21)
                                            (coe v15)
                                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Phase.bindᴰ
d_bind'7472'_114 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_bind'7472'_114 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_bind'7472'_114 v4 v5 v6
du_bind'7472'_114 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_bind'7472'_114 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Zero_6 -> coe v1
      MAlonzo.Code.Once.Type.C_One_8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)
      MAlonzo.Code.Once.Type.C_Many_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Phase.bindᴰ0
d_bind'7472'0_136 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_bind'7472'0_136 ~v0 ~v1 ~v2 v3 = du_bind'7472'0_136 v3
du_bind'7472'0_136 :: AgdaAny -> AgdaAny
du_bind'7472'0_136 v0 = coe v0
-- Once.Denotation.Phase.eraseᴰ
d_erase'7472'_146 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
d_erase'7472'_146 ~v0 v1 v2 v3 = du_erase'7472'_146 v1 v2 v3
du_erase'7472'_146 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_erase'7472'_146 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C_'8709'_8
        -> coe seq (coe v1) (coe v2)
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v4 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           du_erase'7472'_146 (coe v4) (coe v9)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_erase'7472'_146 (coe v4) (coe v9)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_erase'7472'_146 (coe v4) (coe v9)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Phase.eraseᴰ-restrict
d_erase'7472''45'restrict_192 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_erase'7472''45'restrict_192 = erased
-- Once.Denotation.Phase.eraseᴰ-bind
d_erase'7472''45'bind_276 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_erase'7472''45'bind_276 = erased
-- Once.Denotation.Phase.env0
d_env0_304 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> AgdaAny
d_env0_304 v0 v1 = coe seq (coe v0) (coe v1)
