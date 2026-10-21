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

module MAlonzo.Code.Once.Adequacy.EnvRel where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Adequacy.EnvRel.restrict-rel
d_restrict'45'rel_20 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T__'8849''7512'__178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_restrict'45'rel_20 ~v0 v1 v2 v3 v4 ~v5 ~v6 v7
  = du_restrict'45'rel_20 v1 v2 v3 v4 v7
du_restrict'45'rel_20 ::
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T__'8849''7512'__178 ->
  AgdaAny -> AgdaAny
du_restrict'45'rel_20 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Context.C_'8709'_8
        -> coe seq (coe v3) (coe v4)
      MAlonzo.Code.Once.Internal.Context.C__'44'_'94'__12 v6 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Context.C__'8849''8759'__192 v14 v15
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Context.C__'8759'__52 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52 v20 v21
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Internal.Context.C_z'8804'z_164
                                    -> coe
                                         du_restrict'45'rel_20 (coe v6) (coe v18) (coe v21)
                                         (coe v15) (coe v4)
                                  MAlonzo.Code.Once.Internal.Context.C_z'8804'o_166
                                    -> coe
                                         du_restrict'45'rel_20 (coe v6) (coe v18) (coe v21)
                                         (coe v15)
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
                                  MAlonzo.Code.Once.Internal.Context.C_z'8804'm_168
                                    -> coe
                                         du_restrict'45'rel_20 (coe v6) (coe v18) (coe v21)
                                         (coe v15)
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
                                  MAlonzo.Code.Once.Internal.Context.C_o'8804'o_170
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_restrict'45'rel_20 (coe v6) (coe v18) (coe v21)
                                            (coe v15)
                                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
                                  MAlonzo.Code.Once.Internal.Context.C_o'8804'm_172
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_restrict'45'rel_20 (coe v6) (coe v18) (coe v21)
                                            (coe v15)
                                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
                                  MAlonzo.Code.Once.Internal.Context.C_m'8804'm_174
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_restrict'45'rel_20 (coe v6) (coe v18) (coe v21)
                                            (coe v15)
                                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.EnvRel.lookup-rel
d_lookup'45'rel_94 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lookup'45'rel_94 ~v0 v1 v2 ~v3 ~v4 v5
  = du_lookup'45'rel_94 v1 v2 v5
du_lookup'45'rel_94 ::
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
du_lookup'45'rel_94 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Context.C__'44'_'94'__12 v4 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v8
               -> coe du_lookup'45'rel_94 (coe v4) (coe v8) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.EnvRel.bind-rel
d_bind'45'rel_132 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_bind'45'rel_132 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_bind'45'rel_132 v4 v9 v10
du_bind'45'rel_132 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_bind'45'rel_132 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
