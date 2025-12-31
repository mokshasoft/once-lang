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

module MAlonzo.Code.Once.TypeCheck.Infer where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.TypeCheck.Unify

-- Once.TypeCheck.Infer.Fresh
d_Fresh_6 :: ()
d_Fresh_6 = erased
-- Once.TypeCheck.Infer.freshTVar
d_freshTVar_8 :: Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freshTVar_8 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Type.C_TVar_56
         (coe
            MAlonzo.Code.Data.String.Base.d_concat_28
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe ("t" :: Data.Text.Text))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Once.TypeCheck.Infer.generatorType
d_generatorType_16 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_generatorType_16 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         l | (==) l ("apply" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__38
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__64
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_freshTVar_8 (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_freshTVar_8
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe d_freshTVar_8 (coe v1))))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           d_freshTVar_8
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_freshTVar_8 (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_freshTVar_8
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_freshTVar_8 (coe v1))))))
         l | (==) l ("arr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__64
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_freshTVar_8 (coe v1))))))
                     (coe
                        MAlonzo.Code.Once.Type.C_Eff_44
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_freshTVar_8 (coe v1)))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_freshTVar_8
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_freshTVar_8 (coe v1))))))
         l | (==) l ("curry" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__64
                        (coe
                           MAlonzo.Code.Once.Type.C__'42'__38
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe d_freshTVar_8 (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_freshTVar_8
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe d_freshTVar_8 (coe v1))))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    d_freshTVar_8
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe d_freshTVar_8 (coe v1))))))))
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__64
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__64
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_freshTVar_8
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe d_freshTVar_8 (coe v1)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_freshTVar_8
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_freshTVar_8
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe d_freshTVar_8 (coe v1))))))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_freshTVar_8
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_freshTVar_8 (coe v1))))))))
         l | (==) l ("fold" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_freshTVar_8 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.Type.C_Fix_46
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe d_freshTVar_8 (coe v1))))
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__38
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_freshTVar_8 (coe v1))))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_freshTVar_8 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_freshTVar_8
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_freshTVar_8 (coe v1))))))
         l | (==) l ("id" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_freshTVar_8 (coe v1)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_freshTVar_8 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe d_freshTVar_8 (coe v1))))
         l | (==) l ("initial" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe MAlonzo.Code.Once.Type.C_Void_36)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_freshTVar_8 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe d_freshTVar_8 (coe v1))))
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_freshTVar_8 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.Type.C__'43'__40
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_freshTVar_8 (coe v1)))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_freshTVar_8
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_freshTVar_8 (coe v1))))))
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           d_freshTVar_8
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_freshTVar_8 (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.C__'43'__40
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_freshTVar_8 (coe v1)))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_freshTVar_8
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_freshTVar_8 (coe v1))))))
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__64
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    d_freshTVar_8
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe d_freshTVar_8 (coe v1)))))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1))))
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__64
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__64
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_freshTVar_8
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_freshTVar_8
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe d_freshTVar_8 (coe v1)))))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_freshTVar_8
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe d_freshTVar_8 (coe v1))))))
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__64
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_freshTVar_8
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_freshTVar_8
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe d_freshTVar_8 (coe v1)))))))
                           (coe
                              MAlonzo.Code.Once.Type.C__'42'__38
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe d_freshTVar_8 (coe v1)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    d_freshTVar_8
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe d_freshTVar_8 (coe v1)))))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_freshTVar_8
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_freshTVar_8 (coe v1))))))))
         l | (==) l ("pure" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_freshTVar_8 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.Type.C_Eff_44
                        (coe MAlonzo.Code.Once.Type.C_Unit_34)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe d_freshTVar_8 (coe v1))))
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__38
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              d_freshTVar_8
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_freshTVar_8 (coe v1))))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           d_freshTVar_8
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_freshTVar_8 (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_freshTVar_8
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe d_freshTVar_8 (coe v1))))))
         l | (==) l ("terminal" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_freshTVar_8 (coe v1)))
                     (coe MAlonzo.Code.Once.Type.C_Unit_34))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe d_freshTVar_8 (coe v1))))
         l | (==) l ("unfold" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.C_Fix_46
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe d_freshTVar_8 (coe v1))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_freshTVar_8 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe d_freshTVar_8 (coe v1))))
         _ -> coe v2)
-- Once.TypeCheck.Infer.InferResult
d_InferResult_142 = ()
data T_InferResult_142
  = C_success_144 MAlonzo.Code.Once.Type.T_Type_32
                  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] Integer |
    C_failure_146 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Infer.infer
d_infer_148 ::
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer -> T_InferResult_142
d_infer_148 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Context.d_lookup_56
                     (coe v3) (coe v0) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Context.C_found_52 v5 v6 v7
                  -> coe
                       C_success_144 (coe v5)
                       (coe MAlonzo.Code.Once.TypeCheck.Unify.d_emptySubst_8) (coe v2)
                MAlonzo.Code.Once.TypeCheck.Context.C_notFound_54
                  -> let v5 = d_generatorType_16 (coe v3) (coe v2) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> coe
                                        C_success_144 (coe v7)
                                        (coe MAlonzo.Code.Once.TypeCheck.Unify.d_emptySubst_8)
                                        (coe v8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 C_failure_146
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v3))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_38 v3 v4
        -> let v5 = d_infer_148 (coe v0) (coe v3) (coe v2) in
           coe
             (case coe v5 of
                C_success_144 v6 v7 v8
                  -> let v9 = d_infer_148 (coe v0) (coe v4) (coe v8) in
                     coe
                       (case coe v9 of
                          C_success_144 v10 v11 v12
                            -> let v13
                                     = coe
                                         MAlonzo.Code.Once.Type.C_TVar_56
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d_concat_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe ("t" :: Data.Text.Text))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v12)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))) in
                               coe
                                 (let v14 = addInt (coe (1 :: Integer)) (coe v12) in
                                  coe
                                    (let v15
                                           = MAlonzo.Code.Once.TypeCheck.Unify.d_unify_188
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                                  (coe v11) (coe v6))
                                               (coe
                                                  MAlonzo.Code.Once.Type.d__'8658'__64 (coe v10)
                                                  (coe v13)) in
                                     coe
                                       (case coe v15 of
                                          MAlonzo.Code.Once.TypeCheck.Unify.C_unified_184 v16
                                            -> coe
                                                 C_success_144
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                                    (coe v16) (coe v13))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110
                                                    (coe v16)
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110
                                                       (coe v11) (coe v7)))
                                                 (coe v14)
                                          MAlonzo.Code.Once.TypeCheck.Unify.C_failed_186 v16
                                            -> coe C_failure_146 (coe v16)
                                          _ -> MAlonzo.RTE.mazUnreachableError)))
                          C_failure_146 v10 -> coe v9
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_146 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_40 v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Once.Type.C_TVar_56
                     (coe
                        MAlonzo.Code.Data.String.Base.d_concat_28
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe ("t" :: Data.Text.Text))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))) in
           coe
             (let v6 = addInt (coe (1 :: Integer)) (coe v2) in
              coe
                (let v7
                       = d_infer_148
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v0)
                              (coe v3) (coe v5))
                           (coe v4) (coe v6) in
                 coe
                   (case coe v7 of
                      C_success_144 v8 v9 v10
                        -> coe
                             C_success_144
                             (coe
                                MAlonzo.Code.Once.Type.d__'8658'__64
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48 (coe v9)
                                   (coe v5))
                                (coe v8))
                             (coe v9) (coe v10)
                      C_failure_146 v8 -> coe v7
                      _ -> MAlonzo.RTE.mazUnreachableError)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_42 v3 v4 v5
        -> let v6 = d_infer_148 (coe v0) (coe v4) (coe v2) in
           coe
             (case coe v6 of
                C_success_144 v7 v8 v9
                  -> let v10
                           = d_infer_148
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v0)
                                  (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48 (coe v8)
                                     (coe v7)))
                               (coe v5) (coe v9) in
                     coe
                       (case coe v10 of
                          C_success_144 v11 v12 v13
                            -> coe
                                 C_success_144 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110 (coe v12)
                                    (coe v8))
                                 (coe v13)
                          C_failure_146 v11 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_146 v7 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_44 v3 v4
        -> let v5 = d_infer_148 (coe v0) (coe v3) (coe v2) in
           coe
             (case coe v5 of
                C_success_144 v6 v7 v8
                  -> let v9 = d_infer_148 (coe v0) (coe v4) (coe v8) in
                     coe
                       (case coe v9 of
                          C_success_144 v10 v11 v12
                            -> coe
                                 C_success_144
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'42'__38
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48 (coe v11)
                                       (coe v6))
                                    (coe v10))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110 (coe v11)
                                    (coe v7))
                                 (coe v12)
                          C_failure_146 v10 -> coe v9
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_146 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RCase_46 v3 v4 v5 v6 v7
        -> let v8 = d_infer_148 (coe v0) (coe v3) (coe v2) in
           coe
             (case coe v8 of
                C_success_144 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.Type.C_TVar_56
                               (coe
                                  MAlonzo.Code.Data.String.Base.d_concat_28
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("t" :: Data.Text.Text))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v11)
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))) in
                     coe
                       (let v13 = addInt (coe (1 :: Integer)) (coe v11) in
                        coe
                          (let v14
                                 = coe
                                     MAlonzo.Code.Once.Type.C_TVar_56
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d_concat_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe ("t" :: Data.Text.Text))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v13)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))) in
                           coe
                             (let v15 = addInt (coe (2 :: Integer)) (coe v11) in
                              coe
                                (let v16
                                       = MAlonzo.Code.Once.TypeCheck.Unify.d_unify_188
                                           (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'43'__40 (coe v12)
                                              (coe v14)) in
                                 coe
                                   (case coe v16 of
                                      MAlonzo.Code.Once.TypeCheck.Unify.C_unified_184 v17
                                        -> let v18
                                                 = d_infer_148
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                                        (coe v0) (coe v4)
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                                           (coe v17) (coe v12)))
                                                     (coe v5) (coe v15) in
                                           coe
                                             (case coe v18 of
                                                C_success_144 v19 v20 v21
                                                  -> let v22
                                                           = d_infer_148
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                                                  (coe v0) (coe v6)
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                                                     (coe v17) (coe v14)))
                                                               (coe v7) (coe v21) in
                                                     coe
                                                       (case coe v22 of
                                                          C_success_144 v23 v24 v25
                                                            -> let v26
                                                                     = MAlonzo.Code.Once.TypeCheck.Unify.d_unify_188
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                                                            (coe v24) (coe v19))
                                                                         (coe v23) in
                                                               coe
                                                                 (case coe v26 of
                                                                    MAlonzo.Code.Once.TypeCheck.Unify.C_unified_184 v27
                                                                      -> coe
                                                                           C_success_144
                                                                           (coe
                                                                              MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                                                              (coe v27) (coe v23))
                                                                           (coe
                                                                              MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110
                                                                              (coe v27)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110
                                                                                 (coe v24)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110
                                                                                    (coe v20)
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110
                                                                                       (coe v17)
                                                                                       (coe v10)))))
                                                                           (coe v25)
                                                                    MAlonzo.Code.Once.TypeCheck.Unify.C_failed_186 v27
                                                                      -> coe C_failure_146 (coe v27)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          C_failure_146 v23 -> coe v22
                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                C_failure_146 v19 -> coe v18
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      MAlonzo.Code.Once.TypeCheck.Unify.C_failed_186 v17
                                        -> coe C_failure_146 (coe v17)
                                      _ -> MAlonzo.RTE.mazUnreachableError)))))
                C_failure_146 v9 -> coe v8
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_48
        -> coe
             C_success_144 (coe MAlonzo.Code.Once.Type.C_Unit_34)
             (coe MAlonzo.Code.Once.TypeCheck.Unify.d_emptySubst_8) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_50 v3
        -> coe
             C_success_144 (coe MAlonzo.Code.Once.Type.C_Int_48)
             (coe MAlonzo.Code.Once.TypeCheck.Unify.d_emptySubst_8) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_52 v3
        -> coe
             C_success_144 (coe MAlonzo.Code.Once.Type.C_Str_52)
             (coe MAlonzo.Code.Once.TypeCheck.Unify.d_emptySubst_8) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_54 v3 v4
        -> let v5 = d_infer_148 (coe v0) (coe v3) (coe v2) in
           coe
             (case coe v5 of
                C_success_144 v6 v7 v8
                  -> let v9
                           = MAlonzo.Code.Once.TypeCheck.Unify.d_unify_188
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48 (coe v7)
                                  (coe v4))
                               (coe v6) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Once.TypeCheck.Unify.C_unified_184 v10
                            -> coe
                                 C_success_144
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48 (coe v10)
                                    (coe v6))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110 (coe v10)
                                    (coe v7))
                                 (coe v8)
                          MAlonzo.Code.Once.TypeCheck.Unify.C_failed_186 v10
                            -> coe C_failure_146 (coe v10)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_146 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_56 v3 v4 v5
        -> let v6 = d_infer_148 (coe v0) (coe v4) (coe v2) in
           coe
             (case coe v6 of
                C_success_144 v7 v8 v9
                  -> let v10 = d_infer_148 (coe v0) (coe v5) (coe v9) in
                     coe
                       (case coe v10 of
                          C_success_144 v11 v12 v13
                            -> let v14
                                     = MAlonzo.Code.Once.TypeCheck.Unify.d_unify_188
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                            (coe v12) (coe v7))
                                         (coe MAlonzo.Code.Once.Type.C_Int_48) in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Once.TypeCheck.Unify.C_unified_184 v15
                                      -> let v16
                                               = MAlonzo.Code.Once.TypeCheck.Unify.d_unify_188
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                                      (coe v15) (coe v11))
                                                   (coe MAlonzo.Code.Once.Type.C_Int_48) in
                                         coe
                                           (case coe v16 of
                                              MAlonzo.Code.Once.TypeCheck.Unify.C_unified_184 v17
                                                -> coe
                                                     C_success_144
                                                     (coe
                                                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Raw.d_isComparisonOp_86
                                                           (coe v3))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C__'43'__40
                                                           (coe MAlonzo.Code.Once.Type.C_Unit_34)
                                                           (coe MAlonzo.Code.Once.Type.C_Unit_34))
                                                        (coe MAlonzo.Code.Once.Type.C_Int_48))
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110
                                                        (coe v17)
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110
                                                           (coe v15)
                                                           (coe
                                                              MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110
                                                              (coe v12) (coe v8))))
                                                     (coe v13)
                                              MAlonzo.Code.Once.TypeCheck.Unify.C_failed_186 v17
                                                -> coe
                                                     C_failure_146
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_ArithNonInteger_34
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                                           (coe v15) (coe v11)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    MAlonzo.Code.Once.TypeCheck.Unify.C_failed_186 v15
                                      -> coe
                                           C_failure_146
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Error.C_ArithNonInteger_34
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48
                                                 (coe v12) (coe v7)))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_failure_146 v11 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_146 v7 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_58 v4
        -> let v5 = d_infer_148 (coe v0) (coe v4) (coe v2) in
           coe
             (case coe v5 of
                C_success_144 v6 v7 v8
                  -> let v9
                           = MAlonzo.Code.Once.TypeCheck.Unify.d_unify_188
                               (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_48) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Once.TypeCheck.Unify.C_unified_184 v10
                            -> coe
                                 C_success_144 (coe MAlonzo.Code.Once.Type.C_Int_48)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110 (coe v10)
                                    (coe v7))
                                 (coe v8)
                          MAlonzo.Code.Once.TypeCheck.Unify.C_failed_186 v10
                            -> coe
                                 C_failure_146
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_ArithNonInteger_34 (coe v6))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_146 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Infer.check
d_check_1340 ::
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> Integer -> T_InferResult_142
d_check_1340 v0 v1 v2 v3
  = let v4 = d_infer_148 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v4 of
         C_success_144 v5 v6 v7
           -> let v8
                    = MAlonzo.Code.Once.TypeCheck.Unify.d_unify_188
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48 (coe v6)
                           (coe v2))
                        (coe v5) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Once.TypeCheck.Unify.C_unified_184 v9
                     -> coe
                          C_success_144
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Unify.d_applySubst_48 (coe v9)
                             (coe v5))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Unify.d_composeSubst_110 (coe v9)
                             (coe v6))
                          (coe v7)
                   MAlonzo.Code.Once.TypeCheck.Unify.C_failed_186 v9
                     -> coe C_failure_146 (coe v9)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_146 v5 -> coe v4
         _ -> MAlonzo.RTE.mazUnreachableError)
