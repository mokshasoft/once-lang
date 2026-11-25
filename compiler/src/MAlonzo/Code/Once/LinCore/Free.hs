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

module MAlonzo.Code.Once.LinCore.Free where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties

-- Once.LinCore.Free._≼_
d__'8828'__16 a0 a1 a2 = ()
data T__'8828'__16
  = C_'91''93''8828'_22 | C_'8759''8828'_30 T__'8828'__16
-- Once.LinCore.Free.++-≼
d_'43''43''45''8828'_38 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] -> [AgdaAny] -> T__'8828'__16 -> T__'8828'__16
d_'43''43''45''8828'_38 ~v0 v1 ~v2 ~v3 v4
  = du_'43''43''45''8828'_38 v1 v4
du_'43''43''45''8828'_38 ::
  [AgdaAny] -> T__'8828'__16 -> T__'8828'__16
du_'43''43''45''8828'_38 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             C_'8759''8828'_30 (coe du_'43''43''45''8828'_38 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free.Weave
d_Weave_54 a0 a1 a2 a3 a4 a5 = ()
data T_Weave_54
  = C_w'45''91''93'_62 | C_w'45'run_72 T_Weave_54 |
    C_w'45'tmp_82 T_Weave_54
-- Once.LinCore.Free.cmap-++
d_cmap'45''43''43'_90 ::
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cmap'45''43''43'_90 = erased
-- Once.LinCore.Free.cmap-≼
d_cmap'45''8828'_112 ::
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  [AgdaAny] -> [AgdaAny] -> T__'8828'__16 -> T__'8828'__16
d_cmap'45''8828'_112 ~v0 ~v1 v2 v3 v4 v5
  = du_cmap'45''8828'_112 v2 v3 v4 v5
du_cmap'45''8828'_112 ::
  (AgdaAny -> [AgdaAny]) ->
  [AgdaAny] -> [AgdaAny] -> T__'8828'__16 -> T__'8828'__16
du_cmap'45''8828'_112 v0 v1 v2 v3
  = case coe v3 of
      C_'91''93''8828'_22 -> coe C_'91''93''8828'_22
      C_'8759''8828'_30 v7
        -> case coe v1 of
             (:) v8 v9
               -> case coe v2 of
                    (:) v10 v11
                      -> coe
                           du_'43''43''45''8828'_38 (coe v0 v8)
                           (coe du_cmap'45''8828'_112 (coe v0) (coe v9) (coe v11) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free.cmap-weave
d_cmap'45'weave_134 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_Weave_54 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cmap'45'weave_134 = erased
-- Once.LinCore.Free.cmap-nil
d_cmap'45'nil_168 ::
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cmap'45'nil_168 = erased
-- Once.LinCore.Free.cmap-id
d_cmap'45'id_188 ::
  () ->
  (AgdaAny -> [AgdaAny]) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cmap'45'id_188 = erased
-- Once.LinCore.Free.foldl-weave
d_foldl'45'weave_222 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_Weave_54 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldl'45'weave_222 = erased
-- Once.LinCore.Free.Along
d_Along_254 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny -> ()
d_Along_254 = erased
-- Once.LinCore.Free._.Along-++
d_Along'45''43''43'_290 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_Along'45''43''43'_290 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_Along'45''43''43'_290 v4 v7 v8
du_Along'45''43''43'_290 ::
  [AgdaAny] -> AgdaAny -> AgdaAny -> AgdaAny
du_Along'45''43''43'_290 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_Along'45''43''43'_290 (coe v4) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free._.Along-≼
d_Along'45''8828'_318 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> AgdaAny -> T__'8828'__16 -> AgdaAny -> AgdaAny
d_Along'45''8828'_318 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
  = du_Along'45''8828'_318 v4 v5 v7 v8
du_Along'45''8828'_318 ::
  [AgdaAny] -> [AgdaAny] -> T__'8828'__16 -> AgdaAny -> AgdaAny
du_Along'45''8828'_318 v0 v1 v2 v3
  = case coe v2 of
      C_'91''93''8828'_22 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_'8759''8828'_30 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    (:) v10 v11
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                  (coe du_Along'45''8828'_318 (coe v9) (coe v11) (coe v7) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free._.Along-weave
d_Along'45'weave_344 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> T_Weave_54 -> AgdaAny -> AgdaAny -> AgdaAny
d_Along'45'weave_344 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11
                     v12 v13
  = du_Along'45'weave_344 v3 v7 v8 v9 v10 v11 v12 v13
du_Along'45'weave_344 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> T_Weave_54 -> AgdaAny -> AgdaAny -> AgdaAny
du_Along'45'weave_344 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      C_w'45''91''93'_62 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_w'45'run_72 v12
        -> case coe v2 of
             (:) v13 v14
               -> case coe v4 of
                    (:) v15 v16
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                  (coe
                                     du_Along'45'weave_344 (coe v0) (coe v1) (coe v14) (coe v3)
                                     (coe v16) (coe v12) (coe v0 v6 v13) (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_w'45'tmp_82 v12
        -> case coe v3 of
             (:) v13 v14
               -> case coe v4 of
                    (:) v15 v16
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1 v6 v13)
                           (coe
                              du_Along'45'weave_344 (coe v0) (coe v1) (coe v2) (coe v14)
                              (coe v16) (coe v12) (coe v6) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free._.Along-pres
d_Along'45'pres_396 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_Along'45'pres_396 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11
  = du_Along'45'pres_396 v3 v5 v6 v7 v8 v9 v10 v11
du_Along'45'pres_396 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_Along'45'pres_396 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v8 v9
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe v1 v8 v4 v5 v6 v10)
                    (coe
                       du_Along'45'pres_396 (coe v0) (coe v1) (coe v2) (coe v9)
                       (coe v0 v4 v8) (coe v0 v5 v8) (coe v2 v8 v4 v5 v6) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free._.Along-all
d_Along'45'all_436 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_Along'45'all_436 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_Along'45'all_436 v5 v7 v8 v9
du_Along'45'all_436 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_Along'45'all_436 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
        -> case coe v1 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v8 v6 v3)
                    (coe du_Along'45'all_436 (coe v0) (coe v9) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free.foldl-pres
d_foldl'45'pres_470 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_foldl'45'pres_470 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_foldl'45'pres_470 v3 v4 v5 v6 v7 v8
du_foldl'45'pres_470 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_foldl'45'pres_470 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      [] -> coe v5
      (:) v6 v7
        -> coe
             du_foldl'45'pres_470 (coe v0) (coe v1) (coe v7) (coe v0 v3 v6)
             (coe v0 v4 v6) (coe v1 v6 v3 v4 v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free.foldl-all
d_foldl'45'all_504 ::
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldl'45'all_504 = erased
-- Once.LinCore.Free.cmap-All
d_cmap'45'All_534 ::
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cmap'45'All_534 ~v0 ~v1 ~v2 v3 v4 v5
  = du_cmap'45'All_534 v3 v4 v5
du_cmap'45'All_534 ::
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cmap'45'All_534 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe v0 v3) (coe v1 v3)
             (coe du_cmap'45'All_534 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free.w-++
d_w'45''43''43'_562 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> [AgdaAny] -> T_Weave_54 -> T_Weave_54 -> T_Weave_54
d_w'45''43''43'_562 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10
  = du_w'45''43''43'_562 v3 v4 v5 v9 v10
du_w'45''43''43'_562 ::
  [AgdaAny] ->
  [AgdaAny] -> [AgdaAny] -> T_Weave_54 -> T_Weave_54 -> T_Weave_54
du_w'45''43''43'_562 v0 v1 v2 v3 v4
  = case coe v3 of
      C_w'45''91''93'_62 -> coe v4
      C_w'45'run_72 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> coe
                           C_w'45'run_72
                           (coe
                              du_w'45''43''43'_562 (coe v11) (coe v1) (coe v13) (coe v9)
                              (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_w'45'tmp_82 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> coe
                           C_w'45'tmp_82
                           (coe
                              du_w'45''43''43'_562 (coe v0) (coe v11) (coe v13) (coe v9)
                              (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free.w-self
d_w'45'self_578 ::
  () -> () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> T_Weave_54
d_w'45'self_578 ~v0 ~v1 ~v2 v3 = du_w'45'self_578 v3
du_w'45'self_578 :: [AgdaAny] -> T_Weave_54
du_w'45'self_578 v0
  = case coe v0 of
      [] -> coe C_w'45''91''93'_62
      (:) v1 v2 -> coe C_w'45'run_72 (coe du_w'45'self_578 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free.≼-trans
d_'8828''45'trans_590 ::
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> T__'8828'__16 -> T__'8828'__16 -> T__'8828'__16
d_'8828''45'trans_590 ~v0 v1 v2 v3 v4 v5
  = du_'8828''45'trans_590 v1 v2 v3 v4 v5
du_'8828''45'trans_590 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> T__'8828'__16 -> T__'8828'__16 -> T__'8828'__16
du_'8828''45'trans_590 v0 v1 v2 v3 v4
  = case coe v3 of
      C_'91''93''8828'_22 -> coe C_'91''93''8828'_22
      C_'8759''8828'_30 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> case coe v4 of
                           C_'8759''8828'_30 v16
                             -> case coe v2 of
                                  (:) v17 v18
                                    -> coe
                                         C_'8759''8828'_30
                                         (coe
                                            du_'8828''45'trans_590 (coe v10) (coe v12) (coe v18)
                                            (coe v8) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free.≼-refl
d_'8828''45'refl_598 :: () -> [AgdaAny] -> T__'8828'__16
d_'8828''45'refl_598 ~v0 v1 = du_'8828''45'refl_598 v1
du_'8828''45'refl_598 :: [AgdaAny] -> T__'8828'__16
du_'8828''45'refl_598 v0
  = case coe v0 of
      [] -> coe C_'91''93''8828'_22
      (:) v1 v2
        -> coe C_'8759''8828'_30 (coe du_'8828''45'refl_598 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Free.weave-pre
d_weave'45'pre_618 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_Weave_54 ->
  T__'8828'__16 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_weave'45'pre_618 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_weave'45'pre_618 v2 v3 v4 v5 v6 v7 v8
du_weave'45'pre_618 ::
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_Weave_54 ->
  T__'8828'__16 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_weave'45'pre_618 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      C_w'45''91''93'_62
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                      (coe C_'91''93''8828'_22))))
      C_w'45'run_72 v11
        -> case coe v1 of
             (:) v12 v13
               -> case coe v3 of
                    (:) v14 v15
                      -> case coe v6 of
                           C_'91''93''8828'_22
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_w'45''91''93'_62) (coe C_'91''93''8828'_22)))
                           C_'8759''8828'_30 v19
                             -> case coe v4 of
                                  (:) v20 v21
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               du_weave'45'pre_618 (coe v0) (coe v13) (coe v2)
                                               (coe v15) (coe v21) (coe v11) (coe v19)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe v12)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        du_weave'45'pre_618 (coe v0) (coe v13)
                                                        (coe v2) (coe v15) (coe v21) (coe v11)
                                                        (coe v19)))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_w'45'run_72
                                                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              du_weave'45'pre_618 (coe v0) (coe v13)
                                                              (coe v2) (coe v15) (coe v21) (coe v11)
                                                              (coe v19))))))
                                               (coe
                                                  C_'8759''8828'_30
                                                  (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              du_weave'45'pre_618 (coe v0) (coe v13)
                                                              (coe v2) (coe v15) (coe v21) (coe v11)
                                                              (coe v19))))))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_w'45'tmp_82 v11
        -> case coe v2 of
             (:) v12 v13
               -> case coe v3 of
                    (:) v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v12)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    du_weave'45'pre_618 (coe v0) (coe v1) (coe v13) (coe v15)
                                    (coe v4) (coe v11) (coe v6))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0 v12)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_weave'45'pre_618 (coe v0) (coe v1) (coe v13) (coe v15)
                                          (coe v4) (coe v11) (coe v6)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_w'45'tmp_82
                                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                du_weave'45'pre_618 (coe v0) (coe v1) (coe v13)
                                                (coe v15) (coe v4) (coe v11) (coe v6))))))
                                 (coe
                                    C_'8759''8828'_30
                                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                du_weave'45'pre_618 (coe v0) (coe v1) (coe v13)
                                                (coe v15) (coe v4) (coe v11) (coe v6))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
