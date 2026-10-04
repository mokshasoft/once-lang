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

module MAlonzo.Code.Once.Arith.Machine.Recognise where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.Arith.Machine.Recognise.binop
d_binop_12 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
d_binop_12 ~v0 ~v1 v2 v3 = du_binop_12 v2 v3
du_binop_12 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
du_binop_12 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v3 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.pair-of
d_pair'45'of_24 ::
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'of_24 ~v0 v1 v2 = du_pair'45'of_24 v1 v2
du_pair'45'of_24 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'of_24 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.BView
d_BView_36 a0 a1 a2 = ()
data T_BView_36
  = C_bv'45'pair_48 | C_bv'45'dist_64 | C_bv'45'other_72
-- Once.Arith.Machine.Recognise.b-view
d_b'45'view_80 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_BView_36
d_b'45'view_80 ~v0 v1 v2 = du_b'45'view_80 v1 v2
du_b'45'view_80 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_BView_36
du_b'45'view_80 v0 v1
  = let v2 = coe C_bv'45'other_72 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v11 v12
                  -> case coe v0 of
                       MAlonzo.Code.Once.IRTy.C__'42'__20 v13 v14 -> coe C_bv'45'dist_64
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9 -> coe C_bv'45'pair_48
                _ -> coe v2
         _ -> coe v2)
-- Once.Arith.Machine.Recognise.unop
d_unop_98 ::
  () -> () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_unop_98 ~v0 ~v1 v2 v3 = du_unop_98 v2 v3
du_unop_98 ::
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_unop_98 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.plumbing?
d_plumbing'63'_110 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_plumbing'63'_110 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.IR.C_id_20
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.IR.C__'8728'__28 v5 v7 v8
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe d_plumbing'63'_110 (coe v5) (coe v1) (coe v7))
                (coe d_plumbing'63'_110 (coe v0) (coe v5) (coe v8))
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_plumbing'63'_110 (coe v0) (coe v9) (coe v7))
                       (coe d_plumbing'63'_110 (coe v0) (coe v10) (coe v8))
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_fst_42
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_snd_48
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_terminal_72
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v3)
-- Once.Arith.Machine.Recognise.TView
d_TView_124 a0 a1 a2 = ()
data T_TView_124
  = C_tv'45'term_128 | C_tv'45'comp_136 | C_tv'45'other_144
-- Once.Arith.Machine.Recognise.t-view
d_t'45'view_152 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_TView_124
d_t'45'view_152 ~v0 ~v1 v2 = du_t'45'view_152 v2
du_t'45'view_152 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_TView_124
du_t'45'view_152 v0
  = let v1 = coe C_tv'45'other_144 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IR.C__'8728'__28 v3 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_tv'45'comp_136
                _ -> coe v1
         MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_tv'45'term_128
         _ -> coe v1)
-- Once.Arith.Machine.Recognise.it-at
d_it'45'at_164 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_TView_124 -> Bool
d_it'45'at_164 v0 ~v1 v2 v3 = du_it'45'at_164 v0 v2 v3
du_it'45'at_164 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_TView_124 -> Bool
du_it'45'at_164 v0 v1 v2
  = case coe v2 of
      C_tv'45'term_128 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_tv'45'comp_136
        -> case coe v1 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
               -> coe d_plumbing'63'_110 (coe v0) (coe v7) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_tv'45'other_144 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.is-terminal?
d_is'45'terminal'63'_174 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'terminal'63'_174 v0 ~v1 v2
  = du_is'45'terminal'63'_174 v0 v2
du_is'45'terminal'63'_174 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'terminal'63'_174 v0 v1
  = coe
      du_it'45'at_164 (coe v0) (coe v1) (coe du_t'45'view_152 (coe v1))
-- Once.Arith.Machine.Recognise.PView
d_PView_182 a0 a1 a2 = ()
data T_PView_182
  = C_pv'45'id_186 | C_pv'45'fst_192 | C_pv'45'snd_198 |
    C_pv'45'pair_210 | C_pv'45'comp_222 | C_pv'45'other_230
-- Once.Arith.Machine.Recognise.p-view
d_p'45'view_238 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PView_182
d_p'45'view_238 v0 v1 v2
  = let v3 = coe C_pv'45'other_230 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.IR.C_id_20 -> coe C_pv'45'id_186
         MAlonzo.Code.Once.IR.C__'8728'__28 v5 v7 v8 -> coe C_pv'45'comp_222
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10 -> coe C_pv'45'pair_210
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_fst_42
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7 -> coe C_pv'45'fst_192
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_snd_48
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7 -> coe C_pv'45'snd_198
                _ -> coe v3
         _ -> coe v3)
-- Once.Arith.Machine.Recognise.recognise-path
d_recognise'45'path_254 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24]
d_recognise'45'path_254 v0 v1 v2
  = coe
      d_recognise'45'path'45'through_260 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Arith.Machine.Recognise.recognise-path-through
d_recognise'45'path'45'through_260 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24]
d_recognise'45'path'45'through_260 v0 v1 v2 v3
  = coe
      d_rp'45'at_268 (coe v0) (coe v1) (coe v2)
      (coe d_p'45'view_238 (coe v0) (coe v1) (coe v2)) (coe v3)
-- Once.Arith.Machine.Recognise.rp-at
d_rp'45'at_268 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PView_182 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24]
d_rp'45'at_268 v0 v1 v2 v3 v4
  = case coe v3 of
      C_pv'45'id_186
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      C_pv'45'fst_192
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26) (coe v4))
      C_pv'45'snd_198
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28) (coe v4))
      C_pv'45'pair_210
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v15 v16
                      -> case coe v4 of
                           [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           (:) v17 v18
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
                                    -> coe
                                         d_pair'45'path_280 (coe v0) (coe v10)
                                         (coe d_plumbing'63'_110 (coe v0) (coe v11) (coe v16))
                                         (coe v15) (coe v18)
                                  MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
                                    -> coe
                                         d_pair'45'path_280 (coe v0) (coe v11)
                                         (coe d_plumbing'63'_110 (coe v0) (coe v10) (coe v15))
                                         (coe v16) (coe v18)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pv'45'comp_222
        -> case coe v2 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v11 v13 v14
               -> coe
                    d_rp'45'comp_274 (coe v0) (coe v11) (coe v14)
                    (coe
                       d_recognise'45'path'45'through_260 (coe v11) (coe v1) (coe v13)
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pv'45'other_230
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.rp-comp
d_rp'45'comp_274 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24]
d_rp'45'comp_274 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             d_recognise'45'path'45'through_260 (coe v0) (coe v1) (coe v2)
             (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.pair-path
d_pair'45'path_280 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24]
d_pair'45'path_280 v0 v1 v2 v3 v4
  = if coe v2
      then coe
             d_recognise'45'path'45'through_260 (coe v0) (coe v1) (coe v3)
             (coe v4)
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Arith.Machine.Recognise.RBView
d_RBView_338 a0 a1 a2 = ()
data T_RBView_338
  = C_v'45'reassoc_354 | C_v'45'sigop_366 | C_v'45'cint_374 |
    C_v'45'cflt_382 | C_v'45'other_390
-- Once.Arith.Machine.Recognise.rb-view
d_rb'45'view_398 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_RBView_338
d_rb'45'view_398 ~v0 ~v1 v2 = du_rb'45'view_398 v2
du_rb'45'view_398 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_RBView_338
du_rb'45'view_398 v0
  = let v1 = coe C_v'45'other_390 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IR.C__'8728'__28 v3 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.IR.C__'8728'__28 v8 v10 v11
                  -> coe C_v'45'reassoc_354
                MAlonzo.Code.Once.IR.C_const_124 v8 v9
                  -> case coe v8 of
                       MAlonzo.Code.Once.IRTy.C_fits'45'int_520 -> coe C_v'45'cint_374
                       MAlonzo.Code.Once.IRTy.C_fits'45'float_522 -> coe C_v'45'cflt_382
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.IR.C_SigOp_130 v7 v8 v9 -> coe C_v'45'sigop_366
                _ -> coe v1
         _ -> coe v1)
-- Once.Arith.Machine.Recognise.lit-at
d_lit'45'at_422 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool ->
  Integer -> Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_lit'45'at_422 ~v0 v1 v2 = du_lit'45'at_422 v1 v2
du_lit'45'at_422 ::
  Bool ->
  Integer -> Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_lit'45'at_422 v0 v1
  = if coe v0
      then coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 (coe v1))
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Arith.Machine.Recognise.flit-at
d_flit'45'at_430 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_flit'45'at_430 ~v0 v1 v2 = du_flit'45'at_430 v1 v2
du_flit'45'at_430 ::
  Bool ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_flit'45'at_430 v0 v1
  = if coe v0
      then coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Arith.Machine.IR.C_aflit_16 (coe v1))
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Arith.Machine.Recognise.path-at
d_path'45'at_440 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_path'45'at_440 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_unop_98 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.d_typePath'63'_160 (coe v0)
                (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.recognise-body
d_recognise'45'body_458 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_recognise'45'body_458 v0 v1 v2 v3
  = coe
      d_rb'45'at_486 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_rb'45'view_398 (coe v3))
-- Once.Arith.Machine.Recognise.recognise-binop
d_recognise'45'binop_466 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_recognise'45'binop_466 v0 v1 v2 v3
  = coe
      d_rbin'45'at_508 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_b'45'view_80 (coe v2) (coe v3))
-- Once.Arith.Machine.Recognise.recognise-prim
d_recognise'45'prim_476 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_recognise'45'prim_476 v0 ~v1 ~v2 v3 v4 v5
  = du_recognise'45'prim_476 v0 v3 v4 v5
du_recognise'45'prim_476 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_recognise'45'prim_476 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.SigOp.Info.C_primV_158 v5
           -> case coe v5 of
                MAlonzo.Code.Once.Arith.Prim.C_p'45'add_366
                  -> coe
                       du_binop_12 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24)
                       (coe
                          d_recognise'45'binop_466 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134)))
                          (coe v3))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'sub_368
                  -> coe
                       du_binop_12 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28)
                       (coe
                          d_recognise'45'binop_466 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134)))
                          (coe v3))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'mul_370
                  -> coe
                       du_binop_12 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32)
                       (coe
                          d_recognise'45'binop_466 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134)))
                          (coe v3))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'div_372
                  -> coe
                       du_binop_12 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36)
                       (coe
                          d_recognise'45'binop_466 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134)))
                          (coe v3))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'mod_374
                  -> coe
                       du_binop_12 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38)
                       (coe
                          d_recognise'45'binop_466 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134)))
                          (coe v3))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_376
                  -> coe
                       du_unop_98 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42)
                       (coe
                          d_recognise'45'body_458 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe MAlonzo.Code.Once.Type.C_Int_134))
                          (coe v3))
                _ -> coe v4
         _ -> coe v4)
-- Once.Arith.Machine.Recognise.rb-at
d_rb'45'at_486 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_RBView_338 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_rb'45'at_486 v0 v1 v2 v3 v4
  = case coe v4 of
      C_v'45'reassoc_354
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v13 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v18 v20 v21
                      -> coe
                           d_recognise'45'body_458 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28 v18 v20
                              (coe MAlonzo.Code.Once.IR.C__'8728'__28 v13 v21 v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_v'45'sigop_366
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v11 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.IR.C_SigOp_130 v15 v16 v17
                      -> coe
                           du_recognise'45'prim_476 (coe v0) (coe v1)
                           (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v17)) (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_v'45'cint_374
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v9 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.IR.C_const_124 v14 v15
                      -> coe
                           du_lit'45'at_422 (coe du_is'45'terminal'63'_174 (coe v1) (coe v12))
                           (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_v'45'cflt_382 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_v'45'other_390
        -> coe
             d_path'45'at_440 (coe v0)
             (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
             (coe d_recognise'45'path_254 (coe v1) (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.binop-at
d_binop'45'at_498 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_binop'45'at_498 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v5
      then coe
             du_pair'45'of_24
             (coe
                d_recognise'45'body_458 (coe v0) (coe v4) (coe v1)
                (coe MAlonzo.Code.Once.IR.C__'8728'__28 v3 v6 v8))
             (coe
                d_recognise'45'body_458 (coe v0) (coe v4) (coe v2)
                (coe MAlonzo.Code.Once.IR.C__'8728'__28 v3 v7 v8))
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Arith.Machine.Recognise.rbin-at
d_rbin'45'at_508 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_BView_36 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rbin'45'at_508 v0 v1 v2 v3 v4
  = case coe v4 of
      C_bv'45'pair_48
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v15 v16
                      -> coe
                           du_pair'45'of_24
                           (coe d_recognise'45'body_458 (coe v0) (coe v1) (coe v10) (coe v15))
                           (coe d_recognise'45'body_458 (coe v0) (coe v1) (coe v11) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bv'45'dist_64
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v15 v17 v18
                      -> case coe v17 of
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v22 v23
                             -> coe
                                  d_binop'45'at_498 (coe v0) (coe v12) (coe v13) (coe v15) (coe v1)
                                  (coe d_plumbing'63'_110 (coe v1) (coe v15) (coe v18)) (coe v22)
                                  (coe v23) (coe v18)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bv'45'other_72
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.recognise-body-float
d_recognise'45'body'45'float_616 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_recognise'45'body'45'float_616 v0 v1 v2 v3
  = coe
      d_rbf'45'at_644 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_rb'45'view_398 (coe v3))
-- Once.Arith.Machine.Recognise.recognise-binop-float
d_recognise'45'binop'45'float_624 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_recognise'45'binop'45'float_624 v0 v1 v2 v3
  = coe
      d_rbinf'45'at_666 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_b'45'view_80 (coe v2) (coe v3))
-- Once.Arith.Machine.Recognise.recognise-prim-float
d_recognise'45'prim'45'float_634 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_recognise'45'prim'45'float_634 v0 ~v1 ~v2 v3 v4 v5
  = du_recognise'45'prim'45'float_634 v0 v3 v4 v5
du_recognise'45'prim'45'float_634 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_recognise'45'prim'45'float_634 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.SigOp.Info.C_primV_158 v5
           -> case coe v5 of
                MAlonzo.Code.Once.Arith.Prim.C_p'45'fadd_378
                  -> coe
                       du_binop_12 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24)
                       (coe
                          d_recognise'45'binop'45'float_624 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe MAlonzo.Code.Once.Type.C_Float_136)))
                          (coe v3))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'fsub_380
                  -> coe
                       du_binop_12 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28)
                       (coe
                          d_recognise'45'binop'45'float_624 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe MAlonzo.Code.Once.Type.C_Float_136)))
                          (coe v3))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'fmul_382
                  -> coe
                       du_binop_12 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32)
                       (coe
                          d_recognise'45'binop'45'float_624 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe MAlonzo.Code.Once.Type.C_Float_136)))
                          (coe v3))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'fdiv_384
                  -> coe
                       du_binop_12 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36)
                       (coe
                          d_recognise'45'binop'45'float_624 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe MAlonzo.Code.Once.Type.C_Float_136)))
                          (coe v3))
                MAlonzo.Code.Once.Arith.Prim.C_p'45'i2f_386
                  -> coe
                       du_unop_98 (coe MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44)
                       (coe
                          d_recognise'45'body_458 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe MAlonzo.Code.Once.Type.C_Int_134))
                          (coe v3))
                _ -> coe v4
         _ -> coe v4)
-- Once.Arith.Machine.Recognise.rbf-at
d_rbf'45'at_644 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_RBView_338 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_rbf'45'at_644 v0 v1 v2 v3 v4
  = case coe v4 of
      C_v'45'reassoc_354
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v13 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v18 v20 v21
                      -> coe
                           d_recognise'45'body'45'float_616 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28 v18 v20
                              (coe MAlonzo.Code.Once.IR.C__'8728'__28 v13 v21 v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_v'45'sigop_366
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v11 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.IR.C_SigOp_130 v15 v16 v17
                      -> coe
                           du_recognise'45'prim'45'float_634 (coe v0) (coe v1)
                           (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v17)) (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_v'45'cint_374 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_v'45'cflt_382
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v9 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.IR.C_const_124 v14 v15
                      -> coe
                           du_flit'45'at_430
                           (coe du_is'45'terminal'63'_174 (coe v1) (coe v12)) (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_v'45'other_390
        -> coe
             d_path'45'at_440 (coe v0)
             (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
             (coe d_recognise'45'path_254 (coe v1) (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.binop-at-float
d_binop'45'at'45'float_656 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_binop'45'at'45'float_656 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v5
      then coe
             du_pair'45'of_24
             (coe
                d_recognise'45'body'45'float_616 (coe v0) (coe v4) (coe v1)
                (coe MAlonzo.Code.Once.IR.C__'8728'__28 v3 v6 v8))
             (coe
                d_recognise'45'body'45'float_616 (coe v0) (coe v4) (coe v2)
                (coe MAlonzo.Code.Once.IR.C__'8728'__28 v3 v7 v8))
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Arith.Machine.Recognise.rbinf-at
d_rbinf'45'at_666 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_BView_36 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rbinf'45'at_666 v0 v1 v2 v3 v4
  = case coe v4 of
      C_bv'45'pair_48
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v15 v16
                      -> coe
                           du_pair'45'of_24
                           (coe
                              d_recognise'45'body'45'float_616 (coe v0) (coe v1) (coe v10)
                              (coe v15))
                           (coe
                              d_recognise'45'body'45'float_616 (coe v0) (coe v1) (coe v11)
                              (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bv'45'dist_64
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v15 v17 v18
                      -> case coe v17 of
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v22 v23
                             -> coe
                                  d_binop'45'at'45'float_656 (coe v0) (coe v12) (coe v13) (coe v15)
                                  (coe v1) (coe d_plumbing'63'_110 (coe v1) (coe v15) (coe v18))
                                  (coe v22) (coe v23) (coe v18)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bv'45'other_72
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Recognise.recognise
d_recognise_772 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_126
d_recognise_772 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Type.C_NInt_8
        -> let v5
                 = d_rb'45'at_486
                     (coe v0) (coe v2) (coe v3) (coe v4)
                     (coe du_rb'45'view_398 (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_140 (coe v0)
                          (coe v1) (coe v6))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Type.C_NFloat_10
        -> let v5
                 = d_rbf'45'at_644
                     (coe v0) (coe v2) (coe v3) (coe v4)
                     (coe du_rb'45'view_398 (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_140 (coe v0)
                          (coe v1) (coe v6))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
