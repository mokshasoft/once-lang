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

module MAlonzo.Code.Once.CCC.Machine.Validity where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.Validity.pair
d_pair_8 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair_8 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_306 v2 v3
-- Once.CCC.Machine.Validity.ValidityDef._.readLoc
d_readLoc_20 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_20 ~v0 ~v1 = du_readLoc_20
du_readLoc_20 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_20
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_730
-- Once.CCC.Machine.Validity.ValidityDef._.BeforeFrontier
d_BeforeFrontier_58 a0 a1 a2 a3 = ()
-- Once.CCC.Machine.Validity.ValidityDef.ValidAt
d_ValidAt_126 a0 a1 a2 a3 a4 a5 a6 = ()
data T_ValidAt_126
  = C_valid'45'unit_134 |
    C_valid'45'pair_152 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                        T_ValidAt_126 T_ValidAt_126 |
    C_valid'45'inl_166 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       T_ValidAt_126 |
    C_valid'45'inr_180 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       T_ValidAt_126 |
    C_valid'45'closure_204 MAlonzo.Code.Once.IRTy.T_IRTy_6
                           MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                           MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                           MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                           T_ValidAt_126
-- Once.CCC.Machine.Validity.ValidityDef.PairValid
d_PairValid_218 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_PairValid_218
  = C_constructor_268 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      T_ValidAt_126 T_ValidAt_126
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-loc
d_fst'45'loc_250 ::
  T_PairValid_218 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_fst'45'loc_250 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v5 v6 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-loc
d_snd'45'loc_252 ::
  T_PairValid_218 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_snd'45'loc_252 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v5 v6 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-ptr
d_fst'45'ptr_254 ::
  T_PairValid_218 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'ptr_254 = erased
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-ptr
d_snd'45'ptr_256 ::
  T_PairValid_218 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'ptr_256 = erased
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-before
d_fst'45'before_258 ::
  T_PairValid_218 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_fst'45'before_258 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-before
d_snd'45'before_260 ::
  T_PairValid_218 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_snd'45'before_260 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.sucLoc-before
d_sucLoc'45'before_262 ::
  T_PairValid_218 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sucLoc'45'before_262 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-valid
d_fst'45'valid_264 :: T_PairValid_218 -> T_ValidAt_126
d_fst'45'valid_264 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-valid
d_snd'45'valid_266 :: T_PairValid_218 -> T_ValidAt_126
d_snd'45'valid_266 v0
  = case coe v0 of
      C_constructor_268 v1 v2 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid
d_ClosureValid_282 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_ClosureValid_282
  = C_constructor_352 MAlonzo.Code.Once.IRTy.T_IRTy_6
                      MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      T_ValidAt_126
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.EnvType
d_EnvType_324 ::
  T_ClosureValid_282 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_324 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.body
d_body_326 :: T_ClosureValid_282 -> MAlonzo.Code.Once.IR.T_IR_16
d_body_326 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env
d_env_328 :: T_ClosureValid_282 -> AgdaAny
d_env_328 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.body<bound
d_body'60'bound_330 ::
  T_ClosureValid_282 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_body'60'bound_330 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-loc
d_env'45'loc_332 ::
  T_ClosureValid_282 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_env'45'loc_332 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.code-loc
d_code'45'loc_334 ::
  T_ClosureValid_282 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_code'45'loc_334 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-ptr
d_env'45'ptr_336 ::
  T_ClosureValid_282 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_336 = erased
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.code-ptr
d_code'45'ptr_338 ::
  T_ClosureValid_282 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_338 = erased
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-before
d_env'45'before_340 ::
  T_ClosureValid_282 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_env'45'before_340 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.code-before
d_code'45'before_342 ::
  T_ClosureValid_282 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_code'45'before_342 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.sucLoc-before
d_sucLoc'45'before_344 ::
  T_ClosureValid_282 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sucLoc'45'before_344 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-valid
d_env'45'valid_346 :: T_ClosureValid_282 -> T_ValidAt_126
d_env'45'valid_346 v0
  = case coe v0 of
      C_constructor_352 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.f-is-closure
d_f'45'is'45'closure_350 ::
  T_ClosureValid_282 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_350 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InlValid
d_InlValid_366 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InlValid_366
  = C_constructor_408 AgdaAny
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      T_ValidAt_126
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.a
d_a_394 :: T_InlValid_366 -> AgdaAny
d_a_394 v0
  = case coe v0 of
      C_constructor_408 v1 v2 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-loc
d_payload'45'loc_396 ::
  T_InlValid_366 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_396 v0
  = case coe v0 of
      C_constructor_408 v1 v2 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-ptr
d_payload'45'ptr_398 ::
  T_InlValid_366 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_398 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-before
d_payload'45'before_400 ::
  T_InlValid_366 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_payload'45'before_400 v0
  = case coe v0 of
      C_constructor_408 v1 v2 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.sucLoc-before
d_sucLoc'45'before_402 ::
  T_InlValid_366 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sucLoc'45'before_402 v0
  = case coe v0 of
      C_constructor_408 v1 v2 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-valid
d_payload'45'valid_404 :: T_InlValid_366 -> T_ValidAt_126
d_payload'45'valid_404 v0
  = case coe v0 of
      C_constructor_408 v1 v2 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.v-is-inl
d_v'45'is'45'inl_406 ::
  T_InlValid_366 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_406 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InrValid
d_InrValid_422 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InrValid_422
  = C_constructor_464 AgdaAny
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                      T_ValidAt_126
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.b
d_b_450 :: T_InrValid_422 -> AgdaAny
d_b_450 v0
  = case coe v0 of
      C_constructor_464 v1 v2 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-loc
d_payload'45'loc_452 ::
  T_InrValid_422 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_452 v0
  = case coe v0 of
      C_constructor_464 v1 v2 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-ptr
d_payload'45'ptr_454 ::
  T_InrValid_422 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_454 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-before
d_payload'45'before_456 ::
  T_InrValid_422 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_payload'45'before_456 v0
  = case coe v0 of
      C_constructor_464 v1 v2 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.sucLoc-before
d_sucLoc'45'before_458 ::
  T_InrValid_422 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sucLoc'45'before_458 v0
  = case coe v0 of
      C_constructor_464 v1 v2 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-valid
d_payload'45'valid_460 :: T_InrValid_422 -> T_ValidAt_126
d_payload'45'valid_460 v0
  = case coe v0 of
      C_constructor_464 v1 v2 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.v-is-inr
d_v'45'is'45'inr_462 ::
  T_InrValid_422 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_462 = erased
-- Once.CCC.Machine.Validity.ValidityDef.decomposePair
d_decomposePair_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_ValidAt_126 -> T_PairValid_218
d_decomposePair_478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_decomposePair_478 v8
du_decomposePair_478 :: T_ValidAt_126 -> T_PairValid_218
du_decomposePair_478 v0
  = case coe v0 of
      C_valid'45'pair_152 v6 v7 v11 v12 v13 v14 v15
        -> coe C_constructor_268 v6 v7 v11 v12 v13 v14 v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.decomposeClosure
d_decomposeClosure_510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_ValidAt_126 -> T_ClosureValid_282
d_decomposeClosure_510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_decomposeClosure_510 v8
du_decomposeClosure_510 :: T_ValidAt_126 -> T_ClosureValid_282
du_decomposeClosure_510 v0
  = case coe v0 of
      C_valid'45'closure_204 v1 v4 v5 v6 v8 v9 v13 v14 v15 v16
        -> coe C_constructor_352 v1 v4 v5 v6 v8 v9 v13 v14 v15 v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.decomposeInl
d_decomposeInl_548 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_ValidAt_126 -> T_InlValid_366
d_decomposeInl_548 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_decomposeInl_548 v5 v8
du_decomposeInl_548 :: AgdaAny -> T_ValidAt_126 -> T_InlValid_366
du_decomposeInl_548 v0 v1
  = case coe v1 of
      C_valid'45'inl_166 v6 v9 v10 v11
        -> coe C_constructor_408 v0 v6 v9 v10 v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.decomposeInr
d_decomposeInr_578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_ValidAt_126 -> T_InrValid_422
d_decomposeInr_578 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_decomposeInr_578 v5 v8
du_decomposeInr_578 :: AgdaAny -> T_ValidAt_126 -> T_InrValid_422
du_decomposeInr_578 v0 v1
  = case coe v1 of
      C_valid'45'inr_180 v6 v9 v10 v11
        -> coe C_constructor_464 v0 v6 v9 v10 v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.composePair
d_composePair_614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126 -> T_ValidAt_126
d_composePair_614 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11
                  ~v12 v13 v14 v15 v16 v17
  = du_composePair_614 v8 v9 v13 v14 v15 v16 v17
du_composePair_614 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126 -> T_ValidAt_126
du_composePair_614 v0 v1 v2 v3 v4 v5 v6
  = coe C_valid'45'pair_152 v0 v1 v2 v3 v4 v5 v6
-- Once.CCC.Machine.Validity.ValidityDef.composeClosure
d_composeClosure_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126
d_composeClosure_666 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 ~v9 v10 v11
                     ~v12 ~v13 ~v14 v15 v16 v17 v18
  = du_composeClosure_666 v3 v6 v7 v8 v10 v11 v15 v16 v17 v18
du_composeClosure_666 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126
du_composeClosure_666 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe C_valid'45'closure_204 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
-- Once.CCC.Machine.Validity.ValidityDef.composeInl
d_composeInl_708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126
d_composeInl_708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 v12
  = du_composeInl_708 v7 v10 v11 v12
du_composeInl_708 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126
du_composeInl_708 v0 v1 v2 v3 = coe C_valid'45'inl_166 v0 v1 v2 v3
-- Once.CCC.Machine.Validity.ValidityDef.composeInr
d_composeInr_740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126
d_composeInr_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 v12
  = du_composeInr_740 v7 v10 v11 v12
du_composeInr_740 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126
du_composeInr_740 v0 v1 v2 v3 = coe C_valid'45'inr_180 v0 v1 v2 v3
-- Once.CCC.Machine.Validity.ValidityDef.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_764 = erased
-- Once.CCC.Machine.Validity.ValidityDef.validity-mem-only
d_validity'45'mem'45'only_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ValidAt_126 -> T_ValidAt_126
d_validity'45'mem'45'only_804 v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 ~v9 v10
  = du_validity'45'mem'45'only_804 v0 v1 v2 v3 v4 v6 v7 v10
du_validity'45'mem'45'only_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  T_ValidAt_126 -> T_ValidAt_126
du_validity'45'mem'45'only_804 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v4) (coe seq (coe v7) (coe C_valid'45'unit_134))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v7 of
                    C_valid'45'pair_152 v17 v18 v22 v23 v24 v25 v26
                      -> coe
                           C_valid'45'pair_152 v17 v18 v22 v23 v24
                           (coe
                              du_fv''_864 (coe v0) (coe v1) (coe v2) (coe v8) (coe v10) (coe v5)
                              (coe v6) (coe v17) (coe v25))
                           (coe
                              du_sv''_866 (coe v0) (coe v1) (coe v2) (coe v9) (coe v11) (coe v5)
                              (coe v6) (coe v18) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
        -> case coe v7 of
             C_valid'45'inl_166 v14 v17 v18 v19
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                      -> coe
                           C_valid'45'inl_166 v14 v17 v18
                           (coe
                              du_pv''_954 (coe v0) (coe v1) (coe v2) (coe v8) (coe v5) (coe v6)
                              (coe v20) (coe v14) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr_180 v14 v17 v18 v19
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                      -> coe
                           C_valid'45'inr_180 v14 v17 v18
                           (coe
                              du_pv''_990 (coe v0) (coe v1) (coe v2) (coe v9) (coe v5) (coe v6)
                              (coe v20) (coe v14) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
        -> case coe v7 of
             C_valid'45'closure_204 v10 v13 v14 v15 v17 v18 v22 v23 v24 v25
               -> coe
                    C_valid'45'closure_204 v10 v13 v14 v15 v17 v18 v22 v23 v24
                    (coe
                       du_ev''_918 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6) (coe v10)
                       (coe v14) (coe v17) (coe v25))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef._.fp'
d_fp''_860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 ->
  T_ValidAt_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_860 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.sp'
d_sp''_862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 ->
  T_ValidAt_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_862 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.fv'
d_fv''_864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126 -> T_ValidAt_126
d_fv''_864 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13 ~v14
           ~v15 ~v16 ~v17 ~v18 v19 ~v20
  = du_fv''_864 v0 v1 v2 v3 v5 v8 v9 v12 v19
du_fv''_864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_126 -> T_ValidAt_126
du_fv''_864 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_804 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.sv'
d_sv''_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126 -> T_ValidAt_126
d_sv''_866 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 ~v12 v13 ~v14
           ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_sv''_866 v0 v1 v2 v4 v6 v8 v9 v13 v20
du_sv''_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_126 -> T_ValidAt_126
du_sv''_866 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_804 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.ep'
d_ep''_914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_914 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.cp'
d_cp''_916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_916 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.ev'
d_ev''_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126
d_ev''_918 v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 ~v11 v12 ~v13 v14
           ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_ev''_918 v0 v1 v2 v6 v7 v10 v12 v14 v21
du_ev''_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_126 -> T_ValidAt_126
du_ev''_918 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_804 (coe v0) (coe v1) (coe v2) (coe v5)
      (coe v6) (coe v3) (coe v4) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.pp'
d_pp''_952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_952 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.pv'
d_pv''_954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126
d_pv''_954 v0 v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 ~v14
           v15
  = du_pv''_954 v0 v1 v2 v3 v6 v7 v10 v11 v15
du_pv''_954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_126 -> T_ValidAt_126
du_pv''_954 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_804 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v6) (coe v4) (coe v5) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.pp'
d_pp''_988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_988 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.pv'
d_pv''_990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAt_126 -> T_ValidAt_126
d_pv''_990 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 ~v14
           v15
  = du_pv''_990 v0 v1 v2 v4 v6 v7 v10 v11 v15
du_pv''_990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_594 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_126 -> T_ValidAt_126
du_pv''_990 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_804 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v6) (coe v4) (coe v5) (coe v8)
