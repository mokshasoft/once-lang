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
d_readLoc_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_26 ~v0 ~v1 = du_readLoc_26
du_readLoc_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_26
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.CCC.Machine.Validity.ValidityDef._.BeforeFrontier
d_BeforeFrontier_64 a0 a1 a2 a3 = ()
-- Once.CCC.Machine.Validity.ValidityDef.ValidAt
d_ValidAt_132 a0 a1 a2 a3 a4 a5 a6 = ()
data T_ValidAt_132
  = C_valid'45'unit_140 |
    C_valid'45'pair_158 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                        T_ValidAt_132 T_ValidAt_132 |
    C_valid'45'inl_172 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       T_ValidAt_132 |
    C_valid'45'inr_186 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       T_ValidAt_132 |
    C_valid'45'closure_210 MAlonzo.Code.Once.IRTy.T_IRTy_6
                           MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                           MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                           MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                           T_ValidAt_132
-- Once.CCC.Machine.Validity.ValidityDef.PairValid
d_PairValid_224 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_PairValid_224
  = C_constructor_274 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      T_ValidAt_132 T_ValidAt_132
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-loc
d_fst'45'loc_256 ::
  T_PairValid_224 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_fst'45'loc_256 v0
  = case coe v0 of
      C_constructor_274 v1 v2 v5 v6 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-loc
d_snd'45'loc_258 ::
  T_PairValid_224 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_snd'45'loc_258 v0
  = case coe v0 of
      C_constructor_274 v1 v2 v5 v6 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-ptr
d_fst'45'ptr_260 ::
  T_PairValid_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'ptr_260 = erased
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-ptr
d_snd'45'ptr_262 ::
  T_PairValid_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'ptr_262 = erased
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-before
d_fst'45'before_264 ::
  T_PairValid_224 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_fst'45'before_264 v0
  = case coe v0 of
      C_constructor_274 v1 v2 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-before
d_snd'45'before_266 ::
  T_PairValid_224 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_snd'45'before_266 v0
  = case coe v0 of
      C_constructor_274 v1 v2 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.sucLoc-before
d_sucLoc'45'before_268 ::
  T_PairValid_224 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sucLoc'45'before_268 v0
  = case coe v0 of
      C_constructor_274 v1 v2 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-valid
d_fst'45'valid_270 :: T_PairValid_224 -> T_ValidAt_132
d_fst'45'valid_270 v0
  = case coe v0 of
      C_constructor_274 v1 v2 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-valid
d_snd'45'valid_272 :: T_PairValid_224 -> T_ValidAt_132
d_snd'45'valid_272 v0
  = case coe v0 of
      C_constructor_274 v1 v2 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid
d_ClosureValid_288 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_ClosureValid_288
  = C_constructor_358 MAlonzo.Code.Once.IRTy.T_IRTy_6
                      MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      T_ValidAt_132
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.EnvType
d_EnvType_330 ::
  T_ClosureValid_288 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_330 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.body
d_body_332 :: T_ClosureValid_288 -> MAlonzo.Code.Once.IR.T_IR_16
d_body_332 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env
d_env_334 :: T_ClosureValid_288 -> AgdaAny
d_env_334 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.body<bound
d_body'60'bound_336 ::
  T_ClosureValid_288 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_body'60'bound_336 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-loc
d_env'45'loc_338 ::
  T_ClosureValid_288 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_env'45'loc_338 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.code-loc
d_code'45'loc_340 ::
  T_ClosureValid_288 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_code'45'loc_340 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-ptr
d_env'45'ptr_342 ::
  T_ClosureValid_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_342 = erased
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.code-ptr
d_code'45'ptr_344 ::
  T_ClosureValid_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_344 = erased
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-before
d_env'45'before_346 ::
  T_ClosureValid_288 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_env'45'before_346 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.code-before
d_code'45'before_348 ::
  T_ClosureValid_288 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_code'45'before_348 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.sucLoc-before
d_sucLoc'45'before_350 ::
  T_ClosureValid_288 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sucLoc'45'before_350 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-valid
d_env'45'valid_352 :: T_ClosureValid_288 -> T_ValidAt_132
d_env'45'valid_352 v0
  = case coe v0 of
      C_constructor_358 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.f-is-closure
d_f'45'is'45'closure_356 ::
  T_ClosureValid_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_356 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InlValid
d_InlValid_372 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InlValid_372
  = C_constructor_414 AgdaAny
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      T_ValidAt_132
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.a
d_a_400 :: T_InlValid_372 -> AgdaAny
d_a_400 v0
  = case coe v0 of
      C_constructor_414 v1 v2 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-loc
d_payload'45'loc_402 ::
  T_InlValid_372 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_402 v0
  = case coe v0 of
      C_constructor_414 v1 v2 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-ptr
d_payload'45'ptr_404 ::
  T_InlValid_372 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_404 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-before
d_payload'45'before_406 ::
  T_InlValid_372 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_payload'45'before_406 v0
  = case coe v0 of
      C_constructor_414 v1 v2 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.sucLoc-before
d_sucLoc'45'before_408 ::
  T_InlValid_372 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sucLoc'45'before_408 v0
  = case coe v0 of
      C_constructor_414 v1 v2 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-valid
d_payload'45'valid_410 :: T_InlValid_372 -> T_ValidAt_132
d_payload'45'valid_410 v0
  = case coe v0 of
      C_constructor_414 v1 v2 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.v-is-inl
d_v'45'is'45'inl_412 ::
  T_InlValid_372 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_412 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InrValid
d_InrValid_428 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InrValid_428
  = C_constructor_470 AgdaAny
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                      T_ValidAt_132
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.b
d_b_456 :: T_InrValid_428 -> AgdaAny
d_b_456 v0
  = case coe v0 of
      C_constructor_470 v1 v2 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-loc
d_payload'45'loc_458 ::
  T_InrValid_428 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_458 v0
  = case coe v0 of
      C_constructor_470 v1 v2 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-ptr
d_payload'45'ptr_460 ::
  T_InrValid_428 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_460 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-before
d_payload'45'before_462 ::
  T_InrValid_428 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_payload'45'before_462 v0
  = case coe v0 of
      C_constructor_470 v1 v2 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.sucLoc-before
d_sucLoc'45'before_464 ::
  T_InrValid_428 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sucLoc'45'before_464 v0
  = case coe v0 of
      C_constructor_470 v1 v2 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-valid
d_payload'45'valid_466 :: T_InrValid_428 -> T_ValidAt_132
d_payload'45'valid_466 v0
  = case coe v0 of
      C_constructor_470 v1 v2 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.v-is-inr
d_v'45'is'45'inr_468 ::
  T_InrValid_428 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_468 = erased
-- Once.CCC.Machine.Validity.ValidityDef.decomposePair
d_decomposePair_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAt_132 -> T_PairValid_224
d_decomposePair_484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_decomposePair_484 v8
du_decomposePair_484 :: T_ValidAt_132 -> T_PairValid_224
du_decomposePair_484 v0
  = case coe v0 of
      C_valid'45'pair_158 v6 v7 v11 v12 v13 v14 v15
        -> coe C_constructor_274 v6 v7 v11 v12 v13 v14 v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.decomposeClosure
d_decomposeClosure_516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAt_132 -> T_ClosureValid_288
d_decomposeClosure_516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_decomposeClosure_516 v8
du_decomposeClosure_516 :: T_ValidAt_132 -> T_ClosureValid_288
du_decomposeClosure_516 v0
  = case coe v0 of
      C_valid'45'closure_210 v1 v4 v5 v6 v8 v9 v13 v14 v15 v16
        -> coe C_constructor_358 v1 v4 v5 v6 v8 v9 v13 v14 v15 v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.decomposeInl
d_decomposeInl_554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAt_132 -> T_InlValid_372
d_decomposeInl_554 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_decomposeInl_554 v5 v8
du_decomposeInl_554 :: AgdaAny -> T_ValidAt_132 -> T_InlValid_372
du_decomposeInl_554 v0 v1
  = case coe v1 of
      C_valid'45'inl_172 v6 v9 v10 v11
        -> coe C_constructor_414 v0 v6 v9 v10 v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.decomposeInr
d_decomposeInr_584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAt_132 -> T_InrValid_428
d_decomposeInr_584 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_decomposeInr_584 v5 v8
du_decomposeInr_584 :: AgdaAny -> T_ValidAt_132 -> T_InrValid_428
du_decomposeInr_584 v0 v1
  = case coe v1 of
      C_valid'45'inr_186 v6 v9 v10 v11
        -> coe C_constructor_470 v0 v6 v9 v10 v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.composePair
d_composePair_620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132 -> T_ValidAt_132
d_composePair_620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11
                  ~v12 v13 v14 v15 v16 v17
  = du_composePair_620 v8 v9 v13 v14 v15 v16 v17
du_composePair_620 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132 -> T_ValidAt_132
du_composePair_620 v0 v1 v2 v3 v4 v5 v6
  = coe C_valid'45'pair_158 v0 v1 v2 v3 v4 v5 v6
-- Once.CCC.Machine.Validity.ValidityDef.composeClosure
d_composeClosure_672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132
d_composeClosure_672 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 ~v9 v10 v11
                     ~v12 ~v13 ~v14 v15 v16 v17 v18
  = du_composeClosure_672 v3 v6 v7 v8 v10 v11 v15 v16 v17 v18
du_composeClosure_672 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132
du_composeClosure_672 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe C_valid'45'closure_210 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
-- Once.CCC.Machine.Validity.ValidityDef.composeInl
d_composeInl_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132
d_composeInl_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 v12
  = du_composeInl_714 v7 v10 v11 v12
du_composeInl_714 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132
du_composeInl_714 v0 v1 v2 v3 = coe C_valid'45'inl_172 v0 v1 v2 v3
-- Once.CCC.Machine.Validity.ValidityDef.composeInr
d_composeInr_746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132
d_composeInr_746 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 v12
  = du_composeInr_746 v7 v10 v11 v12
du_composeInr_746 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132
du_composeInr_746 v0 v1 v2 v3 = coe C_valid'45'inr_186 v0 v1 v2 v3
-- Once.CCC.Machine.Validity.ValidityDef.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_770 = erased
-- Once.CCC.Machine.Validity.ValidityDef.validity-mem-only
d_validity'45'mem'45'only_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ValidAt_132 -> T_ValidAt_132
d_validity'45'mem'45'only_810 v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 ~v9 v10
  = du_validity'45'mem'45'only_810 v0 v1 v2 v3 v4 v6 v7 v10
du_validity'45'mem'45'only_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAt_132 -> T_ValidAt_132
du_validity'45'mem'45'only_810 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v4) (coe seq (coe v7) (coe C_valid'45'unit_140))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v7 of
                    C_valid'45'pair_158 v17 v18 v22 v23 v24 v25 v26
                      -> coe
                           C_valid'45'pair_158 v17 v18 v22 v23 v24
                           (coe
                              du_fv''_870 (coe v0) (coe v1) (coe v2) (coe v8) (coe v10) (coe v5)
                              (coe v6) (coe v17) (coe v25))
                           (coe
                              du_sv''_872 (coe v0) (coe v1) (coe v2) (coe v9) (coe v11) (coe v5)
                              (coe v6) (coe v18) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
        -> case coe v7 of
             C_valid'45'inl_172 v14 v17 v18 v19
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                      -> coe
                           C_valid'45'inl_172 v14 v17 v18
                           (coe
                              du_pv''_960 (coe v0) (coe v1) (coe v2) (coe v8) (coe v5) (coe v6)
                              (coe v20) (coe v14) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr_186 v14 v17 v18 v19
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                      -> coe
                           C_valid'45'inr_186 v14 v17 v18
                           (coe
                              du_pv''_996 (coe v0) (coe v1) (coe v2) (coe v9) (coe v5) (coe v6)
                              (coe v20) (coe v14) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
        -> case coe v7 of
             C_valid'45'closure_210 v10 v13 v14 v15 v17 v18 v22 v23 v24 v25
               -> coe
                    C_valid'45'closure_210 v10 v13 v14 v15 v17 v18 v22 v23 v24
                    (coe
                       du_ev''_924 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6) (coe v10)
                       (coe v14) (coe v17) (coe v25))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef._.fp'
d_fp''_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 ->
  T_ValidAt_132 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_866 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.sp'
d_sp''_868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 ->
  T_ValidAt_132 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_868 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.fv'
d_fv''_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132 -> T_ValidAt_132
d_fv''_870 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13 ~v14
           ~v15 ~v16 ~v17 ~v18 v19 ~v20
  = du_fv''_870 v0 v1 v2 v3 v5 v8 v9 v12 v19
du_fv''_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_132 -> T_ValidAt_132
du_fv''_870 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_810 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.sv'
d_sv''_872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132 -> T_ValidAt_132
d_sv''_872 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 ~v12 v13 ~v14
           ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_sv''_872 v0 v1 v2 v4 v6 v8 v9 v13 v20
du_sv''_872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_132 -> T_ValidAt_132
du_sv''_872 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_810 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.ep'
d_ep''_920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_920 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.cp'
d_cp''_922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_922 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.ev'
d_ev''_924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132
d_ev''_924 v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 ~v11 v12 ~v13 v14
           ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_ev''_924 v0 v1 v2 v6 v7 v10 v12 v14 v21
du_ev''_924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_132 -> T_ValidAt_132
du_ev''_924 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_810 (coe v0) (coe v1) (coe v2) (coe v5)
      (coe v6) (coe v3) (coe v4) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.pp'
d_pp''_958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_958 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.pv'
d_pv''_960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132
d_pv''_960 v0 v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 ~v14
           v15
  = du_pv''_960 v0 v1 v2 v3 v6 v7 v10 v11 v15
du_pv''_960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_132 -> T_ValidAt_132
du_pv''_960 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_810 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v6) (coe v4) (coe v5) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.pp'
d_pp''_994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_994 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.pv'
d_pv''_996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAt_132 -> T_ValidAt_132
d_pv''_996 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 ~v14
           v15
  = du_pv''_996 v0 v1 v2 v4 v6 v7 v10 v11 v15
du_pv''_996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_132 -> T_ValidAt_132
du_pv''_996 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_810 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v6) (coe v4) (coe v5) (coe v8)
