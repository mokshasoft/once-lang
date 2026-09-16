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
import qualified MAlonzo.Code.Once.CCC.Eval
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
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair_8 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'pair_322 v2 v3
-- Once.CCC.Machine.Validity.ReadLocEq._.readLoc
d_readLoc_24 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_24 ~v0 = du_readLoc_24
du_readLoc_24 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_24
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Machine.Validity.ReadLocEq.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_62 = erased
-- Once.CCC.Machine.Validity.ValidityDef.eval
d_eval_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_eval_100 v0 ~v1 v2 v3 = du_eval_100 v0 v2 v3
du_eval_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_eval_100 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Eval.d_eval_12 (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_158 (coe v0))
-- Once.CCC.Machine.Validity.ValidityDef._.readLoc
d_readLoc_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_112 ~v0 ~v1 = du_readLoc_112
du_readLoc_112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_112
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Machine.Validity.ValidityDef._.BeforeFrontier
d_BeforeFrontier_150 a0 a1 a2 a3 = ()
-- Once.CCC.Machine.Validity.ValidityDef.ValidAt
d_ValidAt_218 a0 a1 a2 a3 a4 a5 a6 = ()
data T_ValidAt_218
  = C_valid'45'unit_226 |
    C_valid'45'pair_244 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                        T_ValidAt_218 T_ValidAt_218 |
    C_valid'45'inl_258 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_ValidAt_218 |
    C_valid'45'inr_272 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_ValidAt_218 |
    C_valid'45'closure_296 MAlonzo.Code.Once.IRTy.T_IRTy_6
                           MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                           MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                           MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                           T_ValidAt_218
-- Once.CCC.Machine.Validity.ValidityDef.PairValid
d_PairValid_310 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_PairValid_310
  = C_constructor_360 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      T_ValidAt_218 T_ValidAt_218
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-loc
d_fst'45'loc_342 ::
  T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_fst'45'loc_342 v0
  = case coe v0 of
      C_constructor_360 v1 v2 v5 v6 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-loc
d_snd'45'loc_344 ::
  T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_snd'45'loc_344 v0
  = case coe v0 of
      C_constructor_360 v1 v2 v5 v6 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-ptr
d_fst'45'ptr_346 ::
  T_PairValid_310 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'ptr_346 = erased
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-ptr
d_snd'45'ptr_348 ::
  T_PairValid_310 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'ptr_348 = erased
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-before
d_fst'45'before_350 ::
  T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_fst'45'before_350 v0
  = case coe v0 of
      C_constructor_360 v1 v2 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-before
d_snd'45'before_352 ::
  T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_snd'45'before_352 v0
  = case coe v0 of
      C_constructor_360 v1 v2 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.sucLoc-before
d_sucLoc'45'before_354 ::
  T_PairValid_310 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_354 v0
  = case coe v0 of
      C_constructor_360 v1 v2 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.fst-valid
d_fst'45'valid_356 :: T_PairValid_310 -> T_ValidAt_218
d_fst'45'valid_356 v0
  = case coe v0 of
      C_constructor_360 v1 v2 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.PairValid.snd-valid
d_snd'45'valid_358 :: T_PairValid_310 -> T_ValidAt_218
d_snd'45'valid_358 v0
  = case coe v0 of
      C_constructor_360 v1 v2 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid
d_ClosureValid_374 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_ClosureValid_374
  = C_constructor_444 MAlonzo.Code.Once.IRTy.T_IRTy_6
                      MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      T_ValidAt_218
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.EnvType
d_EnvType_416 ::
  T_ClosureValid_374 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_416 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.body
d_body_418 :: T_ClosureValid_374 -> MAlonzo.Code.Once.IR.T_IR_16
d_body_418 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env
d_env_420 :: T_ClosureValid_374 -> AgdaAny
d_env_420 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.body<bound
d_body'60'bound_422 ::
  T_ClosureValid_374 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_body'60'bound_422 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-loc
d_env'45'loc_424 ::
  T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_env'45'loc_424 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.code-loc
d_code'45'loc_426 ::
  T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_code'45'loc_426 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-ptr
d_env'45'ptr_428 ::
  T_ClosureValid_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_428 = erased
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.code-ptr
d_code'45'ptr_430 ::
  T_ClosureValid_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_430 = erased
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-before
d_env'45'before_432 ::
  T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_env'45'before_432 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.code-before
d_code'45'before_434 ::
  T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_code'45'before_434 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.sucLoc-before
d_sucLoc'45'before_436 ::
  T_ClosureValid_374 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_436 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.env-valid
d_env'45'valid_438 :: T_ClosureValid_374 -> T_ValidAt_218
d_env'45'valid_438 v0
  = case coe v0 of
      C_constructor_444 v1 v2 v3 v4 v5 v6 v9 v10 v11 v12 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.ClosureValid.f-is-closure
d_f'45'is'45'closure_442 ::
  T_ClosureValid_374 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_442 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InlValid
d_InlValid_458 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InlValid_458
  = C_constructor_500 AgdaAny
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      T_ValidAt_218
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.a
d_a_486 :: T_InlValid_458 -> AgdaAny
d_a_486 v0
  = case coe v0 of
      C_constructor_500 v1 v2 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-loc
d_payload'45'loc_488 ::
  T_InlValid_458 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_488 v0
  = case coe v0 of
      C_constructor_500 v1 v2 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-ptr
d_payload'45'ptr_490 ::
  T_InlValid_458 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_490 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-before
d_payload'45'before_492 ::
  T_InlValid_458 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_payload'45'before_492 v0
  = case coe v0 of
      C_constructor_500 v1 v2 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.sucLoc-before
d_sucLoc'45'before_494 ::
  T_InlValid_458 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_494 v0
  = case coe v0 of
      C_constructor_500 v1 v2 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.payload-valid
d_payload'45'valid_496 :: T_InlValid_458 -> T_ValidAt_218
d_payload'45'valid_496 v0
  = case coe v0 of
      C_constructor_500 v1 v2 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InlValid.v-is-inl
d_v'45'is'45'inl_498 ::
  T_InlValid_458 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_498 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InrValid
d_InrValid_514 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InrValid_514
  = C_constructor_556 AgdaAny
                      MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                      T_ValidAt_218
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.b
d_b_542 :: T_InrValid_514 -> AgdaAny
d_b_542 v0
  = case coe v0 of
      C_constructor_556 v1 v2 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-loc
d_payload'45'loc_544 ::
  T_InrValid_514 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_544 v0
  = case coe v0 of
      C_constructor_556 v1 v2 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-ptr
d_payload'45'ptr_546 ::
  T_InrValid_514 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_546 = erased
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-before
d_payload'45'before_548 ::
  T_InrValid_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_payload'45'before_548 v0
  = case coe v0 of
      C_constructor_556 v1 v2 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.sucLoc-before
d_sucLoc'45'before_550 ::
  T_InrValid_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_550 v0
  = case coe v0 of
      C_constructor_556 v1 v2 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.payload-valid
d_payload'45'valid_552 :: T_InrValid_514 -> T_ValidAt_218
d_payload'45'valid_552 v0
  = case coe v0 of
      C_constructor_556 v1 v2 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.InrValid.v-is-inr
d_v'45'is'45'inr_554 ::
  T_InrValid_514 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_554 = erased
-- Once.CCC.Machine.Validity.ValidityDef.decomposePair
d_decomposePair_570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAt_218 -> T_PairValid_310
d_decomposePair_570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_decomposePair_570 v8
du_decomposePair_570 :: T_ValidAt_218 -> T_PairValid_310
du_decomposePair_570 v0
  = case coe v0 of
      C_valid'45'pair_244 v6 v7 v11 v12 v13 v14 v15
        -> coe C_constructor_360 v6 v7 v11 v12 v13 v14 v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.decomposeClosure
d_decomposeClosure_602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAt_218 -> T_ClosureValid_374
d_decomposeClosure_602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_decomposeClosure_602 v8
du_decomposeClosure_602 :: T_ValidAt_218 -> T_ClosureValid_374
du_decomposeClosure_602 v0
  = case coe v0 of
      C_valid'45'closure_296 v1 v4 v5 v6 v8 v9 v13 v14 v15 v16
        -> coe C_constructor_444 v1 v4 v5 v6 v8 v9 v13 v14 v15 v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.decomposeInl
d_decomposeInl_640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAt_218 -> T_InlValid_458
d_decomposeInl_640 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_decomposeInl_640 v5 v8
du_decomposeInl_640 :: AgdaAny -> T_ValidAt_218 -> T_InlValid_458
du_decomposeInl_640 v0 v1
  = case coe v1 of
      C_valid'45'inl_258 v6 v9 v10 v11
        -> coe C_constructor_500 v0 v6 v9 v10 v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.decomposeInr
d_decomposeInr_670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAt_218 -> T_InrValid_514
d_decomposeInr_670 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_decomposeInr_670 v5 v8
du_decomposeInr_670 :: AgdaAny -> T_ValidAt_218 -> T_InrValid_514
du_decomposeInr_670 v0 v1
  = case coe v1 of
      C_valid'45'inr_272 v6 v9 v10 v11
        -> coe C_constructor_556 v0 v6 v9 v10 v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef.composePair
d_composePair_706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218 -> T_ValidAt_218
d_composePair_706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11
                  ~v12 v13 v14 v15 v16 v17
  = du_composePair_706 v8 v9 v13 v14 v15 v16 v17
du_composePair_706 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218 -> T_ValidAt_218
du_composePair_706 v0 v1 v2 v3 v4 v5 v6
  = coe C_valid'45'pair_244 v0 v1 v2 v3 v4 v5 v6
-- Once.CCC.Machine.Validity.ValidityDef.composeClosure
d_composeClosure_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218
d_composeClosure_758 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 ~v9 v10 v11
                     ~v12 ~v13 ~v14 v15 v16 v17 v18
  = du_composeClosure_758 v3 v6 v7 v8 v10 v11 v15 v16 v17 v18
du_composeClosure_758 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218
du_composeClosure_758 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe C_valid'45'closure_296 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
-- Once.CCC.Machine.Validity.ValidityDef.composeInl
d_composeInl_800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218
d_composeInl_800 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 v12
  = du_composeInl_800 v7 v10 v11 v12
du_composeInl_800 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218
du_composeInl_800 v0 v1 v2 v3 = coe C_valid'45'inl_258 v0 v1 v2 v3
-- Once.CCC.Machine.Validity.ValidityDef.composeInr
d_composeInr_832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218
d_composeInr_832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 v12
  = du_composeInr_832 v7 v10 v11 v12
du_composeInr_832 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218
du_composeInr_832 v0 v1 v2 v3 = coe C_valid'45'inr_272 v0 v1 v2 v3
-- Once.CCC.Machine.Validity.ValidityDef._.readLoc-stack-heap-eq
d_readLoc'45'stack'45'heap'45'eq_852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stack'45'heap'45'eq_852 = erased
-- Once.CCC.Machine.Validity.ValidityDef.validity-mem-only
d_validity'45'mem'45'only_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ValidAt_218 -> T_ValidAt_218
d_validity'45'mem'45'only_866 v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 ~v9 v10
  = du_validity'45'mem'45'only_866 v0 v1 v2 v3 v4 v6 v7 v10
du_validity'45'mem'45'only_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAt_218 -> T_ValidAt_218
du_validity'45'mem'45'only_866 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v4) (coe seq (coe v7) (coe C_valid'45'unit_226))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v7 of
                    C_valid'45'pair_244 v17 v18 v22 v23 v24 v25 v26
                      -> coe
                           C_valid'45'pair_244 v17 v18 v22 v23 v24
                           (coe
                              du_fv''_926 (coe v0) (coe v1) (coe v2) (coe v8) (coe v10) (coe v5)
                              (coe v6) (coe v17) (coe v25))
                           (coe
                              du_sv''_928 (coe v0) (coe v1) (coe v2) (coe v9) (coe v11) (coe v5)
                              (coe v6) (coe v18) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
        -> case coe v7 of
             C_valid'45'inl_258 v14 v17 v18 v19
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                      -> coe
                           C_valid'45'inl_258 v14 v17 v18
                           (coe
                              du_pv''_1016 (coe v0) (coe v1) (coe v2) (coe v8) (coe v5) (coe v6)
                              (coe v20) (coe v14) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr_272 v14 v17 v18 v19
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                      -> coe
                           C_valid'45'inr_272 v14 v17 v18
                           (coe
                              du_pv''_1052 (coe v0) (coe v1) (coe v2) (coe v9) (coe v5) (coe v6)
                              (coe v20) (coe v14) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
        -> case coe v7 of
             C_valid'45'closure_296 v10 v13 v14 v15 v17 v18 v22 v23 v24 v25
               -> coe
                    C_valid'45'closure_296 v10 v13 v14 v15 v17 v18 v22 v23 v24
                    (coe
                       du_ev''_980 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6) (coe v10)
                       (coe v14) (coe v17) (coe v25))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Validity.ValidityDef._.fp'
d_fp''_922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 ->
  T_ValidAt_218 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_922 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.sp'
d_sp''_924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 ->
  T_ValidAt_218 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_924 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.fv'
d_fv''_926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218 -> T_ValidAt_218
d_fv''_926 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13 ~v14
           ~v15 ~v16 ~v17 ~v18 v19 ~v20
  = du_fv''_926 v0 v1 v2 v3 v5 v8 v9 v12 v19
du_fv''_926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_218 -> T_ValidAt_218
du_fv''_926 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_866 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.sv'
d_sv''_928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218 -> T_ValidAt_218
d_sv''_928 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 ~v12 v13 ~v14
           ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_sv''_928 v0 v1 v2 v4 v6 v8 v9 v13 v20
du_sv''_928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_218 -> T_ValidAt_218
du_sv''_928 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_866 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.ep'
d_ep''_976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_976 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.cp'
d_cp''_978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_978 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.ev'
d_ev''_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218
d_ev''_980 v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 ~v11 v12 ~v13 v14
           ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_ev''_980 v0 v1 v2 v6 v7 v10 v12 v14 v21
du_ev''_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_218 -> T_ValidAt_218
du_ev''_980 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_866 (coe v0) (coe v1) (coe v2) (coe v5)
      (coe v6) (coe v3) (coe v4) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.pp'
d_pp''_1014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_1014 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.pv'
d_pv''_1016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218
d_pv''_1016 v0 v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13
            ~v14 v15
  = du_pv''_1016 v0 v1 v2 v3 v6 v7 v10 v11 v15
du_pv''_1016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_218 -> T_ValidAt_218
du_pv''_1016 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_866 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v6) (coe v4) (coe v5) (coe v8)
-- Once.CCC.Machine.Validity.ValidityDef._.pp'
d_pp''_1050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_1050 = erased
-- Once.CCC.Machine.Validity.ValidityDef._.pv'
d_pv''_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAt_218 -> T_ValidAt_218
d_pv''_1052 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13
            ~v14 v15
  = du_pv''_1052 v0 v1 v2 v4 v6 v7 v10 v11 v15
du_pv''_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAt_218 -> T_ValidAt_218
du_pv''_1052 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validity'45'mem'45'only_866 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v6) (coe v4) (coe v5) (coe v8)
