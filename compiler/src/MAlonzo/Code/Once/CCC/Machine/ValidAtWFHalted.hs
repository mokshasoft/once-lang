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

module MAlonzo.Code.Once.CCC.Machine.ValidAtWFHalted where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor

-- Once.CCC.Machine.ValidAtWFHalted._.ClosureWellFormedDef.CellAt
d_CellAt_20 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ValidAtWFHalted._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_82 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ValidAtWFHalted._._.CellAt
d_CellAt_666 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ValidAtWFHalted._._.ValidAtWF
d_ValidAtWF_728 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ValidAtWFHalted._._.readLoc
d_readLoc_1298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1298 ~v0 ~v1 ~v2 = du_readLoc_1298
du_readLoc_1298 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1298
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Machine.ValidAtWFHalted._.rl
d_rl_1310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rl_1310 = erased
-- Once.CCC.Machine.ValidAtWFHalted._.validAtWF-set-halted
d_validAtWF'45'set'45'halted_1332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
d_validAtWF'45'set'45'halted_1332 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 v9
                                  v10
  = du_validAtWF'45'set'45'halted_1332 v0 v1 v2 v4 v5 v6 v8 v9 v10
du_validAtWF'45'set'45'halted_1332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
du_validAtWF'45'set'45'halted_1332 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_810
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_810
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_828 v17 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                      -> coe
                           MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_828
                           v17 v18
                           (coe
                              du_cellAt'45'set'45'halted_1346 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe v21) (coe v23) (coe v6) (coe v7) (coe v19))
                           (coe
                              du_cellAt'45'set'45'halted_1346 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe v22) (coe v24) (coe v6) (coe v7) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'wf_854 v9 v12 v13 v16 v18 v19 v20 v23 v24 v25
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'wf_854
             v9 v12 v13 v16 v18 v19 v20 v23 v24
             (coe
                du_validAtWF'45'set'45'halted_1332 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v9) (coe v13) (coe v6) (coe v7) (coe v25))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'reg'45'wf_878 v9 v12 v13 v17 v18 v19 v22
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'reg'45'wf_878
             v9 v12 v13 v17 v18 v19 v22
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'susp'45'wf_898 v10 v11 v12 v13 v17 v18 v19 v21
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'susp'45'wf_898
             v10 v11 v12 v13 v17 v18
             (coe
                du_cellAt'45'set'45'halted_1346 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v10) (coe v13) (coe v6) (coe v7) (coe v19))
             v21
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'wf_918 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'wf_918
                           v15 v17 v18 v21 v22
                           (coe
                              du_validAtWF'45'set'45'halted_1332 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v24) (coe v26) (coe v6) (coe v7) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'wf_938 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'wf_938
                           v15 v17 v18 v21 v22
                           (coe
                              du_validAtWF'45'set'45'halted_1332 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v25) (coe v26) (coe v6) (coe v7) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'reg'45'wf_956 v16 v18 v20
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'reg'45'wf_956
             v16 v18 v20
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'reg'45'wf_974 v16 v18 v20
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'reg'45'wf_974
             v16 v18 v20
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_990 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v17
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_990
                    v14
                    (coe
                       du_validAtWF'45'set'45'halted_1332 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v17) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval'7472'_30 v1
                             v4
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v17) (coe v4))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v14) v5)
                          (coe (0 :: Integer)))
                       (coe v6) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'int'45'wf_1002 v14
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'int'45'wf_1002
             v14
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'float'45'wf_1014 v14
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'float'45'wf_1014
             v14
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'str'45'wf_1026 v14
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'str'45'wf_1026
             v14
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'buffer'45'wf_1038 v14
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'buffer'45'wf_1038
             v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ValidAtWFHalted._.cellAt-set-halted
d_cellAt'45'set'45'halted_1346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586
d_cellAt'45'set'45'halted_1346 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_cellAt'45'set'45'halted_1346 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_cellAt'45'set'45'halted_1346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586
du_cellAt'45'set'45'halted_1346 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_788 v12 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_788
             v12 v14 v16
             (coe
                du_validAtWF'45'set'45'halted_1332 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v17))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_800 v13
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_800
             v13
      _ -> MAlonzo.RTE.mazUnreachableError
