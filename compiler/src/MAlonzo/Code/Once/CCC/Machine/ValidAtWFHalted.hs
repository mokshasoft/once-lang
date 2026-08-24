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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor

-- Once.CCC.Machine.ValidAtWFHalted._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_64 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ValidAtWFHalted._._.ValidAtWF
d_ValidAtWF_644 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ValidAtWFHalted._._.readLoc
d_readLoc_1166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1166 ~v0 ~v1 ~v2 = du_readLoc_1166
du_readLoc_1166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1166
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Machine.ValidAtWFHalted._.rl
d_rl_1178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rl_1178 = erased
-- Once.CCC.Machine.ValidAtWFHalted._.validAtWF-set-halted
d_validAtWF'45'set'45'halted_1200 ::
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
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_546 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_546
d_validAtWF'45'set'45'halted_1200 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8
                                  ~v9 v10
  = du_validAtWF'45'set'45'halted_1200 v1 v5 v6 v10
du_validAtWF'45'set'45'halted_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_546 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_546
du_validAtWF'45'set'45'halted_1200 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_782
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_782
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_808 v11 v12 v14 v15 v16 v19 v20 v21 v22 v23
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v24 v25
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                      -> coe
                           MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_808
                           v11 v12 v14 v15 v16 v19 v20 v21
                           (coe
                              du_validAtWF'45'set'45'halted_1200 (coe v0) (coe v24) (coe v26)
                              (coe v22))
                           (coe
                              du_validAtWF'45'set'45'halted_1200 (coe v0) (coe v25) (coe v27)
                              (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'wf_838 v5 v8 v9 v11 v13 v15 v16 v17 v20 v21 v22 v23
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'wf_838
             v5 v8 v9 v11 v13 v15 v16 v17 v20 v21
             (coe
                du_validAtWF'45'set'45'halted_1200 (coe v0) (coe v5) (coe v9)
                (coe v22))
             v23
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'wf_858 v10 v12 v13 v16 v17 v18
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v19 v20
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                      -> coe
                           MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'wf_858
                           v10 v12 v13 v16 v17
                           (coe
                              du_validAtWF'45'set'45'halted_1200 (coe v0) (coe v19) (coe v21)
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'wf_878 v10 v12 v13 v16 v17 v18
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v19 v20
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                      -> coe
                           MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'wf_878
                           v10 v12 v13 v16 v17
                           (coe
                              du_validAtWF'45'set'45'halted_1200 (coe v0) (coe v20) (coe v21)
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_894 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_894
                    v9
                    (coe
                       du_validAtWF'45'set'45'halted_1200 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v1))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval_24 v0 v1
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v1))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v9) v2)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'wf_910 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'wf_910
                    v9
                    (coe
                       du_validAtWF'45'set'45'halted_1200 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v1))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval_24 v0 v1
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v1))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v9) v2)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'int'45'wf_922 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'int'45'wf_922
             v9
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'float'45'wf_934 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'float'45'wf_934
             v9
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'str'45'wf_946 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'str'45'wf_946
             v9
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'buffer'45'wf_958 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'buffer'45'wf_958
             v9
      _ -> MAlonzo.RTE.mazUnreachableError
