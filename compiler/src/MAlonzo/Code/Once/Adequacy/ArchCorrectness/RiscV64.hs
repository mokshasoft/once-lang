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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.Compile
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ArchCorrectness.RiscV64.program-bound
d_program'45'bound_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.RiscV64.program-bound"
-- Once.Adequacy.ArchCorrectness.RiscV64._.IRObsCorrectF
d_IRObsCorrectF_12 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_12 = erased
-- Once.Adequacy.ArchCorrectness.RiscV64._.ir-obs-correct
d_ir'45'obs'45'correct_14 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_522 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.T_MachineRefinesObsF_250
d_ir'45'obs'45'correct_14
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_340
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_302)
      (coe d_program'45'bound_8)
-- Once.Adequacy.ArchCorrectness.RiscV64.riscv64-flat-from-obs
d_riscv64'45'flat'45'from'45'obs_22
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ArchCorrectness.RiscV64.riscv64-flat-from-obs"
-- Once.Adequacy.ArchCorrectness.RiscV64.riscv64-correct
d_riscv64'45'correct_24 ::
  MAlonzo.Code.Once.Adequacy.Compile.T_ArchCorrect_46
d_riscv64'45'correct_24
  = coe
      d_riscv64'45'flat'45'from'45'obs_22
      (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat.d_ir'45'obs'45'correct_340
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation.d_rv64'45'frame'45'semantics_302)
         (coe d_program'45'bound_8))
