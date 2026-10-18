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

module MAlonzo.Code.Once.Adequacy.ImageUnique where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.ListAction
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Membership.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.LabelSymbols
import qualified MAlonzo.Code.Once.Adequacy.NameClash
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.ImageSymbols
import qualified MAlonzo.Code.Once.CCC.Codegen.LabelDefs
import qualified MAlonzo.Code.Once.CCC.Codegen.LabelRange
import qualified MAlonzo.Code.Once.CCC.Codegen.ProgramImage
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolInjective
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties

-- Once.Adequacy.ImageUnique.ilab
d_ilab_6 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28]
d_ilab_6 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v3 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.CCC.Label.C_callee_34 (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                _ -> coe v1
         _ -> coe v1)
-- Once.Adequacy.ImageUnique.dlabs
d_dlabs_12 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28]
d_dlabs_12 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ilab_6 (coe v1)) (coe d_dlabs_12 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.lefts
d_lefts_18 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] -> [Integer]
d_lefts_18 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                    (coe d_lefts_18 (coe v2))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe d_lefts_18 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.rights
d_rights_26 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_rights_26 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe d_rights_26 (coe v2)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                    (coe d_rights_26 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.lefts-++
d_lefts'45''43''43'_38 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lefts'45''43''43'_38 = erased
-- Once.Adequacy.ImageUnique.rights-++
d_rights'45''43''43'_58 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rights'45''43''43'_58 = erased
-- Once.Adequacy.ImageUnique.idefs
d_idefs_76 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idefs_76 = erased
-- Once.Adequacy.ImageUnique.idefl
d_idefl_86 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_idefl_86 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2260
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2266
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2268
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2270 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2272 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2274 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2276 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2278 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2280 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2282
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2284
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2286 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2288 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2290 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2292 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2298 v1 v2 v3
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2304 v1 v2 v3
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2306 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2308
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2310 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2312 v1 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2314 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2316 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2318 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v2
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe MAlonzo.Code.Once.Adequacy.LabelSymbols.C_d'45'once_22)
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v2 v3
               -> coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Once.Adequacy.LabelSymbols.C_d'45'callee_26)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2244
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2322 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.ileft
d_ileft_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ileft_96 = erased
-- Once.Adequacy.ImageUnique.iright
d_iright_106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iright_106 = erased
-- Once.Adequacy.ImageUnique.adefs-labs
d_adefs'45'labs_116 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_adefs'45'labs_116 = erased
-- Once.Adequacy.ImageUnique.dlabs-def
d_dlabs'45'def_124 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dlabs'45'def_124 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe d_ilab_6 (coe v1)) (coe d_idefl_86 (coe v1))
             (coe d_dlabs'45'def_124 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.cl-at-++
d_cl'45'at'45''43''43'_134 ::
  Maybe Integer ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cl'45'at'45''43''43'_134 = erased
-- Once.Adequacy.ImageUnique.keys-lefts
d_keys'45'lefts_144 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keys'45'lefts_144 = erased
-- Once.Adequacy.ImageUnique.keys-rights
d_keys'45'rights_152 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keys'45'rights_152 = erased
-- Once.Adequacy.ImageUnique.lr-dst
d_lr'45'dst_160 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_lr'45'dst_160 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v8 v9
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                           (coe du_fresh'8321'_182 (coe v4) (coe v8))
                           (d_lr'45'dst_160 (coe v4) (coe v9) (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v8 v9
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                           (coe du_fresh'8322'_228 (coe v4) (coe v8))
                           (d_lr'45'dst_160 (coe v4) (coe v1) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.fresh₁
d_fresh'8321'_182 ::
  Integer ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fresh'8321'_182 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_fresh'8321'_182 v5 v6
du_fresh'8321'_182 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fresh'8321'_182 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (\ v9 -> coe v7 erased) (coe du_fresh'8321'_182 (coe v3) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                    (coe du_fresh'8321'_182 (coe v3) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._._.inj₁-inj
d_inj'8321''45'inj_200 ::
  Integer ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  Integer ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'8321''45'inj_200 = erased
-- Once.Adequacy.ImageUnique._.fresh₂
d_fresh'8322'_228 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fresh'8322'_228 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_fresh'8322'_228 v5 v6
du_fresh'8322'_228 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fresh'8322'_228 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                    (coe du_fresh'8322'_228 (coe v3) (coe v1))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (\ v9 -> coe v7 erased) (coe du_fresh'8322'_228 (coe v3) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._._.inj₂-inj
d_inj'8322''45'inj_250 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'8322''45'inj_250 = erased
-- Once.Adequacy.ImageUnique.adefs-unique
d_adefs'45'unique_256 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_adefs'45'unique_256 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Properties.du_map'8314'_44
      (coe d_dlabs_12 (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.LabelSymbols.d_keys'8594'syms_306
         (coe d_dlabs_12 (coe v0)) (coe d_dlabs'45'def_124 (coe v0))
         (coe
            du_AP'45'map'8315'_274 (coe d_dlabs_12 (coe v0))
            (coe
               d_lr'45'dst_160
               (coe
                  MAlonzo.Code.Data.List.Base.du_map_22
                  (coe MAlonzo.Code.Once.Adequacy.LabelSymbols.d_key_6)
                  (coe d_dlabs_12 (coe v0)))
               (coe v1) (coe v2))))
-- Once.Adequacy.ImageUnique._.AP-map⁻
d_AP'45'map'8315'_274 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_AP'45'map'8315'_274 ~v0 ~v1 ~v2 v3 v4
  = du_AP'45'map'8315'_274 v3 v4
du_AP'45'map'8315'_274 ::
  [MAlonzo.Code.Once.CCC.Label.T_Label_28] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_AP'45'map'8315'_274 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                    (coe du_all'45'map'8315'_294 (coe v3) (coe v6))
                    (coe du_AP'45'map'8315'_274 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._._.all-map⁻
d_all'45'map'8315'_294 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'map'8315'_294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_all'45'map'8315'_294 v7 v8
du_all'45'map'8315'_294 ::
  [MAlonzo.Code.Once.CCC.Label.T_Label_28] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'map'8315'_294 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6
                    (coe du_all'45'map'8315'_294 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.fns-end
d_fns'45'end_304 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> Integer
d_fns'45'end_304 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             d_fns'45'end_304
             (coe
                MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                (coe v2))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.unit-cl
d_unit'45'cl_318 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unit'45'cl_318 = erased
-- Once.Adequacy.ImageUnique.unit-nf
d_unit'45'nf_328 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unit'45'nf_328 = erased
-- Once.Adequacy.ImageUnique.fns-end-≥
d_fns'45'end'45''8805'_340 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fns'45'end'45''8805'_340 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Once.CCC.Codegen.LabelRange.d_label'45'mono_160
                (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                (coe (0 :: Integer)) (coe v0))
             (coe
                d_fns'45'end'45''8805'_340
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                   (coe v2))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.fns-cl
d_fns'45'cl_354 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fns'45'cl_354 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_dst'45''43''43'_78
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_600
                      (coe du_o_368 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                      (coe (0 :: Integer)) (coe v0))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_602
                      (coe du_o_368 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                      (coe (0 :: Integer)) (coe v0)))
                (coe du_dU_372 (coe v0) (coe v2))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_rest_376 (coe v0) (coe v2) (coe v3)))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_dj'45'win_118
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_600
                         (coe du_o_368 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                         (coe (0 :: Integer)) (coe v0))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_602
                         (coe du_o_368 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                         (coe (0 :: Integer)) (coe v0)))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_clabs_208
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                            (coe v2))
                         (coe v3)))
                   (coe du_wU_374 (coe v0) (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe d_rest_376 (coe v0) (coe v2) (coe v3)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_600
                      (coe du_o_368 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                      (coe (0 :: Integer)) (coe v0))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_602
                      (coe du_o_368 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                      (coe (0 :: Integer)) (coe v0)))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_win'45'weaken_146
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_600
                         (coe du_o_368 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                         (coe (0 :: Integer)) (coe v0))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_602
                         (coe du_o_368 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                         (coe (0 :: Integer)) (coe v0)))
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
                   (d_fns'45'end'45''8805'_340
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                         (coe v2))
                      (coe v3))
                   (coe du_wU_374 (coe v0) (coe v2)))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_win'45'weaken_146
                   (MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_clabs_208
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                            (coe v2))
                         (coe v3)))
                   (MAlonzo.Code.Once.CCC.Codegen.LabelRange.d_label'45'mono_160
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                      (coe (0 :: Integer)) (coe v0))
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe
                         d_fns'45'end_304
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                            (coe v2))
                         (coe v3)))
                   (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe d_rest_376 (coe v0) (coe v2) (coe v3)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.o
d_o_368 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_o_368 ~v0 v1 ~v2 = du_o_368 v1
du_o_368 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
du_o_368 v0
  = coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v0)
-- Once.Adequacy.ImageUnique._.F
d_F_370 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_F_370 v0 v1 ~v2 = du_F_370 v0 v1
du_F_370 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_F_370 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_frag_1404
      (coe du_o_368 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))
      (coe (0 :: Integer)) (coe v0)
-- Once.Adequacy.ImageUnique._.dU
d_dU_372 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dU_372 v0 v1 ~v2 = du_dU_372 v0 v1
du_dU_372 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_dU_372 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_frag'45'dst_1688
      (coe du_o_368 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))
      (coe (0 :: Integer)) (coe v0)
-- Once.Adequacy.ImageUnique._.wU
d_wU_374 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wU_374 v0 v1 ~v2 = du_wU_374 v0 v1
du_wU_374 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_wU_374 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_600
         (coe du_o_368 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))
         (coe (0 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_F_370 (coe v0) (coe v1))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_F_370 (coe v0) (coe v1))))
-- Once.Adequacy.ImageUnique._.rest
d_rest_376 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rest_376 v0 v1 v2
  = coe
      d_fns'45'cl_354
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
         (coe v1))
      (coe v2)
-- Once.Adequacy.ImageUnique._.eq
d_eq_378 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq_378 = erased
-- Once.Adequacy.ImageUnique.fns-fdefs
d_fns'45'fdefs_388 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fns'45'fdefs_388 = erased
-- Once.Adequacy.ImageUnique._.fdefs-++
d_fdefs'45''43''43'_406 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fdefs'45''43''43'_406 = erased
-- Once.Adequacy.ImageUnique.image-cl
d_image'45'cl_426 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_image'45'cl_426 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_dst'45''43''43'_78
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe d_TL_452 (coe v0) (coe v1)) (coe d_BL_454 (coe v0) (coe v1)))
      (d_dM_456 (coe v0) (coe v1))
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_FS_460 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_dj'45'win_118
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe d_TL_452 (coe v0) (coe v1)) (coe d_BL_454 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_clabs_208
            (coe
               MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
               (coe addInt (coe (1 :: Integer)) (coe d_nM_438 (coe v0) (coe v1)))
               (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v1))))
         (coe d_wM_458 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_FS_460 (coe v0) (coe v1))))
-- Once.Adequacy.ImageUnique._.X
d_X_436 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_X_436 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
-- Once.Adequacy.ImageUnique._.nM
d_nM_438 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 -> Integer
d_nM_438 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelRange.du_label'45'of_42
      (coe d_X_436 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.F
d_F_440 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_F_440 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_frag_1404 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Adequacy.ImageUnique._.wT
d_wT_448 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wT_448 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_F_440 (coe v0) (coe v1)))
-- Once.Adequacy.ImageUnique._.wB
d_wB_450 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wB_450 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_F_440 (coe v0) (coe v1)))
-- Once.Adequacy.ImageUnique._.TL
d_TL_452 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 -> [Integer]
d_TL_452 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_600 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Adequacy.ImageUnique._.BL
d_BL_454 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 -> [Integer]
d_BL_454 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_602 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Adequacy.ImageUnique._.dM
d_dM_456 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dM_456 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_frag'45'dst_1688
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Adequacy.ImageUnique._.wM
d_wM_458 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wM_458 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_600 (coe v0)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
         (coe (0 :: Integer)) (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_win'45'weaken_146
         (MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_600
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
            (coe (0 :: Integer)) (coe (0 :: Integer)))
         (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
            (coe (0 :: Integer)))
         (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe d_nM_438 (coe v0) (coe v1)))
         (d_wT_448 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_win'45'weaken_146
         (MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_602
            (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
            (coe (0 :: Integer)) (coe (0 :: Integer)))
         (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
            (coe (0 :: Integer)))
         (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe d_nM_438 (coe v0) (coe v1)))
         (d_wB_450 (coe v0) (coe v1)))
-- Once.Adequacy.ImageUnique._.FS
d_FS_460 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_FS_460 v0 v1
  = coe
      d_fns'45'cl_354
      (coe addInt (coe (1 :: Integer)) (coe d_nM_438 (coe v0) (coe v1)))
      (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v1))
-- Once.Adequacy.ImageUnique._.eq
d_eq_462 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq_462 = erased
-- Once.Adequacy.ImageUnique.image-fdefs
d_image'45'fdefs_470 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_image'45'fdefs_470 = erased
-- Once.Adequacy.ImageUnique._.X
d_X_480 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_X_480 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
-- Once.Adequacy.ImageUnique._._∙_
d__'8729'__488 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d__'8729'__488 = erased
-- Once.Adequacy.ImageUnique._.fdefs-++′
d_fdefs'45''43''43''8242'_494 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fdefs'45''43''43''8242'_494 = erased
-- Once.Adequacy.ImageUnique.TableNames
d_TableNames_510 a0 = ()
data T_TableNames_510
  = C_constructor_534 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
                      MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.Adequacy.ImageUnique.TableNames.names
d_names_524 ::
  T_TableNames_510 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_names_524 v0
  = case coe v0 of
      C_constructor_534 v1 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.TableNames.syms≡
d_syms'8801'_528 ::
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_syms'8801'_528 = erased
-- Once.Adequacy.ImageUnique.TableNames.dist
d_dist_530 ::
  T_TableNames_510 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dist_530 v0
  = case coe v0 of
      C_constructor_534 v1 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.TableNames.valid
d_valid_532 ::
  T_TableNames_510 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_valid_532 v0
  = case coe v0 of
      C_constructor_534 v1 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.sym-of
d_sym'45'of_536 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_sym'45'of_536 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v0))
-- Once.Adequacy.ImageUnique.tbl-go
d_tbl'45'go_544 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_238] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tbl'45'go_544 = erased
-- Once.Adequacy.ImageUnique.no-names
d_no'45'names_556 :: T_TableNames_510
d_no'45'names_556
  = coe
      C_constructor_534
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
-- Once.Adequacy.ImageUnique.table-names
d_table'45'names_560 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  T_TableNames_510
d_table'45'names_560 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38 v1
        -> let v2
                 = MAlonzo.Code.Once.Parser.d_guardDistinct_538
                     (coe
                        MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                        (coe v1) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
                  -> coe d_no'45'names_556
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> let v4
                           = MAlonzo.Code.Once.Compile.d_compileEntries_460
                               (coe MAlonzo.Code.Once.IR.C_Heap_8)
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                               (coe MAlonzo.Code.Once.Compile.d_emptyCScope_388) (coe v3) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
                            -> coe d_no'45'names_556
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                            -> coe
                                 C_constructor_534
                                 (MAlonzo.Code.Once.Parser.d_emittedNames_522
                                    (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3)))
                                 (MAlonzo.Code.Once.Adequacy.NameClash.d_map'45'allpairs'45'own_110
                                    (coe
                                       MAlonzo.Code.Once.Parser.d_emittedNames_522
                                       (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3)))
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.NameClash.du_namesDistinct'45'sound_68
                                       (coe
                                          MAlonzo.Code.Once.Parser.d_emittedNames_522
                                          (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3))))
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.NameClash.du_allValidIdentB'45'sound_58
                                       (coe
                                          MAlonzo.Code.Once.Parser.d_emittedNames_522
                                          (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3)))))
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.NameClash.du_allValidIdentB'45'sound_58
                                    (coe
                                       MAlonzo.Code.Once.Parser.d_emittedNames_522
                                       (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3))))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.guard
d_guard_596 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guard_596 = erased
-- Once.Adequacy.ImageUnique.ap-reverse
d_ap'45'reverse_600 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_ap'45'reverse_600 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Properties.du_'43''43''8314'_74
                    (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v3)
                    (coe d_ap'45'reverse_600 (coe v3) (coe v7))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22))
                    (coe
                       du_rev'45'all_622 (coe v3)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                          (coe (\ v8 v9 v10 -> coe v9 erased)) (coe v3) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.rev-all
d_rev'45'all_622 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rev'45'all_622 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_rev'45'all_622 v4 v5
du_rev'45'all_622 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rev'45'all_622 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266
      (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0)
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
           (coe
              MAlonzo.Code.Data.List.Relation.Unary.All.du_lookup_436 v0 v1
              (coe du_rev'45''8712'_634 v0 v3))
           (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
-- Once.Adequacy.ImageUnique._._.rev-∈
d_rev'45''8712'_634 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_rev'45''8712'_634 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_rev'45''8712'_634 v4
du_rev'45''8712'_634 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_rev'45''8712'_634 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_reverse'8315'_2018
      (coe v0)
-- Once.Adequacy.ImageUnique.hd
d_hd_646 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_hd_646 v0
  = case coe v0 of
      [] -> coe ' '
      (:) v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.shd
d_shd_650 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_shd_650 v0
  = coe
      d_hd_646
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Adequacy.ImageUnique.once-hd
d_once'45'hd_656 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_once'45'hd_656 = erased
-- Once.Adequacy.ImageUnique.thunk-hd
d_thunk'45'hd_662 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thunk'45'hd_662 = erased
-- Once.Adequacy.ImageUnique.osp-hd
d_osp'45'hd_668 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_osp'45'hd_668 = erased
-- Once.Adequacy.ImageUnique.hd≢
d_hd'8802'_680 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_hd'8802'_680 = erased
-- Once.Adequacy.ImageUnique.heap≢osp
d_heap'8802'osp_690 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'osp_690 = erased
-- Once.Adequacy.ImageUnique.own≢block
d_own'8802'block_696 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_own'8802'block_696 = erased
-- Once.Adequacy.ImageUnique._.bn
d_bn_710 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_bn_710 ~v0 v1 ~v2 ~v3 = du_bn_710 v1
du_bn_710 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_bn_710 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("arith.block." :: Data.Text.Text) v0
-- Once.Adequacy.ImageUnique._.∷-inj
d_'8759''45'inj_720 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''45'inj_720 = erased
-- Once.Adequacy.ImageUnique._.sym-shape
d_sym'45'shape_724 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym'45'shape_724 = erased
-- Once.Adequacy.ImageUnique._.body≡
d_body'8801'_738 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'8801'_738 = erased
-- Once.Adequacy.ImageUnique._.hnd-x
d_hnd'45'x_740 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_hnd'45'x_740 v0 ~v1 v2 ~v3 = du_hnd'45'x_740 v0 v2
du_hnd'45'x_740 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
du_hnd'45'x_740 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.Target.SymbolInjective.d_zencL'45'vic_656
               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
               (coe v1))))
-- Once.Adequacy.ImageUnique._.bn-chars
d_bn'45'chars_750 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bn'45'chars_750 = erased
-- Once.Adequacy.ImageUnique._.hnd-bn
d_hnd'45'bn_752 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_hnd'45'bn_752 = erased
-- Once.Adequacy.ImageUnique._.tl≡
d_tl'8801'_756 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tl'8801'_756 = erased
-- Once.Adequacy.ImageUnique._.Lx
d_Lx_758 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_Lx_758 v0 ~v1 ~v2 ~v3 = du_Lx_758 v0
du_Lx_758 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
du_Lx_758 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe
         MAlonzo.Code.Once.Target.SymbolInjective.d_zencL_142
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
-- Once.Adequacy.ImageUnique._.Lb
d_Lb_760 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_Lb_760 ~v0 v1 ~v2 ~v3 = du_Lb_760 v1
du_Lb_760 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
du_Lb_760 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe
         MAlonzo.Code.Once.Target.SymbolInjective.d_zencL_142
         (coe
            MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
            (coe du_bn_710 (coe v0))))
-- Once.Adequacy.ImageUnique._.not-valid
d_not'45'valid_762 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_not'45'valid_762 = erased
-- Once.Adequacy.ImageUnique._._.dot
d_dot_770 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dot_770 = erased
-- Once.Adequacy.ImageUnique.BlockSym
d_BlockSym_772 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_BlockSym_772 = erased
-- Once.Adequacy.ImageUnique.==-false
d_'61''61''45'false_782 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'61''61''45'false_782 = erased
-- Once.Adequacy.ImageUnique.any-false
d_any'45'false_826 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_any'45'false_826 ~v0 v1 ~v2 = du_any'45'false_826 v1
du_any'45'false_826 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_any'45'false_826 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
             (coe du_any'45'false_826 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.∨-falseˡ
d_'8744''45'false'737'_844 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'false'737'_844 = erased
-- Once.Adequacy.ImageUnique._.∨-falseʳ
d_'8744''45'false'691'_852 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'false'691'_852 = erased
-- Once.Adequacy.ImageUnique.DD
d_DD_856 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_DD_856 = erased
-- Once.Adequacy.ImageUnique.dedup-dd
d_dedup'45'dd_870 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dedup'45'dd_870 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_dedup'45'step_884 (coe v0) (coe v4) (coe v3)
                    (coe
                       MAlonzo.Code.Data.Bool.ListAction.du_any_14
                       (coe
                          (\ v6 ->
                             MAlonzo.Code.Data.String.Properties.d__'61''61'__86
                               (coe v6) (coe v4)))
                       (coe v0))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.dedup-step
d_dedup'45'step_884 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dedup'45'step_884 v0 v1 ~v2 v3 v4 ~v5
  = du_dedup'45'step_884 v0 v1 v3 v4
du_dedup'45'step_884 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dedup'45'step_884 v0 v1 v2 v3
  = if coe v3
      then coe d_dedup'45'dd_870 (coe v0) (coe v2)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                (coe
                   du_head'45'fresh_936
                   (coe
                      MAlonzo.Code.Once.Compile.d_dedup'45'go_912
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                      (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_dedup'45'dd_870
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                         (coe v2))))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_dedup'45'dd_870
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                      (coe v2))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_any'45'false_826 (coe v0))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                   (\ v4 v5 -> coe du_tl_924 v5)
                   (coe
                      MAlonzo.Code.Once.Compile.d_dedup'45'go_912
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                      (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_dedup'45'dd_870
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                         (coe v2)))))
-- Once.Adequacy.ImageUnique._.tl
d_tl_924 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_tl_924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_tl_924 v6
du_tl_924 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_tl_924 v0
  = case coe v0 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v3 v4
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.head-fresh
d_head'45'fresh_936 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_head'45'fresh_936 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_head'45'fresh_936 v5 v6
du_head'45'fresh_936 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_head'45'fresh_936 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v10 v11
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v10
                           (coe du_head'45'fresh_936 (coe v3) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.dedup-⊆
d_dedup'45''8838'_960 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dedup'45''8838'_960 ~v0 v1 v2 v3
  = du_dedup'45''8838'_960 v1 v2 v3
du_dedup'45''8838'_960 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_dedup'45''8838'_960 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v9 v10
                      -> coe
                           du_dedup'45''8838''45'step_978 (coe v0) (coe v5) (coe v4)
                           (coe
                              MAlonzo.Code.Data.List.Base.du_foldr_216
                              (coe MAlonzo.Code.Data.Bool.Base.d__'8744'__30)
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                              (coe
                                 MAlonzo.Code.Data.List.Base.du_map_22
                                 (coe
                                    (\ v11 ->
                                       MAlonzo.Code.Data.String.Properties.d__'61''61'__86
                                         (coe v11) (coe v5)))
                                 (coe v0)))
                           (coe v9) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.dedup-⊆-step
d_dedup'45''8838''45'step_978 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dedup'45''8838''45'step_978 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_dedup'45''8838''45'step_978 v1 v2 v4 v5 v6 v7
du_dedup'45''8838''45'step_978 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_dedup'45''8838''45'step_978 v0 v1 v2 v3 v4 v5
  = if coe v3
      then coe du_dedup'45''8838'_960 (coe v0) (coe v2) (coe v5)
      else coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
             (coe
                du_dedup'45''8838'_960
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                (coe v2) (coe v5))
-- Once.Adequacy.ImageUnique.tag
d_tag_1018 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag_1018 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Compile.d_block'45'symbol_928 (coe v0))
      (coe v0)
-- Once.Adequacy.ImageUnique.tagged
d_tagged_1026 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_tagged_1026 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'digest_180
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'shape_174 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_178 (coe v1)))
                erased)
             (d_tagged_1026 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.fsts
d_fsts_1038 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fsts_1038 ~v0 v1 v2 = du_fsts_1038 v1 v2
du_fsts_1038 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fsts_1038 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6
                    (coe du_fsts_1038 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.blocks-unique
d_blocks'45'unique_1048 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_blocks'45'unique_1048 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         d_dedup'45'dd_870
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22 (coe d_tag_1018) (coe v0)))
-- Once.Adequacy.ImageUnique.blocks-sym
d_blocks'45'sym_1054 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'sym_1054 v0
  = coe
      du_fsts_1038
      (coe
         MAlonzo.Code.Once.Compile.d_dedup'45'blocks_926
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22 (coe d_tag_1018) (coe v0)))
      (coe
         du_dedup'45''8838'_960
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22 (coe d_tag_1018) (coe v0))
         (coe d_tagged_1026 (coe v0)))
-- Once.Adequacy.ImageUnique.rights-∈
d_rights'45''8712'_1062 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_rights'45''8712'_1062 ~v0 v1 v2 = du_rights'45''8712'_1062 v1 v2
du_rights'45''8712'_1062 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_rights'45''8712'_1062 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
                      -> coe du_rights'45''8712'_1062 (coe v3) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v7
                      -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                           (coe du_rights'45''8712'_1062 (coe v3) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.DefClass
d_DefClass_1076 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_DefClass_1076 = erased
-- Once.Adequacy.ImageUnique.adefs-class
d_adefs'45'class_1084 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_adefs'45'class_1084 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_map'8314'_496
      (coe d_dlabs_12 (coe v0))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266
         (d_dlabs_12 (coe v0)) (d_cls_1094 (coe v0)))
-- Once.Adequacy.ImageUnique._.cls
d_cls_1094 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cls_1094 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Label.C_once_30 v3
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.CCC.Label.C_sigop_32 v3 v4
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Label.C_callee_34 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v4
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       du_rights'45''8712'_1062
                       (coe
                          MAlonzo.Code.Data.List.Base.du_map_22
                          (coe MAlonzo.Code.Once.Adequacy.LabelSymbols.d_key_6)
                          (coe d_dlabs_12 (coe v0)))
                       (coe
                          MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'map'8314'_164
                          v1 (d_dlabs_12 (coe v0)) v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._._.no-sigop
d_no'45'sigop_1116 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Adequacy.LabelSymbols.T_DefL_18 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'sigop_1116 = erased
-- Once.Adequacy.ImageUnique.rt-names
d_rt'45'names_1120 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rt'45'names_1120 = erased
-- Once.Adequacy.ImageUnique.Entries._.dist
d_dist_1136 ::
  T_TableNames_510 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dist_1136 v0 = coe d_dist_530 (coe v0)
-- Once.Adequacy.ImageUnique.Entries._.names
d_names_1138 ::
  T_TableNames_510 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_names_1138 v0 = coe d_names_524 (coe v0)
-- Once.Adequacy.ImageUnique.Entries._.syms≡
d_syms'8801'_1140 ::
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_syms'8801'_1140 = erased
-- Once.Adequacy.ImageUnique.Entries._.valid
d_valid_1142 ::
  T_TableNames_510 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_valid_1142 v0 = coe d_valid_532 (coe v0)
-- Once.Adequacy.ImageUnique.Entries.EF
d_EF_1144 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_EF_1144 v0 ~v1 = du_EF_1144 v0
du_EF_1144 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_EF_1144 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v1 -> MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1)))
         (coe MAlonzo.Code.Once.Compile.d_rewrite'45'table_888 (coe v0)))
-- Once.Adequacy.ImageUnique.Entries.EF≡
d_EF'8801'_1146 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_EF'8801'_1146 = erased
-- Once.Adequacy.ImageUnique.Entries.EF-dist
d_EF'45'dist_1148 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_EF'45'dist_1148 ~v0 v1 = du_EF'45'dist_1148 v1
du_EF'45'dist_1148 ::
  T_TableNames_510 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_EF'45'dist_1148 v0
  = coe
      d_ap'45'reverse_600
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_62)
         (coe d_names_524 (coe v0)))
      (coe d_dist_530 (coe v0))
-- Once.Adequacy.ImageUnique.Entries.EF-own
d_EF'45'own_1154 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_EF'45'own_1154 ~v0 v1 ~v2 v3 = du_EF'45'own_1154 v1 v3
du_EF'45'own_1154 ::
  T_TableNames_510 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_EF'45'own_1154 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.List.Membership.Setoid.du_find_86
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
              (coe d_names_524 (coe v0))
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_map'8315'_736
                 (coe d_names_524 (coe v0))
                 (coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_reverse'8315'_2018
                    (coe
                       MAlonzo.Code.Data.List.Base.du_map_22
                       (coe MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_62)
                       (coe d_names_524 (coe v0)))
                    (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.du_lookup_436
                             (d_names_524 (coe v0)) (d_valid_532 (coe v0)) v5)
                          erased)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ImageUnique.Apart._.EF
d_EF_1186 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_EF_1186 ~v0 v1 ~v2 ~v3 = du_EF_1186 v1
du_EF_1186 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_EF_1186 v0 = coe du_EF_1144 (coe v0)
-- Once.Adequacy.ImageUnique.Apart._.EF-dist
d_EF'45'dist_1188 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_EF'45'dist_1188 ~v0 ~v1 v2 ~v3 = du_EF'45'dist_1188 v2
du_EF'45'dist_1188 ::
  T_TableNames_510 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_EF'45'dist_1188 v0 = coe du_EF'45'dist_1148 (coe v0)
-- Once.Adequacy.ImageUnique.Apart._.EF-own
d_EF'45'own_1190 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_EF'45'own_1190 ~v0 ~v1 v2 ~v3 = du_EF'45'own_1190 v2
du_EF'45'own_1190 ::
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_EF'45'own_1190 v0 v1 v2 = coe du_EF'45'own_1154 (coe v0) v2
-- Once.Adequacy.ImageUnique.Apart._.EF≡
d_EF'8801'_1192 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_EF'8801'_1192 = erased
-- Once.Adequacy.ImageUnique.Apart.toEF
d_toEF_1196 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_toEF_1196 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_toEF_1196 v5
du_toEF_1196 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_toEF_1196 v0 = coe v0
-- Once.Adequacy.ImageUnique.Apart.def≢blk
d_def'8802'blk_1204 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_def'8802'blk_1204 = erased
-- Once.Adequacy.ImageUnique.Apart.heap≢def
d_heap'8802'def_1228 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'def_1228 = erased
-- Once.Adequacy.ImageUnique.Apart.heap≢blk
d_heap'8802'blk_1244 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'blk_1244 = erased
-- Once.Adequacy.ImageUnique.Apart.start≢def
d_start'8802'def_1250 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'def_1250 = erased
-- Once.Adequacy.ImageUnique.Apart.start≢blk
d_start'8802'blk_1266 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'blk_1266 = erased
-- Once.Adequacy.ImageUnique.Apart.defs++blocks
d_defs'43''43'blocks_1274 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_defs'43''43'blocks_1274 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_defs'43''43'blocks_1274 v4 v5 v6 v7 v8 v9
du_defs'43''43'blocks_1274 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_defs'43''43'blocks_1274 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Properties.du_'43''43''8314'_74
      (coe v0) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v6 v7 ->
               coe
                 MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
                 (coe v1) (coe v3)))
         (coe v0) (coe v2))
-- Once.Adequacy.ImageUnique.Apart.heap-fresh
d_heap'45'fresh_1298 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_heap'45'fresh_1298 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_heap'45'fresh_1298 v4 v5 v6 v7
du_heap'45'fresh_1298 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_heap'45'fresh_1298 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe v0)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
         (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
         (coe v1) (coe v3))
-- Once.Adequacy.ImageUnique.Apart.start-fresh
d_start'45'fresh_1314 ::
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_start'45'fresh_1314 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_start'45'fresh_1314 v4 v5 v6 v7
du_start'45'fresh_1314 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_start'45'fresh_1314 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe v0)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
         (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
         (coe v1) (coe v3))
-- Once.Adequacy.ImageUnique.prog-unique
d_prog'45'unique_1328 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_prog'45'unique_1328 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
         (coe
            du_heap'45'fresh_1298 (coe d_D_1372 (coe v0) (coe v1))
            (coe d_B_1374 (coe v0) (coe v1)) (coe d_cD_1376 (coe v0) (coe v1))
            (coe d_cB_1378 (coe v0) (coe v1))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
         (coe
            du_start'45'fresh_1314 (coe d_D_1372 (coe v0) (coe v1))
            (coe d_B_1374 (coe v0) (coe v1)) (coe d_cD_1376 (coe v0) (coe v1))
            (coe d_cB_1378 (coe v0) (coe v1)))
         (coe
            du_defs'43''43'blocks_1274 (coe d_D_1372 (coe v0) (coe v1))
            (coe d_B_1374 (coe v0) (coe v1)) (coe d_cD_1376 (coe v0) (coe v1))
            (coe d_cB_1378 (coe v0) (coe v1)) (coe d_uD_1380 (coe v0) (coe v1))
            (coe
               d_blocks'45'unique_1048
               (coe
                  MAlonzo.Code.Once.Compile.d_program'45'blocks_898
                  (coe d_p_1342 (coe v0) (coe v1))))))
-- Once.Adequacy.ImageUnique._.T
d_T_1338 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_T_1338 v0 ~v1 = du_T_1338 v0
du_T_1338 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_T_1338 v0
  = coe MAlonzo.Code.Once.Compile.d_moduleTable_868 (coe v0)
-- Once.Adequacy.ImageUnique._.tn
d_tn_1340 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_TableNames_510
d_tn_1340 v0 ~v1 = du_tn_1340 v0
du_tn_1340 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  T_TableNames_510
du_tn_1340 v0 = coe d_table'45'names_560 (coe v0)
-- Once.Adequacy.ImageUnique._.p
d_p_1342 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_p_1342 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe du_T_1338 (coe v0)) (coe v1)
-- Once.Adequacy.ImageUnique._.q
d_q_1344 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_q_1344 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_rewrite'45'program_894
      (coe d_p_1342 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.img
d_img_1346 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_img_1346 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_image'45'of_970
      (coe d_p_1342 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.fs
d_fs_1348 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6]
d_fs_1348 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_fdefs_244
      (coe d_img_1346 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.fs≡
d_fs'8801'_1350 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fs'8801'_1350 = erased
-- Once.Adequacy.ImageUnique._._.defs++blocks
d_defs'43''43'blocks_1354 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_defs'43''43'blocks_1354 ~v0 ~v1 = du_defs'43''43'blocks_1354
du_defs'43''43'blocks_1354 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_defs'43''43'blocks_1354 = coe du_defs'43''43'blocks_1274
-- Once.Adequacy.ImageUnique._._.def≢blk
d_def'8802'blk_1356 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_def'8802'blk_1356 = erased
-- Once.Adequacy.ImageUnique._._.heap-fresh
d_heap'45'fresh_1358 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_heap'45'fresh_1358 ~v0 ~v1 = du_heap'45'fresh_1358
du_heap'45'fresh_1358 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_heap'45'fresh_1358 = coe du_heap'45'fresh_1298
-- Once.Adequacy.ImageUnique._._.heap≢blk
d_heap'8802'blk_1360 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'blk_1360 = erased
-- Once.Adequacy.ImageUnique._._.heap≢def
d_heap'8802'def_1362 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'def_1362 = erased
-- Once.Adequacy.ImageUnique._._.start-fresh
d_start'45'fresh_1364 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_start'45'fresh_1364 ~v0 ~v1 = du_start'45'fresh_1364
du_start'45'fresh_1364 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_start'45'fresh_1364 = coe du_start'45'fresh_1314
-- Once.Adequacy.ImageUnique._._.start≢blk
d_start'8802'blk_1366 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'blk_1366 = erased
-- Once.Adequacy.ImageUnique._._.start≢def
d_start'8802'def_1368 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'def_1368 = erased
-- Once.Adequacy.ImageUnique._._.toEF
d_toEF_1370 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_toEF_1370 ~v0 ~v1 ~v2 v3 = du_toEF_1370 v3
du_toEF_1370 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_toEF_1370 v0 = coe v0
-- Once.Adequacy.ImageUnique._.D
d_D_1372 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_D_1372 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
      (coe d_img_1346 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.B
d_B_1374 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_B_1374 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_block'45'syms_932
      (coe
         MAlonzo.Code.Once.Compile.d_program'45'blocks_898
         (coe d_p_1342 (coe v0) (coe v1)))
-- Once.Adequacy.ImageUnique._.cD
d_cD_1376 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cD_1376 v0 v1
  = coe d_adefs'45'class_1084 (coe d_img_1346 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.cB
d_cB_1378 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cB_1378 v0 v1
  = coe
      d_blocks'45'sym_1054
      (coe
         MAlonzo.Code.Once.Compile.d_program'45'blocks_898
         (coe d_p_1342 (coe v0) (coe v1)))
-- Once.Adequacy.ImageUnique._.uD
d_uD_1380 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_uD_1380 v0 v1
  = coe
      d_adefs'45'unique_256 (coe d_img_1346 (coe v0) (coe v1))
      (coe
         d_image'45'cl_426
         (coe MAlonzo.Code.Once.Compile.d_entry'45'owner_962)
         (coe d_q_1344 (coe v0) (coe v1)))
      (coe du_EF'45'dist_1148 (coe du_tn_1340 (coe v0)))
-- Once.Adequacy.ImageUnique.lib-unique
d_lib'45'unique_1384 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_lib'45'unique_1384 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
      (coe
         du_heap'45'fresh_1298 (coe d_D_1422 (coe v0))
         (coe d_B_1424 (coe v0)) (coe d_cD_1426 (coe v0))
         (coe d_cB_1428 (coe v0)))
      (coe
         du_defs'43''43'blocks_1274 (coe d_D_1422 (coe v0))
         (coe d_B_1424 (coe v0)) (coe d_cD_1426 (coe v0))
         (coe d_cB_1428 (coe v0)) (coe d_uD_1430 (coe v0))
         (coe
            d_blocks'45'unique_1048
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'blocks_1022
               (coe d_T_1392 (coe v0)))))
-- Once.Adequacy.ImageUnique._.T
d_T_1392 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_T_1392 v0
  = coe MAlonzo.Code.Once.Compile.d_moduleTable_868 (coe v0)
-- Once.Adequacy.ImageUnique._.tn
d_tn_1394 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  T_TableNames_510
d_tn_1394 v0 = coe d_table'45'names_560 (coe v0)
-- Once.Adequacy.ImageUnique._.img
d_img_1396 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_img_1396 v0
  = coe
      MAlonzo.Code.Once.Compile.d_lib'45'image_1014
      (coe d_T_1392 (coe v0))
-- Once.Adequacy.ImageUnique._.fs
d_fs_1398 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6]
d_fs_1398 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_fdefs_244
      (coe d_img_1396 (coe v0))
-- Once.Adequacy.ImageUnique._.fs≡
d_fs'8801'_1400 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fs'8801'_1400 = erased
-- Once.Adequacy.ImageUnique._._.defs++blocks
d_defs'43''43'blocks_1404 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_defs'43''43'blocks_1404 ~v0 = du_defs'43''43'blocks_1404
du_defs'43''43'blocks_1404 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_defs'43''43'blocks_1404 = coe du_defs'43''43'blocks_1274
-- Once.Adequacy.ImageUnique._._.def≢blk
d_def'8802'blk_1406 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_def'8802'blk_1406 = erased
-- Once.Adequacy.ImageUnique._._.heap-fresh
d_heap'45'fresh_1408 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_heap'45'fresh_1408 ~v0 = du_heap'45'fresh_1408
du_heap'45'fresh_1408 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_heap'45'fresh_1408 = coe du_heap'45'fresh_1298
-- Once.Adequacy.ImageUnique._._.heap≢blk
d_heap'8802'blk_1410 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'blk_1410 = erased
-- Once.Adequacy.ImageUnique._._.heap≢def
d_heap'8802'def_1412 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'def_1412 = erased
-- Once.Adequacy.ImageUnique._._.start-fresh
d_start'45'fresh_1414 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_start'45'fresh_1414 ~v0 = du_start'45'fresh_1414
du_start'45'fresh_1414 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_start'45'fresh_1414 = coe du_start'45'fresh_1314
-- Once.Adequacy.ImageUnique._._.start≢blk
d_start'8802'blk_1416 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'blk_1416 = erased
-- Once.Adequacy.ImageUnique._._.start≢def
d_start'8802'def_1418 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'def_1418 = erased
-- Once.Adequacy.ImageUnique._._.toEF
d_toEF_1420 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_toEF_1420 ~v0 ~v1 v2 = du_toEF_1420 v2
du_toEF_1420 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_toEF_1420 v0 = coe v0
-- Once.Adequacy.ImageUnique._.D
d_D_1422 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_D_1422 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
      (coe d_img_1396 (coe v0))
-- Once.Adequacy.ImageUnique._.B
d_B_1424 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_B_1424 v0
  = coe
      MAlonzo.Code.Once.Compile.d_block'45'syms_932
      (coe
         MAlonzo.Code.Once.Compile.d_lib'45'blocks_1022
         (coe d_T_1392 (coe v0)))
-- Once.Adequacy.ImageUnique._.cD
d_cD_1426 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cD_1426 v0 = coe d_adefs'45'class_1084 (coe d_img_1396 (coe v0))
-- Once.Adequacy.ImageUnique._.cB
d_cB_1428 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cB_1428 v0
  = coe
      d_blocks'45'sym_1054
      (coe
         MAlonzo.Code.Once.Compile.d_lib'45'blocks_1022
         (coe d_T_1392 (coe v0)))
-- Once.Adequacy.ImageUnique._.uD
d_uD_1430 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_uD_1430 v0
  = coe
      d_adefs'45'unique_256 (coe d_img_1396 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_fns'45'cl_354 (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Once.Compile.d_rewrite'45'table_888
               (coe d_T_1392 (coe v0)))))
      (coe du_EF'45'dist_1148 (coe d_tn_1394 (coe v0)))
