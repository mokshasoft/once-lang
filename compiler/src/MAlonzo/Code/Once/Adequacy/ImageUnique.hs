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
import qualified MAlonzo.Code.Data.Digit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolInjective
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties

-- Once.Adequacy.ImageUnique.ilab
d_ilab_6 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28]
d_ilab_6 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v2
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idefs_76 = erased
-- Once.Adequacy.ImageUnique.idefl
d_idefl_86 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_idefl_86 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2268 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2272 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2274 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2276 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2278 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2280
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2284 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2286 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2290 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296 v1 v2 v3
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302 v1 v2 v3
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2310 v1 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2314 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v1
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
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2320 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.ileft
d_ileft_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ileft_96 = erased
-- Once.Adequacy.ImageUnique.iright
d_iright_106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iright_106 = erased
-- Once.Adequacy.ImageUnique.adefs-labs
d_adefs'45'labs_116 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_adefs'45'labs_116 = erased
-- Once.Adequacy.ImageUnique.dlabs-def
d_dlabs'45'def_124 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keys'45'lefts_144 = erased
-- Once.Adequacy.ImageUnique.keys-rights
d_keys'45'rights_152 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
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
                MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_dst'45''43''43'_84
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606
                      (coe du_o_368 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                      (coe (0 :: Integer)) (coe v0))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_608
                      (coe du_o_368 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                      (coe (0 :: Integer)) (coe v0)))
                (coe du_dU_372 (coe v0) (coe v2))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_rest_376 (coe v0) (coe v2) (coe v3)))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_dj'45'win_124
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606
                         (coe du_o_368 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                         (coe (0 :: Integer)) (coe v0))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_608
                         (coe du_o_368 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                         (coe (0 :: Integer)) (coe v0)))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_clabs_214
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
                      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606
                      (coe du_o_368 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                      (coe (0 :: Integer)) (coe v0))
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_608
                      (coe du_o_368 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                      (coe (0 :: Integer)) (coe v0)))
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_win'45'weaken_152
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606
                         (coe du_o_368 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                         (coe (0 :: Integer)) (coe v0))
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_608
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
                   MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_win'45'weaken_152
                   (MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_clabs_214
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
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_o_368 ~v0 v1 ~v2 = du_o_368 v1
du_o_368 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
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
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_frag_1420
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
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_frag'45'dst_1704
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
         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fdefs'45''43''43'_406 = erased
-- Once.Adequacy.ImageUnique.image-cl
d_image'45'cl_426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_image'45'cl_426 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_dst'45''43''43'_84
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe d_TL_452 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe d_nM_438 (coe v0) (coe v1)) (coe d_BL_454 (coe v0) (coe v1))))
      (d_dM_456 (coe v0) (coe v1))
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_FS_472 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_dj'45'win_124
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe d_TL_452 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe d_nM_438 (coe v0) (coe v1)) (coe d_BL_454 (coe v0) (coe v1))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_clabs_214
            (coe
               MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
               (coe addInt (coe (1 :: Integer)) (coe d_nM_438 (coe v0) (coe v1)))
               (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v1))))
         (coe d_wM_470 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_FS_472 (coe v0) (coe v1))))
-- Once.Adequacy.ImageUnique._.X
d_X_436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 -> Integer
d_nM_438 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelRange.du_label'45'of_42
      (coe d_X_436 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.F
d_F_440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_F_440 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_frag_1420 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Adequacy.ImageUnique._.dT
d_dT_442 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dT_442 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_F_440 (coe v0) (coe v1)))
-- Once.Adequacy.ImageUnique._.dB
d_dB_444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dB_444 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_F_440 (coe v0) (coe v1))))
-- Once.Adequacy.ImageUnique._.jTB
d_jTB_446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_jTB_446 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe d_F_440 (coe v0) (coe v1))))
-- Once.Adequacy.ImageUnique._.wT
d_wT_448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 -> [Integer]
d_TL_452 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Adequacy.ImageUnique._.BL
d_BL_454 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 -> [Integer]
d_BL_454 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_608 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Adequacy.ImageUnique._.dM
d_dM_456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dM_456 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_dst'45''43''43'_84
      (MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606
         (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
         (coe (0 :: Integer)) (coe (0 :: Integer)))
      (d_dT_442 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
         (coe
            MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_fresh'45'above_188
            (MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_608
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
               (coe (0 :: Integer)) (coe (0 :: Integer)))
            (d_wB_450 (coe v0) (coe v1)))
         (d_dB_444 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_zipWith_174
         (coe
            (\ v2 v3 ->
               coe
                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606 (coe v0)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
            (coe (0 :: Integer)) (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606 (coe v0)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
                  (coe (0 :: Integer)) (coe (0 :: Integer)))
               (coe d_wT_448 (coe v0) (coe v1)))
            (coe d_jTB_446 (coe v0) (coe v1))))
-- Once.Adequacy.ImageUnique._.wM
d_wM_470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wM_470 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606 (coe v0)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
         (coe (0 :: Integer)) (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_win'45'weaken_152
         (MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_TL_606
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
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
               (coe d_nM_438 (coe v0) (coe v1))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.LabelDefs.du_win'45'weaken_152
            (MAlonzo.Code.Once.CCC.Codegen.CLabelsUnique.d_BL_608
               (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
               (coe (0 :: Integer)) (coe (0 :: Integer)))
            (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
               (coe (0 :: Integer)))
            (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
               (coe d_nM_438 (coe v0) (coe v1)))
            (d_wB_450 (coe v0) (coe v1))))
-- Once.Adequacy.ImageUnique._.FS
d_FS_472 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_FS_472 v0 v1
  = coe
      d_fns'45'cl_354
      (coe addInt (coe (1 :: Integer)) (coe d_nM_438 (coe v0) (coe v1)))
      (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v1))
-- Once.Adequacy.ImageUnique._.eq
d_eq_474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq_474 = erased
-- Once.Adequacy.ImageUnique.image-fdefs
d_image'45'fdefs_482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_image'45'fdefs_482 = erased
-- Once.Adequacy.ImageUnique._.X
d_X_492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_X_492 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v1))
-- Once.Adequacy.ImageUnique._._∙_
d__'8729'__500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d__'8729'__500 = erased
-- Once.Adequacy.ImageUnique._.fdefs-++′
d_fdefs'45''43''43''8242'_506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fdefs'45''43''43''8242'_506 = erased
-- Once.Adequacy.ImageUnique.TableNames
d_TableNames_522 a0 = ()
data T_TableNames_522
  = C_constructor_546 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
                      MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.Adequacy.ImageUnique.TableNames.names
d_names_536 ::
  T_TableNames_522 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_names_536 v0
  = case coe v0 of
      C_constructor_546 v1 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.TableNames.syms≡
d_syms'8801'_540 ::
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_syms'8801'_540 = erased
-- Once.Adequacy.ImageUnique.TableNames.dist
d_dist_542 ::
  T_TableNames_522 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dist_542 v0
  = case coe v0 of
      C_constructor_546 v1 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.TableNames.valid
d_valid_544 ::
  T_TableNames_522 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_valid_544 v0
  = case coe v0 of
      C_constructor_546 v1 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.sym-of
d_sym'45'of_548 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_sym'45'of_548 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v0))
-- Once.Adequacy.ImageUnique.tbl-go
d_tbl'45'go_556 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_238] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tbl'45'go_556 = erased
-- Once.Adequacy.ImageUnique.no-names
d_no'45'names_568 :: T_TableNames_522
d_no'45'names_568
  = coe
      C_constructor_546
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
-- Once.Adequacy.ImageUnique.table-names
d_table'45'names_572 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  T_TableNames_522
d_table'45'names_572 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38 v1
        -> let v2
                 = MAlonzo.Code.Once.Parser.d_guardDistinct_560
                     (coe
                        MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                        (coe v1) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
                  -> coe d_no'45'names_568
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> let v4
                           = MAlonzo.Code.Once.Compile.d_compileEntries_466
                               (coe MAlonzo.Code.Once.IR.C_Heap_8)
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                               (coe MAlonzo.Code.Once.Compile.d_emptyCScope_394) (coe v3) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
                            -> coe d_no'45'names_568
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                            -> coe
                                 C_constructor_546
                                 (MAlonzo.Code.Once.Parser.d_emittedNames_544
                                    (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3)))
                                 (MAlonzo.Code.Once.Adequacy.NameClash.d_map'45'allpairs'45'own_150
                                    (coe
                                       MAlonzo.Code.Once.Parser.d_emittedNames_544
                                       (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3)))
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.NameClash.du_namesDistinct'45'sound_110
                                       (coe
                                          MAlonzo.Code.Once.Parser.d_emittedNames_544
                                          (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3))))
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.NameClash.du_allValidIdentB'45'sound_58
                                       (coe
                                          MAlonzo.Code.Once.Parser.d_emittedNames_544
                                          (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3)))))
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.NameClash.du_allValidIdentB'45'sound_58
                                    (coe
                                       MAlonzo.Code.Once.Parser.d_emittedNames_544
                                       (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3))))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.guard
d_guard_608 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guard_608 = erased
-- Once.Adequacy.ImageUnique.ap-reverse
d_ap'45'reverse_612 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_ap'45'reverse_612 v0 v1
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
                    (coe d_ap'45'reverse_612 (coe v3) (coe v7))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22))
                    (coe
                       du_rev'45'all_634 (coe v3)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                          (coe (\ v8 v9 v10 -> coe v9 erased)) (coe v3) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.rev-all
d_rev'45'all_634 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rev'45'all_634 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_rev'45'all_634 v4 v5
du_rev'45'all_634 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rev'45'all_634 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266
      (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0)
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
           (coe
              MAlonzo.Code.Data.List.Relation.Unary.All.du_lookup_436 v0 v1
              (coe du_rev'45''8712'_646 v0 v3))
           (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
-- Once.Adequacy.ImageUnique._._.rev-∈
d_rev'45''8712'_646 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_rev'45''8712'_646 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_rev'45''8712'_646 v4
du_rev'45''8712'_646 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_rev'45''8712'_646 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_reverse'8315'_2018
      (coe v0)
-- Once.Adequacy.ImageUnique.hd
d_hd_658 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_hd_658 v0
  = case coe v0 of
      [] -> coe ' '
      (:) v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.shd
d_shd_662 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_shd_662 v0
  = coe
      d_hd_658
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Adequacy.ImageUnique.once-hd
d_once'45'hd_668 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_once'45'hd_668 = erased
-- Once.Adequacy.ImageUnique.thunk-hd
d_thunk'45'hd_674 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thunk'45'hd_674 = erased
-- Once.Adequacy.ImageUnique.osp-hd
d_osp'45'hd_680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_osp'45'hd_680 = erased
-- Once.Adequacy.ImageUnique.hd≢
d_hd'8802'_692 ::
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
d_hd'8802'_692 = erased
-- Once.Adequacy.ImageUnique.map-nil
d_map'45'nil_708 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'nil_708 = erased
-- Once.Adequacy.ImageUnique.cib-ne
d_cib'45'ne_716 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cib'45'ne_716 = erased
-- Once.Adequacy.ImageUnique._.ds
d_ds_726 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_ds_726 v0 ~v1 = du_ds_726 v0
du_ds_726 :: Integer -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_ds_726 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Data.Digit.du_toDigits_84 (coe (10 :: Integer))
         (coe addInt (coe (1 :: Integer)) (coe v0)))
-- Once.Adequacy.ImageUnique._.rds≡[]
d_rds'8801''91''93'_728 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rds'8801''91''93'_728 = erased
-- Once.Adequacy.ImageUnique._.ds≡[]
d_ds'8801''91''93'_730 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ds'8801''91''93'_730 = erased
-- Once.Adequacy.ImageUnique._.0≢s
d_0'8802's_734 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_0'8802's_734 = erased
-- Once.Adequacy.ImageUnique.cib-head-digit
d_cib'45'head'45'digit_740 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cib'45'head'45'digit_740 = erased
-- Once.Adequacy.ImageUnique._.go
d_go_754 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_754 = erased
-- Once.Adequacy.ImageUnique.heap≢osp
d_heap'8802'osp_766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'osp_766 = erased
-- Once.Adequacy.ImageUnique._.toList-osp
d_toList'45'osp_778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'osp_778 = erased
-- Once.Adequacy.ImageUnique._.body
d_body_784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_body_784 = erased
-- Once.Adequacy.ImageUnique._._.∷-inj
d_'8759''45'inj_804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''45'inj_804 = erased
-- Once.Adequacy.ImageUnique._._.peel
d_peel_806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_peel_806 = erased
-- Once.Adequacy.ImageUnique._._.false≢true
d_false'8802'true_810 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_false'8802'true_810 = erased
-- Once.Adequacy.ImageUnique._._.L
d_L_812 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_L_812 ~v0 ~v1 v2 ~v3 ~v4 = du_L_812 v2
du_L_812 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
du_L_812 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe
         MAlonzo.Code.Once.Target.SymbolInjective.d_zencL_142
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
-- Once.Adequacy.ImageUnique._._.mangle-shape
d_mangle'45'shape_814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mangle'45'shape_814 = erased
-- Once.Adequacy.ImageUnique._._.digitRHS
d_digitRHS_818 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_digitRHS_818 = erased
-- Once.Adequacy.ImageUnique._._._.R
d_R_830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_R_830 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_R_830 v5 v6
du_R_830 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_R_830 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("_" :: Data.Text.Text)
      (MAlonzo.Code.Once.Target.Symbol.d_join'45'us_48
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe MAlonzo.Code.Once.Target.Symbol.d_mangle'45'component_44)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))))
-- Once.Adequacy.ImageUnique.own≢block
d_own'8802'block_842 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_own'8802'block_842 = erased
-- Once.Adequacy.ImageUnique._.bn
d_bn_856 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_bn_856 ~v0 v1 ~v2 ~v3 = du_bn_856 v1
du_bn_856 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_bn_856 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("arith.block." :: Data.Text.Text) v0
-- Once.Adequacy.ImageUnique._.∷-inj
d_'8759''45'inj_866 ::
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
d_'8759''45'inj_866 = erased
-- Once.Adequacy.ImageUnique._.sym-shape
d_sym'45'shape_870 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym'45'shape_870 = erased
-- Once.Adequacy.ImageUnique._.body≡
d_body'8801'_884 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'8801'_884 = erased
-- Once.Adequacy.ImageUnique._.hnd-x
d_hnd'45'x_886 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_hnd'45'x_886 v0 ~v1 v2 ~v3 = du_hnd'45'x_886 v0 v2
du_hnd'45'x_886 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
du_hnd'45'x_886 v0 v1
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
d_bn'45'chars_896 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bn'45'chars_896 = erased
-- Once.Adequacy.ImageUnique._.hnd-bn
d_hnd'45'bn_898 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_hnd'45'bn_898 = erased
-- Once.Adequacy.ImageUnique._.tl≡
d_tl'8801'_902 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tl'8801'_902 = erased
-- Once.Adequacy.ImageUnique._.Lx
d_Lx_904 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_Lx_904 v0 ~v1 ~v2 ~v3 = du_Lx_904 v0
du_Lx_904 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
du_Lx_904 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe
         MAlonzo.Code.Once.Target.SymbolInjective.d_zencL_142
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
-- Once.Adequacy.ImageUnique._.Lb
d_Lb_906 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_Lb_906 ~v0 v1 ~v2 ~v3 = du_Lb_906 v1
du_Lb_906 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
du_Lb_906 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe
         MAlonzo.Code.Once.Target.SymbolInjective.d_zencL_142
         (coe
            MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
            (coe du_bn_856 (coe v0))))
-- Once.Adequacy.ImageUnique._.not-valid
d_not'45'valid_908 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_not'45'valid_908 = erased
-- Once.Adequacy.ImageUnique._._.dot
d_dot_916 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dot_916 = erased
-- Once.Adequacy.ImageUnique.BlockSym
d_BlockSym_918 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_BlockSym_918 = erased
-- Once.Adequacy.ImageUnique.==-false
d_'61''61''45'false_928 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'61''61''45'false_928 = erased
-- Once.Adequacy.ImageUnique.any-false
d_any'45'false_972 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_any'45'false_972 ~v0 v1 ~v2 = du_any'45'false_972 v1
du_any'45'false_972 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_any'45'false_972 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
             (coe du_any'45'false_972 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.∨-falseˡ
d_'8744''45'false'737'_990 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'false'737'_990 = erased
-- Once.Adequacy.ImageUnique._.∨-falseʳ
d_'8744''45'false'691'_998 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'false'691'_998 = erased
-- Once.Adequacy.ImageUnique.DD
d_DD_1002 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_DD_1002 = erased
-- Once.Adequacy.ImageUnique.dedup-dd
d_dedup'45'dd_1016 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dedup'45'dd_1016 v0 v1
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
                    du_dedup'45'step_1030 (coe v0) (coe v4) (coe v3)
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
d_dedup'45'step_1030 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dedup'45'step_1030 v0 v1 ~v2 v3 v4 ~v5
  = du_dedup'45'step_1030 v0 v1 v3 v4
du_dedup'45'step_1030 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dedup'45'step_1030 v0 v1 v2 v3
  = if coe v3
      then coe d_dedup'45'dd_1016 (coe v0) (coe v2)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                (coe
                   du_head'45'fresh_1082
                   (coe
                      MAlonzo.Code.Once.Compile.d_dedup'45'go_918
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                      (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_dedup'45'dd_1016
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                         (coe v2))))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_dedup'45'dd_1016
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                      (coe v2))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe du_any'45'false_972 (coe v0))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                   (\ v4 v5 -> coe du_tl_1070 v5)
                   (coe
                      MAlonzo.Code.Once.Compile.d_dedup'45'go_918
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                      (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_dedup'45'dd_1016
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                         (coe v2)))))
-- Once.Adequacy.ImageUnique._.tl
d_tl_1070 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_tl_1070 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_tl_1070 v6
du_tl_1070 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_tl_1070 v0
  = case coe v0 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v3 v4
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique._.head-fresh
d_head'45'fresh_1082 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_head'45'fresh_1082 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_head'45'fresh_1082 v5 v6
du_head'45'fresh_1082 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_head'45'fresh_1082 v0 v1
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
                           (coe du_head'45'fresh_1082 (coe v3) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.dedup-⊆
d_dedup'45''8838'_1106 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dedup'45''8838'_1106 ~v0 v1 v2 v3
  = du_dedup'45''8838'_1106 v1 v2 v3
du_dedup'45''8838'_1106 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_dedup'45''8838'_1106 v0 v1 v2
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
                           du_dedup'45''8838''45'step_1124 (coe v0) (coe v5) (coe v4)
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
d_dedup'45''8838''45'step_1124 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dedup'45''8838''45'step_1124 ~v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_dedup'45''8838''45'step_1124 v1 v2 v4 v5 v6 v7
du_dedup'45''8838''45'step_1124 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_dedup'45''8838''45'step_1124 v0 v1 v2 v3 v4 v5
  = if coe v3
      then coe du_dedup'45''8838'_1106 (coe v0) (coe v2) (coe v5)
      else coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
             (coe
                du_dedup'45''8838'_1106
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0))
                (coe v2) (coe v5))
-- Once.Adequacy.ImageUnique.tag
d_tag_1164 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag_1164 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Compile.d_block'45'symbol_934 (coe v0))
      (coe v0)
-- Once.Adequacy.ImageUnique.tagged
d_tagged_1172 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_tagged_1172 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'digest_358
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'shape_174 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_178 (coe v1)))
                erased)
             (d_tagged_1172 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.fsts
d_fsts_1184 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fsts_1184 ~v0 v1 v2 = du_fsts_1184 v1 v2
du_fsts_1184 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fsts_1184 v0 v1
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
                    (coe du_fsts_1184 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.blocks-unique
d_blocks'45'unique_1194 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_blocks'45'unique_1194 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         d_dedup'45'dd_1016
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22 (coe d_tag_1164) (coe v0)))
-- Once.Adequacy.ImageUnique.blocks-sym
d_blocks'45'sym_1200 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'sym_1200 v0
  = coe
      du_fsts_1184
      (coe
         MAlonzo.Code.Once.Compile.d_dedup'45'blocks_932
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22 (coe d_tag_1164) (coe v0)))
      (coe
         du_dedup'45''8838'_1106
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22 (coe d_tag_1164) (coe v0))
         (coe d_tagged_1172 (coe v0)))
-- Once.Adequacy.ImageUnique.rights-∈
d_rights'45''8712'_1208 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_rights'45''8712'_1208 ~v0 v1 v2 = du_rights'45''8712'_1208 v1 v2
du_rights'45''8712'_1208 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_rights'45''8712'_1208 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
                      -> coe du_rights'45''8712'_1208 (coe v3) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v7
                      -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                           (coe du_rights'45''8712'_1208 (coe v3) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageUnique.DefClass
d_DefClass_1222 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_DefClass_1222 = erased
-- Once.Adequacy.ImageUnique.adefs-class
d_adefs'45'class_1230 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_adefs'45'class_1230 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_map'8314'_496
      (coe d_dlabs_12 (coe v0))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266
         (d_dlabs_12 (coe v0)) (d_cls_1240 (coe v0)))
-- Once.Adequacy.ImageUnique._.cls
d_cls_1240 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cls_1240 v0 v1 v2
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
                       du_rights'45''8712'_1208
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
d_no'45'sigop_1262 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Adequacy.LabelSymbols.T_DefL_18 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'sigop_1262 = erased
-- Once.Adequacy.ImageUnique.rt-names
d_rt'45'names_1266 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rt'45'names_1266 = erased
-- Once.Adequacy.ImageUnique.Entries._.dist
d_dist_1282 ::
  T_TableNames_522 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dist_1282 v0 = coe d_dist_542 (coe v0)
-- Once.Adequacy.ImageUnique.Entries._.names
d_names_1284 ::
  T_TableNames_522 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_names_1284 v0 = coe d_names_536 (coe v0)
-- Once.Adequacy.ImageUnique.Entries._.syms≡
d_syms'8801'_1286 ::
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_syms'8801'_1286 = erased
-- Once.Adequacy.ImageUnique.Entries._.valid
d_valid_1288 ::
  T_TableNames_522 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_valid_1288 v0 = coe d_valid_544 (coe v0)
-- Once.Adequacy.ImageUnique.Entries.EF
d_EF_1290 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_EF_1290 v0 ~v1 = du_EF_1290 v0
du_EF_1290 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_EF_1290 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v1 -> MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1)))
         (coe MAlonzo.Code.Once.Compile.d_rewrite'45'table_894 (coe v0)))
-- Once.Adequacy.ImageUnique.Entries.EF≡
d_EF'8801'_1292 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_EF'8801'_1292 = erased
-- Once.Adequacy.ImageUnique.Entries.EF-dist
d_EF'45'dist_1294 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_EF'45'dist_1294 ~v0 v1 = du_EF'45'dist_1294 v1
du_EF'45'dist_1294 ::
  T_TableNames_522 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_EF'45'dist_1294 v0
  = coe
      d_ap'45'reverse_612
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_62)
         (coe d_names_536 (coe v0)))
      (coe d_dist_542 (coe v0))
-- Once.Adequacy.ImageUnique.Entries.EF-own
d_EF'45'own_1300 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_EF'45'own_1300 ~v0 v1 ~v2 v3 = du_EF'45'own_1300 v1 v3
du_EF'45'own_1300 ::
  T_TableNames_522 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_EF'45'own_1300 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.List.Membership.Setoid.du_find_86
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
              (coe d_names_536 (coe v0))
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_map'8315'_736
                 (coe d_names_536 (coe v0))
                 (coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_reverse'8315'_2018
                    (coe
                       MAlonzo.Code.Data.List.Base.du_map_22
                       (coe MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_62)
                       (coe d_names_536 (coe v0)))
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
                             (d_names_536 (coe v0)) (d_valid_544 (coe v0)) v5)
                          erased)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ImageUnique.Apart._.EF
d_EF_1332 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_EF_1332 ~v0 v1 ~v2 ~v3 = du_EF_1332 v1
du_EF_1332 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_EF_1332 v0 = coe du_EF_1290 (coe v0)
-- Once.Adequacy.ImageUnique.Apart._.EF-dist
d_EF'45'dist_1334 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_EF'45'dist_1334 ~v0 ~v1 v2 ~v3 = du_EF'45'dist_1334 v2
du_EF'45'dist_1334 ::
  T_TableNames_522 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_EF'45'dist_1334 v0 = coe du_EF'45'dist_1294 (coe v0)
-- Once.Adequacy.ImageUnique.Apart._.EF-own
d_EF'45'own_1336 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_EF'45'own_1336 ~v0 ~v1 v2 ~v3 = du_EF'45'own_1336 v2
du_EF'45'own_1336 ::
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_EF'45'own_1336 v0 v1 v2 = coe du_EF'45'own_1300 (coe v0) v2
-- Once.Adequacy.ImageUnique.Apart._.EF≡
d_EF'8801'_1338 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_EF'8801'_1338 = erased
-- Once.Adequacy.ImageUnique.Apart.toEF
d_toEF_1342 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_toEF_1342 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_toEF_1342 v5
du_toEF_1342 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_toEF_1342 v0 = coe v0
-- Once.Adequacy.ImageUnique.Apart.def≢blk
d_def'8802'blk_1350 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_def'8802'blk_1350 = erased
-- Once.Adequacy.ImageUnique.Apart.heap≢def
d_heap'8802'def_1374 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'def_1374 = erased
-- Once.Adequacy.ImageUnique.Apart.heap≢blk
d_heap'8802'blk_1390 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'blk_1390 = erased
-- Once.Adequacy.ImageUnique.Apart.start≢def
d_start'8802'def_1396 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'def_1396 = erased
-- Once.Adequacy.ImageUnique.Apart.start≢blk
d_start'8802'blk_1412 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'blk_1412 = erased
-- Once.Adequacy.ImageUnique.Apart.defs++blocks
d_defs'43''43'blocks_1420 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_defs'43''43'blocks_1420 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_defs'43''43'blocks_1420 v4 v5 v6 v7 v8 v9
du_defs'43''43'blocks_1420 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_defs'43''43'blocks_1420 v0 v1 v2 v3 v4 v5
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
d_heap'45'fresh_1444 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_heap'45'fresh_1444 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_heap'45'fresh_1444 v4 v5 v6 v7
du_heap'45'fresh_1444 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_heap'45'fresh_1444 v0 v1 v2 v3
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
d_start'45'fresh_1460 ::
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_TableNames_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_start'45'fresh_1460 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_start'45'fresh_1460 v4 v5 v6 v7
du_start'45'fresh_1460 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_start'45'fresh_1460 v0 v1 v2 v3
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
d_prog'45'unique_1474 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_prog'45'unique_1474 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
         (coe
            du_heap'45'fresh_1444 (coe d_D_1518 (coe v0) (coe v1))
            (coe d_B_1520 (coe v0) (coe v1)) (coe d_cD_1522 (coe v0) (coe v1))
            (coe d_cB_1524 (coe v0) (coe v1))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
         (coe
            du_start'45'fresh_1460 (coe d_D_1518 (coe v0) (coe v1))
            (coe d_B_1520 (coe v0) (coe v1)) (coe d_cD_1522 (coe v0) (coe v1))
            (coe d_cB_1524 (coe v0) (coe v1)))
         (coe
            du_defs'43''43'blocks_1420 (coe d_D_1518 (coe v0) (coe v1))
            (coe d_B_1520 (coe v0) (coe v1)) (coe d_cD_1522 (coe v0) (coe v1))
            (coe d_cB_1524 (coe v0) (coe v1)) (coe d_uD_1526 (coe v0) (coe v1))
            (coe
               d_blocks'45'unique_1194
               (coe
                  MAlonzo.Code.Once.Compile.d_program'45'blocks_904
                  (coe d_p_1488 (coe v0) (coe v1))))))
-- Once.Adequacy.ImageUnique._.T
d_T_1484 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_T_1484 v0 ~v1 = du_T_1484 v0
du_T_1484 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_T_1484 v0
  = coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0)
-- Once.Adequacy.ImageUnique._.tn
d_tn_1486 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_TableNames_522
d_tn_1486 v0 ~v1 = du_tn_1486 v0
du_tn_1486 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  T_TableNames_522
du_tn_1486 v0 = coe d_table'45'names_572 (coe v0)
-- Once.Adequacy.ImageUnique._.p
d_p_1488 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_p_1488 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe du_T_1484 (coe v0)) (coe v1)
-- Once.Adequacy.ImageUnique._.q
d_q_1490 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_q_1490 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_rewrite'45'program_900
      (coe d_p_1488 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.img
d_img_1492 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_img_1492 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_image'45'of_972
      (coe d_p_1488 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.fs
d_fs_1494 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_fs_1494 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_fdefs_250
      (coe d_img_1492 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.fs≡
d_fs'8801'_1496 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fs'8801'_1496 = erased
-- Once.Adequacy.ImageUnique._._.defs++blocks
d_defs'43''43'blocks_1500 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_defs'43''43'blocks_1500 ~v0 ~v1 = du_defs'43''43'blocks_1500
du_defs'43''43'blocks_1500 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_defs'43''43'blocks_1500 = coe du_defs'43''43'blocks_1420
-- Once.Adequacy.ImageUnique._._.def≢blk
d_def'8802'blk_1502 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_def'8802'blk_1502 = erased
-- Once.Adequacy.ImageUnique._._.heap-fresh
d_heap'45'fresh_1504 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_heap'45'fresh_1504 ~v0 ~v1 = du_heap'45'fresh_1504
du_heap'45'fresh_1504 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_heap'45'fresh_1504 = coe du_heap'45'fresh_1444
-- Once.Adequacy.ImageUnique._._.heap≢blk
d_heap'8802'blk_1506 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'blk_1506 = erased
-- Once.Adequacy.ImageUnique._._.heap≢def
d_heap'8802'def_1508 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'def_1508 = erased
-- Once.Adequacy.ImageUnique._._.start-fresh
d_start'45'fresh_1510 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_start'45'fresh_1510 ~v0 ~v1 = du_start'45'fresh_1510
du_start'45'fresh_1510 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_start'45'fresh_1510 = coe du_start'45'fresh_1460
-- Once.Adequacy.ImageUnique._._.start≢blk
d_start'8802'blk_1512 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'blk_1512 = erased
-- Once.Adequacy.ImageUnique._._.start≢def
d_start'8802'def_1514 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'def_1514 = erased
-- Once.Adequacy.ImageUnique._._.toEF
d_toEF_1516 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_toEF_1516 ~v0 ~v1 ~v2 v3 = du_toEF_1516 v3
du_toEF_1516 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_toEF_1516 v0 = coe v0
-- Once.Adequacy.ImageUnique._.D
d_D_1518 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_D_1518 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
      (coe d_img_1492 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.B
d_B_1520 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_B_1520 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_block'45'syms_938
      (coe
         MAlonzo.Code.Once.Compile.d_program'45'blocks_904
         (coe d_p_1488 (coe v0) (coe v1)))
-- Once.Adequacy.ImageUnique._.cD
d_cD_1522 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cD_1522 v0 v1
  = coe d_adefs'45'class_1230 (coe d_img_1492 (coe v0) (coe v1))
-- Once.Adequacy.ImageUnique._.cB
d_cB_1524 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cB_1524 v0 v1
  = coe
      d_blocks'45'sym_1200
      (coe
         MAlonzo.Code.Once.Compile.d_program'45'blocks_904
         (coe d_p_1488 (coe v0) (coe v1)))
-- Once.Adequacy.ImageUnique._.uD
d_uD_1526 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_uD_1526 v0 v1
  = coe
      d_adefs'45'unique_256 (coe d_img_1492 (coe v0) (coe v1))
      (coe
         d_image'45'cl_426
         (coe MAlonzo.Code.Once.Compile.d_entry'45'owner_964)
         (coe d_q_1490 (coe v0) (coe v1)))
      (coe du_EF'45'dist_1294 (coe du_tn_1486 (coe v0)))
-- Once.Adequacy.ImageUnique.lib-unique
d_lib'45'unique_1530 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_lib'45'unique_1530 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
      (coe
         du_heap'45'fresh_1444 (coe d_D_1568 (coe v0))
         (coe d_B_1570 (coe v0)) (coe d_cD_1572 (coe v0))
         (coe d_cB_1574 (coe v0)))
      (coe
         du_defs'43''43'blocks_1420 (coe d_D_1568 (coe v0))
         (coe d_B_1570 (coe v0)) (coe d_cD_1572 (coe v0))
         (coe d_cB_1574 (coe v0)) (coe d_uD_1576 (coe v0))
         (coe
            d_blocks'45'unique_1194
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'blocks_1024
               (coe d_T_1538 (coe v0)))))
-- Once.Adequacy.ImageUnique._.T
d_T_1538 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_T_1538 v0
  = coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0)
-- Once.Adequacy.ImageUnique._.tn
d_tn_1540 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  T_TableNames_522
d_tn_1540 v0 = coe d_table'45'names_572 (coe v0)
-- Once.Adequacy.ImageUnique._.img
d_img_1542 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_img_1542 v0
  = coe
      MAlonzo.Code.Once.Compile.d_lib'45'image_1016
      (coe d_T_1538 (coe v0))
-- Once.Adequacy.ImageUnique._.fs
d_fs_1544 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_fs_1544 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelDefs.d_fdefs_250
      (coe d_img_1542 (coe v0))
-- Once.Adequacy.ImageUnique._.fs≡
d_fs'8801'_1546 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fs'8801'_1546 = erased
-- Once.Adequacy.ImageUnique._._.defs++blocks
d_defs'43''43'blocks_1550 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_defs'43''43'blocks_1550 ~v0 = du_defs'43''43'blocks_1550
du_defs'43''43'blocks_1550 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_defs'43''43'blocks_1550 = coe du_defs'43''43'blocks_1420
-- Once.Adequacy.ImageUnique._._.def≢blk
d_def'8802'blk_1552 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_def'8802'blk_1552 = erased
-- Once.Adequacy.ImageUnique._._.heap-fresh
d_heap'45'fresh_1554 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_heap'45'fresh_1554 ~v0 = du_heap'45'fresh_1554
du_heap'45'fresh_1554 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_heap'45'fresh_1554 = coe du_heap'45'fresh_1444
-- Once.Adequacy.ImageUnique._._.heap≢blk
d_heap'8802'blk_1556 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'blk_1556 = erased
-- Once.Adequacy.ImageUnique._._.heap≢def
d_heap'8802'def_1558 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'8802'def_1558 = erased
-- Once.Adequacy.ImageUnique._._.start-fresh
d_start'45'fresh_1560 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_start'45'fresh_1560 ~v0 = du_start'45'fresh_1560
du_start'45'fresh_1560 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_start'45'fresh_1560 = coe du_start'45'fresh_1460
-- Once.Adequacy.ImageUnique._._.start≢blk
d_start'8802'blk_1562 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'blk_1562 = erased
-- Once.Adequacy.ImageUnique._._.start≢def
d_start'8802'def_1564 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_start'8802'def_1564 = erased
-- Once.Adequacy.ImageUnique._._.toEF
d_toEF_1566 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_toEF_1566 ~v0 ~v1 v2 = du_toEF_1566 v2
du_toEF_1566 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_toEF_1566 v0 = coe v0
-- Once.Adequacy.ImageUnique._.D
d_D_1568 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_D_1568 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
      (coe d_img_1542 (coe v0))
-- Once.Adequacy.ImageUnique._.B
d_B_1570 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_B_1570 v0
  = coe
      MAlonzo.Code.Once.Compile.d_block'45'syms_938
      (coe
         MAlonzo.Code.Once.Compile.d_lib'45'blocks_1024
         (coe d_T_1538 (coe v0)))
-- Once.Adequacy.ImageUnique._.cD
d_cD_1572 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cD_1572 v0 = coe d_adefs'45'class_1230 (coe d_img_1542 (coe v0))
-- Once.Adequacy.ImageUnique._.cB
d_cB_1574 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cB_1574 v0
  = coe
      d_blocks'45'sym_1200
      (coe
         MAlonzo.Code.Once.Compile.d_lib'45'blocks_1024
         (coe d_T_1538 (coe v0)))
-- Once.Adequacy.ImageUnique._.uD
d_uD_1576 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_uD_1576 v0
  = coe
      d_adefs'45'unique_256 (coe d_img_1542 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_fns'45'cl_354 (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Once.Compile.d_rewrite'45'table_894
               (coe d_T_1538 (coe v0)))))
      (coe du_EF'45'dist_1294 (coe d_tn_1540 (coe v0)))
