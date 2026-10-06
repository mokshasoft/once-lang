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

module MAlonzo.Code.Once.Adequacy.ImageWF where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.ImageSymbols
import qualified MAlonzo.Code.Once.CCC.Codegen.NodesOK
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ImageWF._._∈?_
d__'8712''63'__8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712''63'__8
  = let v0 = MAlonzo.Code.Data.String.Properties.d__'8799'__54 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Once.Adequacy.ImageWF.prog-defs
d_prog'45'defs_10 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_prog'45'defs_10 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_heap'45'symbol_8)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe ("_start" :: Data.Text.Text))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
               (coe MAlonzo.Code.Once.Compile.d_image'45'of_972 (coe v0)))
            (coe
               MAlonzo.Code.Once.Compile.d_block'45'syms_938
               (coe MAlonzo.Code.Once.Compile.d_program'45'blocks_904 (coe v0)))))
-- Once.Adequacy.ImageWF.lib-defs
d_lib'45'defs_14 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lib'45'defs_14 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_heap'45'symbol_8)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'image_1016
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0))))
         (coe
            MAlonzo.Code.Once.Compile.d_block'45'syms_938
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'blocks_1024
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0)))))
-- Once.Adequacy.ImageWF.Resolved
d_Resolved_18 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_Resolved_18 = erased
-- Once.Adequacy.ImageWF.ProgG
d_ProgG_28 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_ProgG_28 = erased
-- Once.Adequacy.ImageWF.ProgP
d_ProgP_40 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> ()
d_ProgP_40 = erased
-- Once.Adequacy.ImageWF.calls-ok
d_calls'45'ok_52 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_calls'45'ok_52 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266
      (MAlonzo.Code.Once.Compile.d_calls'45'of_944
         (coe
            MAlonzo.Code.Once.Compile.d_rewrite'45'program_900
            (coe
               MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0))
               (coe v1))))
      (\ v2 v3 ->
         coe
           du_split_66 (coe v0) (coe v1) (coe v3)
           (coe
              MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                 (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
              (coe v2)
              (coe
                 MAlonzo.Code.Once.Compile.d_block'45'syms_938
                 (coe
                    MAlonzo.Code.Once.Compile.d_program'45'blocks_904
                    (coe d_p_62 (coe v0) (coe v1))))))
-- Once.Adequacy.ImageWF._.p
d_p_62 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_p_62 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0)) (coe v1)
-- Once.Adequacy.ImageWF._.split
d_split_66 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split_66 v0 v1 ~v2 v3 v4 = du_split_66 v0 v1 v3 v4
du_split_66 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_split_66 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                 (coe
                                    MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                                    (MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_image'45'of_972
                                          (coe d_p_62 (coe v0) (coe v1))))
                                    (MAlonzo.Code.Once.Compile.d_block'45'syms_938
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_program'45'blocks_904
                                          (coe d_p_62 (coe v0) (coe v1))))
                                    v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'filter'8314'_510
                          (MAlonzo.Code.Once.Compile.d_is'45'extern'63'_954
                             (coe d_p_62 (coe v0) (coe v1)))
                          (MAlonzo.Code.Once.Compile.d_calls'45'of_944
                             (coe
                                MAlonzo.Code.Once.Compile.d_rewrite'45'program_900
                                (coe d_p_62 (coe v0) (coe v1))))
                          v2 erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageWF.table-ok
d_table'45'ok_94 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_table'45'ok_94 ~v0 v1 v2 = du_table'45'ok_94 v1 v2
du_table'45'ok_94 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_table'45'ok_94 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe
                MAlonzo.Code.Once.CCC.Codegen.NodesOK.du_leaf'45'syms'45'leaves_128
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_96
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))
                      (coe v1))))
             (coe
                du_table'45'ok_94 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_96
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))
                      (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageWF.prog-sigops
d_prog'45'sigops_110 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prog'45'sigops_110 v0 v1 ~v2 = du_prog'45'sigops_110 v0 v1
du_prog'45'sigops_110 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prog'45'sigops_110 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Codegen.NodesOK.du_leaf'45'syms'45'leaves_128
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_main_388
            (coe du_rp_120 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_96
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.d_main_388
                     (coe du_rp_120 (coe v0) (coe v1))))
               (coe d_calls'45'ok_52 (coe v0) (coe v1)))))
      (coe
         du_table'45'ok_94
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_table_386
            (coe du_rp_120 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_96
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.d_main_388
                     (coe du_rp_120 (coe v0) (coe v1))))
               (coe d_calls'45'ok_52 (coe v0) (coe v1)))))
-- Once.Adequacy.ImageWF._.rp
d_rp_120 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_rp_120 v0 v1 ~v2 = du_rp_120 v0 v1
du_rp_120 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
du_rp_120 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_rewrite'45'program_900
      (coe
         MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
         (coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0))
         (coe v1))
