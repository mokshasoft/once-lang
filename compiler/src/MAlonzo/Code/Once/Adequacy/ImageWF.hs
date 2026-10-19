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
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.List.Membership.Propositional
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Membership.Setoid
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
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ImageWF.StrMem._∈_
d__'8712'__8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d__'8712'__8 = erased
-- Once.Adequacy.ImageWF.StrMem._∈?_
d__'8712''63'__10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712''63'__10
  = let v0 = MAlonzo.Code.Data.String.Properties.d__'8799'__54 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Once.Adequacy.ImageWF.StrMem._∉_
d__'8713'__12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d__'8713'__12 = erased
-- Once.Adequacy.ImageWF.StrMem._∉?_
d__'8713''63'__14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8713''63'__14
  = let v0 = MAlonzo.Code.Data.String.Properties.d__'8799'__54 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8713''63'__68
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Once.Adequacy.ImageWF.StrMem._∷=_
d__'8759''61'__16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d__'8759''61'__16
  = coe MAlonzo.Code.Data.List.Membership.Setoid.du__'8759''61'__52
-- Once.Adequacy.ImageWF.StrMem._≢∈_
d__'8802''8712'__18 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> ()
d__'8802''8712'__18 = erased
-- Once.Adequacy.ImageWF.StrMem._─_
d__'9472'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d__'9472'__20
  = coe MAlonzo.Code.Data.List.Membership.Setoid.du__'9472'__54
-- Once.Adequacy.ImageWF.StrMem.find
d_find_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find_22 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_find_86
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      v2 v3
-- Once.Adequacy.ImageWF.StrMem.lose
d_lose_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lose_24 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Membership.Propositional.du_lose_50 v2 v3
-- Once.Adequacy.ImageWF.StrMem.mapWith∈
d_mapWith'8712'_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny) ->
  [AgdaAny]
d_mapWith'8712'_26 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_mapWith'8712'_64
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      v2 v3
-- Once.Adequacy.ImageWF.prog-defs
d_prog'45'defs_28 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_prog'45'defs_28 v0
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
               (coe MAlonzo.Code.Once.Compile.d_image'45'of_1186 (coe v0)))
            (coe
               MAlonzo.Code.Once.Compile.d_block'45'syms_1148
               (coe
                  MAlonzo.Code.Once.Compile.d_program'45'blocks_1114 (coe v0)))))
-- Once.Adequacy.ImageWF.lib-defs
d_lib'45'defs_32 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lib'45'defs_32 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_heap'45'symbol_8)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'image_1230
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_1084 (coe v0))))
         (coe
            MAlonzo.Code.Once.Compile.d_block'45'syms_1148
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'blocks_1238
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_1084 (coe v0)))))
-- Once.Adequacy.ImageWF.Resolved
d_Resolved_36 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_Resolved_36 = erased
-- Once.Adequacy.ImageWF.ProgG
d_ProgG_46 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_ProgG_46 = erased
-- Once.Adequacy.ImageWF.ProgP
d_ProgP_58 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 -> ()
d_ProgP_58 = erased
-- Once.Adequacy.ImageWF.calls-ok
d_calls'45'ok_70 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_calls'45'ok_70 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266
      (MAlonzo.Code.Once.Compile.d_calls'45'of_1154
         (coe
            MAlonzo.Code.Once.Compile.d_rewrite'45'program_1110
            (coe
               MAlonzo.Code.Once.Denotation.Program.C_irProgram_396
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_1084 (coe v0))
               (coe v1))))
      (\ v2 v3 ->
         coe
           du_split_84 (coe v0) (coe v1) (coe v3)
           (coe
              MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                 (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
              (coe v2)
              (coe
                 MAlonzo.Code.Once.Compile.d_block'45'syms_1148
                 (coe
                    MAlonzo.Code.Once.Compile.d_program'45'blocks_1114
                    (coe d_p_80 (coe v0) (coe v1))))))
-- Once.Adequacy.ImageWF._.p
d_p_80 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_p_80 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_396
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_1084 (coe v0))
      (coe v1)
-- Once.Adequacy.ImageWF._.split
d_split_84 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split_84 v0 v1 ~v2 v3 v4 = du_split_84 v0 v1 v3 v4
du_split_84 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_split_84 v0 v1 v2 v3
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
                                          MAlonzo.Code.Once.Compile.d_image'45'of_1186
                                          (coe d_p_80 (coe v0) (coe v1))))
                                    (MAlonzo.Code.Once.Compile.d_block'45'syms_1148
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_program'45'blocks_1114
                                          (coe d_p_80 (coe v0) (coe v1))))
                                    v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                          (coe
                             MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'filter'8314'_510
                             (MAlonzo.Code.Once.Compile.d_is'45'extern'63'_1164
                                (coe d_p_80 (coe v0) (coe v1)))
                             (MAlonzo.Code.Once.Compile.d_calls'45'of_1154
                                (coe
                                   MAlonzo.Code.Once.Compile.d_rewrite'45'program_1110
                                   (coe d_p_80 (coe v0) (coe v1))))
                             v2 erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageWF.table-ok
d_table'45'ok_112 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_table'45'ok_112 ~v0 v1 v2 = du_table'45'ok_112 v1 v2
du_table'45'ok_112 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_table'45'ok_112 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe
                MAlonzo.Code.Once.CCC.Codegen.NodesOK.du_leaf'45'syms'45'leaves_134
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_100
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))
                      (coe v1))))
             (coe
                du_table'45'ok_112 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_100
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))
                      (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageWF.prog-sigops
d_prog'45'sigops_128 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prog'45'sigops_128 v0 v1 ~v2 = du_prog'45'sigops_128 v0 v1
du_prog'45'sigops_128 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prog'45'sigops_128 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Codegen.NodesOK.du_leaf'45'syms'45'leaves_134
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_main_394
            (coe du_rp_138 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_100
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.d_main_394
                     (coe du_rp_138 (coe v0) (coe v1))))
               (coe d_calls'45'ok_70 (coe v0) (coe v1)))))
      (coe
         du_table'45'ok_112
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_table_392
            (coe du_rp_138 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315'_626
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_100
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.d_main_394
                     (coe du_rp_138 (coe v0) (coe v1))))
               (coe d_calls'45'ok_70 (coe v0) (coe v1)))))
-- Once.Adequacy.ImageWF._.rp
d_rp_138 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_rp_138 v0 v1 ~v2 = du_rp_138 v0 v1
du_rp_138 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
du_rp_138 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_rewrite'45'program_1110
      (coe
         MAlonzo.Code.Once.Denotation.Program.C_irProgram_396
         (coe MAlonzo.Code.Once.Compile.d_moduleTable_1084 (coe v0))
         (coe v1))
