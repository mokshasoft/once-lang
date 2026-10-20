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

module MAlonzo.Code.Once.Adequacy.ImageResolved where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
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
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.ImageWF
import qualified MAlonzo.Code.Once.Adequacy.ProgramLinked
import qualified MAlonzo.Code.Once.Adequacy.SourceTrace
import qualified MAlonzo.Code.Once.Adequacy.TelePosition
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.ImageSymbols
import qualified MAlonzo.Code.Once.CCC.Codegen.LabelScope
import qualified MAlonzo.Code.Once.CCC.Codegen.NodesOK
import qualified MAlonzo.Code.Once.CCC.Codegen.ProgramImage
import qualified MAlonzo.Code.Once.CCC.Codegen.RefsClosed
import qualified MAlonzo.Code.Once.CCC.Codegen.SlotBudget
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ImageResolved.defd-self
d_defd'45'self_12 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_defd'45'self_12 v0 ~v1 v2 ~v3 v4 = du_defd'45'self_12 v0 v2 v4
du_defd'45'self_12 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_defd'45'self_12 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v7
               -> coe
                    MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                    (MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_instr'45'defs_26
                       (coe v3))
                    v2
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
               -> coe
                    MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                    (MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_instr'45'defs_26
                       (coe v3))
                    (MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38 (coe v4))
                    (coe du_defd'45'self_12 (coe v4) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved.linked-entry
d_linked'45'entry_38 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_linked'45'entry_38 v0 v1 v2 v3 v4
  = case coe v0 of
      (:) v5 v6
        -> coe
             du_at_88 (coe v5) (coe v6) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
                (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v5))
                (coe v1))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__196
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v5))
                (coe v2))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__196
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v5))
                (coe v3))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved._.rest
d_rest_64 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rest_64 ~v0 v1 v2 v3 v4 ~v5 v6 = du_rest_64 v1 v2 v3 v4 v6
du_rest_64 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rest_64 v0 v1 v2 v3 v4
  = let v5
          = d_linked'45'entry_38
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8)
                          (coe v9))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ImageResolved._.at
d_at_88 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_88 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_at_88 v0 v1 v2 v3 v4 v6 v7 v8 v9
du_at_88 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_88 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then case coe v10 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                      -> case coe v6 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                             -> if coe v12
                                  then coe
                                         seq (coe v13)
                                         (case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                              -> if coe v14
                                                   then coe
                                                          seq (coe v15)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v0)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                                   erased)
                                                                (coe v11)))
                                                   else coe
                                                          seq (coe v15)
                                                          (coe
                                                             du_rest_64 (coe v1) (coe v2) (coe v3)
                                                             (coe v4) (coe v8))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  else coe
                                         seq (coe v13)
                                         (coe
                                            du_rest_64 (coe v1) (coe v2) (coe v3) (coe v4) (coe v8))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v10)
                    (coe du_rest_64 (coe v1) (coe v2) (coe v3) (coe v4) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved.entry∈fns
d_entry'8712'fns_106 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'8712'fns_106 v0 v1 ~v2 v3 = du_entry'8712'fns_106 v0 v1 v3
du_entry'8712'fns_106 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'8712'fns_106 v0 v1 v2
  = case coe v1 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget'45'from_926
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                       (coe v0)
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3)))
                    (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
               -> let v8
                        = coe
                            du_entry'8712'fns_106
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v0)
                               (coe v3))
                            (coe v4) (coe v7) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                              (coe
                                 MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                                 (MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'image_8
                                    (coe v0) (coe v3))
                                 (MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Program.d_fname_16
                                                (coe v3))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Program.d_fdom_18
                                                (coe v3))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Program.d_fcod_20
                                                (coe v3))
                                             (coe (0 :: Integer)) (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Program.d_fbody_22
                                                (coe v3)))))
                                    (coe v4))
                                 v10)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved.Fns.P
d_P_160 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 -> ()
d_P_160 = erased
-- Once.Adequacy.ImageResolved.Fns.closes-FI
d_closes'45'FI_176 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_closes'45'FI_176 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_closes'45'FI_176 v1 v4 v5 v6 v7 v8 v9
du_closes'45'FI_176 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_closes'45'FI_176 v0 v1 v2 v3 v4 v5 v6
  = case coe v3 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v7 v8
        -> case coe v5 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
               -> case coe v6 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v15 v16
                      -> coe
                           MAlonzo.Code.Once.CCC.Codegen.RefsClosed.du_closes'45''43''43'_206
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'image_8 (coe v2)
                              (coe v7))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.RefsClosed.du_closes'45''43''43'_206
                              (coe du_Te_204 (coe v2) (coe v7))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    du_cl_216 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4) (coe v11)
                                    (coe v15)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    du_cl_216 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4) (coe v11)
                                    (coe v15))))
                           (coe
                              du_closes'45'FI_176 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14 (coe v2)
                                 (coe v7))
                              (coe v8)
                              (coe
                                 (\ v17 v18 ->
                                    coe
                                      v4 v17
                                      (coe
                                         MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                                         (MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'image_8
                                            (coe v2) (coe v7))
                                         (MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'next_14
                                               (coe v2) (coe v7))
                                            (coe v8))
                                         v18)))
                              (coe v12) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved.Fns._.Y
d_Y_202 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Y_202 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_Y_202 v5 v6
du_Y_202 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Y_202 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
      (coe (0 :: Integer)) (coe v0)
      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))
-- Once.Adequacy.ImageResolved.Fns._.Te
d_Te_204 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_Te_204 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_Te_204 v5 v6
du_Te_204 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_Te_204 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelScope.du_trace'45'of_114
      (coe du_Y_202 (coe v0) (coe v1))
-- Once.Adequacy.ImageResolved.Fns._.Le
d_Le_206 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_Le_206 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_Le_206 v5 v6
du_Le_206 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_Le_206 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_blocks'45'layout_2352
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_bodies'45'of_1784
         (coe du_Y_202 (coe v0) (coe v1)))
-- Once.Adequacy.ImageResolved.Fns._.unit⊆
d_unit'8838'_210 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_unit'8838'_210 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 v13
  = du_unit'8838'_210 v5 v6 v13
du_unit'8838'_210 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_unit'8838'_210 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.RefsClosed.du_'43''43''45''8838'_142
      (coe du_Te_204 (coe v0) (coe v1)) (coe du_Le_206 (coe v0) (coe v1))
      (coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
              (coe
                 MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                 (coe du_Te_204 (coe v0) (coe v1)) v4)))
      (coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
              (coe
                 MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                 (coe du_Te_204 (coe v0) (coe v1))
                 (coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_proj'45'budget_848
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
                                (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v1))
                                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
                                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
                                (coe (0 :: Integer)) (coe v0)
                                (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))))))
                    (coe du_Le_206 (coe v0) (coe v1)))
                 (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v4))))
      (coe v2)
-- Once.Adequacy.ImageResolved.Fns._.cl
d_cl_216 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cl_216 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7 v8 v9 ~v10 v11 ~v12
  = du_cl_216 v1 v4 v5 v6 v8 v9 v11
du_cl_216 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cl_216 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.RefsClosed.du_close_1062
      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3))
      (coe (0 :: Integer)) (coe v2) (coe v0)
      (coe
         (\ v7 v8 ->
            coe
              v4 v7
              (coe
                 MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                 (MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fn'45'image_8
                    (coe v2) (coe v3))
                 (coe du_unit'8838'_210 v2 v3 v7 v8))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.NodesOK.du_nodes'45'from_338 (coe v1)
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3))
         (coe v5) (coe v6))
-- Once.Adequacy.ImageResolved.Prog.p
d_p_230 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_p_230 v0 v1 ~v2 = du_p_230 v0 v1
du_p_230 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
du_p_230 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_396
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_1070 (coe v0))
      (coe v1)
-- Once.Adequacy.ImageResolved.Prog.rp
d_rp_232 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_rp_232 v0 v1 ~v2 = du_rp_232 v0 v1
du_rp_232 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
du_rp_232 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_rewrite'45'program_1096
      (coe du_p_230 (coe v0) (coe v1))
-- Once.Adequacy.ImageResolved.Prog.eo
d_eo_234 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_eo_234 ~v0 ~v1 ~v2 = du_eo_234
du_eo_234 :: MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
du_eo_234 = coe MAlonzo.Code.Once.Compile.d_entry'45'owner_1164
-- Once.Adequacy.ImageResolved.Prog.D
d_D_236 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_D_236 v0 v1 ~v2 = du_D_236 v0 v1
du_D_236 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_D_236 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ImageWF.d_prog'45'defs_28
      (coe du_p_230 (coe v0) (coe v1))
-- Once.Adequacy.ImageResolved.Prog.ext
d_ext_238 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ext_238 v0 v1 ~v2 = du_ext_238 v0 v1
du_ext_238 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_ext_238 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_prog'45'externs_1160
      (coe
         MAlonzo.Code.Once.Denotation.Program.C_irProgram_396
         (coe MAlonzo.Code.Once.Compile.d_moduleTable_1070 (coe v0))
         (coe v1))
-- Once.Adequacy.ImageResolved.Prog.img
d_img_240 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_img_240 v0 v1 ~v2 = du_img_240 v0 v1
du_img_240 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_img_240 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_image'45'of_1172
      (coe du_p_230 (coe v0) (coe v1))
-- Once.Adequacy.ImageResolved.Prog.G
d_G_242 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_G_242 = erased
-- Once.Adequacy.ImageResolved.Prog.P
d_P_248 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 -> ()
d_P_248 = erased
-- Once.Adequacy.ImageResolved.Prog.inD
d_inD_252 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_inD_252 v0 v1 ~v2 ~v3 v4 = du_inD_252 v0 v1 v4
du_inD_252 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_inD_252 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
         (coe
            MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
            (MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
               (coe du_img_240 (coe v0) (coe v1)))
            v2))
-- Once.Adequacy.ImageResolved.Prog.d-img
d_d'45'img_260 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_d'45'img_260 v0 v1 ~v2 ~v3 v4 ~v5 v6
  = du_d'45'img_260 v0 v1 v4 v6
du_d'45'img_260 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_d'45'img_260 v0 v1 v2 v3
  = coe
      du_inD_252 (coe v0) (coe v1)
      (coe
         du_defd'45'self_12 (coe du_img_240 (coe v0) (coe v1)) (coe v2)
         (coe v3))
-- Once.Adequacy.ImageResolved.Prog.main′
d_main'8242'_266 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_main'8242'_266 v0 v1 ~v2 = du_main'8242'_266 v0 v1
du_main'8242'_266 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_main'8242'_266 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.d_main_394
      (coe du_rp_232 (coe v0) (coe v1))
-- Once.Adequacy.ImageResolved.Prog.X
d_X_268 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_X_268 v0 v1 ~v2 = du_X_268 v0 v1
du_X_268 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_X_268 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_542
      (coe du_eo_234) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe du_main'8242'_266 (coe v0) (coe v1))
-- Once.Adequacy.ImageResolved.Prog.T
d_T_270 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_T_270 v0 v1 ~v2 = du_T_270 v0 v1
du_T_270 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_T_270 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.LabelScope.du_trace'45'of_114
      (coe du_X_268 (coe v0) (coe v1))
-- Once.Adequacy.ImageResolved.Prog.L
d_L_272 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_L_272 v0 v1 ~v2 = du_L_272 v0 v1
du_L_272 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_L_272 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_blocks'45'layout_2352
      (coe
         MAlonzo.Code.Once.CCC.Codegen.SlotBudget.du_bodies'45'of_1784
         (coe du_X_268 (coe v0) (coe v1)))
-- Once.Adequacy.ImageResolved.Prog.LT
d_LT_274 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_LT_274 v0 v1 ~v2 = du_LT_274 v0 v1
du_LT_274 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_LT_274 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link'45'top_2378
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_872
         (coe du_eo_234) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe du_main'8242'_266 (coe v0) (coe v1)))
-- Once.Adequacy.ImageResolved.Prog.FI
d_FI_276 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_FI_276 v0 v1 ~v2 = du_FI_276 v0 v1
du_FI_276 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_FI_276 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
            (coe du_eo_234) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
            (coe du_main'8242'_266 (coe v0) (coe v1))))
      (coe
         MAlonzo.Code.Once.Denotation.Program.d_table_392
         (coe du_rp_232 (coe v0) (coe v1)))
-- Once.Adequacy.ImageResolved.Prog.LT⊆
d_LT'8838'_280 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_LT'8838'_280 v0 v1 ~v2 ~v3 v4 = du_LT'8838'_280 v0 v1 v4
du_LT'8838'_280 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_LT'8838'_280 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
      (coe
         MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
         (coe du_LT_274 (coe v0) (coe v1)) v2)
-- Once.Adequacy.ImageResolved.Prog.FI⊆
d_FI'8838'_286 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_FI'8838'_286 v0 v1 ~v2 ~v3 v4 = du_FI'8838'_286 v0 v1 v4
du_FI'8838'_286 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_FI'8838'_286 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
      (coe
         MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
         (coe du_LT_274 (coe v0) (coe v1)) (coe du_FI_276 (coe v0) (coe v1))
         v2)
-- Once.Adequacy.ImageResolved.Prog.call-G
d_call'45'G_296 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_call'45'G_296 v0 v1 ~v2 v3 v4 v5 v6
  = du_call'45'G_296 v0 v1 v3 v4 v5 v6
du_call'45'G_296 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_call'45'G_296 v0 v1 v2 v3 v4 v5
  = let v6
          = d_linked'45'entry_38
              (coe
                 MAlonzo.Code.Once.Compile.d_rewrite'45'table_1090
                 (coe
                    MAlonzo.Code.Once.Compile.d_tableOfResult_1066
                    (coe
                       MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_816
                       (coe MAlonzo.Code.Once.IR.C_Heap_8)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe
                          MAlonzo.Code.Once.Parser.d_guardDistinct_542
                          (coe
                             MAlonzo.Code.Once.Parser.d_thenExtract_626
                             (coe
                                MAlonzo.Code.Once.Parser.d_sigsAdjacent_554
                                (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                             (coe
                                MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_220
                                (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                                (coe
                                   MAlonzo.Code.Once.Parser.d_sigsFirst_622
                                   (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0)))
                                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))))
              (coe v2) (coe v3) (coe v4) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> let v11
                           = coe
                               du_entry'8712'fns_106
                               (coe
                                  addInt (coe (1 :: Integer))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
                                     (coe du_eo_234) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
                                     (coe du_main'8242'_266 (coe v0) (coe v1))))
                               (coe
                                  MAlonzo.Code.Once.Compile.d_rewrite'45'table_1090
                                  (coe
                                     MAlonzo.Code.Once.Compile.d_tableOfResult_1066
                                     (coe
                                        MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_816
                                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                        (coe
                                           MAlonzo.Code.Once.Parser.d_guardDistinct_542
                                           (coe
                                              MAlonzo.Code.Once.Parser.d_thenExtract_626
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_sigsAdjacent_554
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                    (coe v0))
                                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_220
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_extractAliases_76
                                                    (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_sigsFirst_622
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                       (coe v0)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))))
                               (coe v9) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> coe
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                 (coe
                                    du_d'45'img_260 (coe v0) (coe v1)
                                    (coe du_FI'8838'_286 (coe v0) (coe v1) (coe v13))
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ImageResolved.Prog._.lk
d_lk_352 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lk_352 v0 v1 ~v2 ~v3 ~v4 = du_lk_352 v0 v1
du_lk_352 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lk_352 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.SourceTrace.du_rewrite'45'program'45'linked_234
      (coe du_p_230 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ProgramLinked.du_moduleToProgram'45'linked_2758
         (coe v0))
-- Once.Adequacy.ImageResolved.Prog._.closes-LT
d_closes'45'LT_354 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_closes'45'LT_354 v0 v1 ~v2 v3 ~v4 = du_closes'45'LT_354 v0 v1 v3
du_closes'45'LT_354 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_closes'45'LT_354 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.RefsClosed.du_closes'45''43''43'_206
      (coe du_T_270 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_cl_360 (coe v0) (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe
               MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
               (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_cl_360 (coe v0) (coe v1) (coe v2))))
-- Once.Adequacy.ImageResolved.Prog._._.cl
d_cl_360 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cl_360 v0 v1 ~v2 v3 ~v4 = du_cl_360 v0 v1 v3
du_cl_360 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cl_360 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.RefsClosed.du_close_1062
      (coe du_eo_234) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe du_main'8242'_266 (coe v0) (coe v1)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe du_D_236 (coe v0) (coe v1))
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              du_d'45'img_260 (coe v0) (coe v1)
              (coe
                 du_LT'8838'_280 (coe v0) (coe v1)
                 (coe
                    MAlonzo.Code.Once.CCC.Codegen.RefsClosed.du_'43''43''45''8838'_142
                    (coe du_T_270 (coe v0) (coe v1)) (coe du_L_272 (coe v0) (coe v1))
                    (coe
                       (\ v7 ->
                          coe
                            MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                            (coe du_T_270 (coe v0) (coe v1))))
                    (coe
                       (\ v7 v8 ->
                          coe
                            MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                            (coe du_T_270 (coe v0) (coe v1))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2244))
                               (coe du_L_272 (coe v0) (coe v1)))
                            (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8)))
                    (coe v3) (coe v4)))
              v6))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.NodesOK.du_nodes'45'from_338
         (coe du_call'45'G_296 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe du_main'8242'_266 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe du_lk_352 (coe v0) (coe v1)))
         (coe v2))
-- Once.Adequacy.ImageResolved.Prog._.closes-FI
d_closes'45'FI_376 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_closes'45'FI_376 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_closes'45'FI_376 v0 v1 v5 v6 v7
du_closes'45'FI_376 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_closes'45'FI_376 v0 v1 v2 v3 v4
  = coe
      du_closes'45'FI_176 (coe du_D_236 (coe v0) (coe v1))
      (coe du_call'45'G_296 (coe v0) (coe v1)) (coe v2) (coe v3)
      (coe
         (\ v5 v6 v7 v8 ->
            coe du_d'45'img_260 (coe v0) (coe v1) (coe v4 v5 v6) v8))
-- Once.Adequacy.ImageResolved.Prog._.closes-img
d_closes'45'img_386 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_closes'45'img_386 v0 v1 ~v2 v3 v4
  = du_closes'45'img_386 v0 v1 v3 v4
du_closes'45'img_386 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_closes'45'img_386 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
         (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.RefsClosed.du_closes'45''43''43'_206
         (coe du_LT_274 (coe v0) (coe v1))
         (coe du_closes'45'LT_354 (coe v0) (coe v1) (coe v2))
         (coe
            du_closes'45'FI_376 v0 v1
            (addInt
               (coe (1 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'next'45'label_946
                  (coe du_eo_234) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe (0 :: Integer))
                  (coe du_main'8242'_266 (coe v0) (coe v1))))
            (MAlonzo.Code.Once.Denotation.Program.d_table_392
               (coe du_rp_232 (coe v0) (coe v1)))
            (\ v4 v5 -> coe du_FI'8838'_286 (coe v0) (coe v1) v5)
            (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe du_lk_352 (coe v0) (coe v1)))
            v3))
-- Once.Adequacy.ImageResolved.Prog._.resolved
d_resolved_388 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_resolved_388 v0 v1 ~v2 v3 v4 = du_resolved_388 v0 v1 v3 v4
du_resolved_388 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_resolved_388 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
      (\ v4 v5 -> coe du_flat_396 v5)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_arefs_44
         (coe du_img_240 (coe v0) (coe v1)))
      (coe du_closes'45'img_386 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ImageResolved.Prog._._.flat
d_flat_396 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_flat_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_flat_396 v6
du_flat_396 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_flat_396 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved.prog-resolved
d_prog'45'resolved_410 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_prog'45'resolved_410 v0 v1 ~v2 = du_prog'45'resolved_410 v0 v1
du_prog'45'resolved_410 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_prog'45'resolved_410 v0 v1
  = coe
      du_resolved_388 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Adequacy.ImageWF.du_prog'45'sigops_128 (coe v0)
            (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Adequacy.ImageWF.du_prog'45'sigops_128 (coe v0)
            (coe v1)))
-- Once.Adequacy.ImageResolved.StrMem._∈_
d__'8712'__420 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d__'8712'__420 = erased
-- Once.Adequacy.ImageResolved.StrMem._∈?_
d__'8712''63'__422 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712''63'__422
  = let v0 = MAlonzo.Code.Data.String.Properties.d__'8799'__54 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Once.Adequacy.ImageResolved.StrMem._∉_
d__'8713'__424 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d__'8713'__424 = erased
-- Once.Adequacy.ImageResolved.StrMem._∉?_
d__'8713''63'__426 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8713''63'__426
  = let v0 = MAlonzo.Code.Data.String.Properties.d__'8799'__54 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8713''63'__68
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Once.Adequacy.ImageResolved.StrMem._∷=_
d__'8759''61'__428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d__'8759''61'__428
  = coe MAlonzo.Code.Data.List.Membership.Setoid.du__'8759''61'__52
-- Once.Adequacy.ImageResolved.StrMem._≢∈_
d__'8802''8712'__430 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> ()
d__'8802''8712'__430 = erased
-- Once.Adequacy.ImageResolved.StrMem._─_
d__'9472'__432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d__'9472'__432
  = coe MAlonzo.Code.Data.List.Membership.Setoid.du__'9472'__54
-- Once.Adequacy.ImageResolved.StrMem.find
d_find_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find_434 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_find_86
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      v2 v3
-- Once.Adequacy.ImageResolved.StrMem.lose
d_lose_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lose_436 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Membership.Propositional.du_lose_50 v2 v3
-- Once.Adequacy.ImageResolved.StrMem.mapWith∈
d_mapWith'8712'_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny) ->
  [AgdaAny]
d_mapWith'8712'_438 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_mapWith'8712'_64
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      v2 v3
-- Once.Adequacy.ImageResolved.Lib.tbl
d_tbl_444 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tbl_444 v0
  = coe MAlonzo.Code.Once.Compile.d_moduleTable_1070 (coe v0)
-- Once.Adequacy.ImageResolved.Lib.lp
d_lp_446 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_lp_446 v0
  = coe
      MAlonzo.Code.Once.Compile.d_lib'45'program_1220
      (coe d_tbl_444 (coe v0))
-- Once.Adequacy.ImageResolved.Lib.rt
d_rt_448 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_rt_448 v0
  = coe
      MAlonzo.Code.Once.Compile.d_rewrite'45'table_1090
      (coe d_tbl_444 (coe v0))
-- Once.Adequacy.ImageResolved.Lib.D
d_D_450 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_D_450 v0
  = coe MAlonzo.Code.Once.Adequacy.ImageWF.d_lib'45'defs_32 (coe v0)
-- Once.Adequacy.ImageResolved.Lib.ext
d_ext_452 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ext_452 v0
  = coe
      MAlonzo.Code.Once.Compile.d_externs'45'of_1156
      (coe d_lp_446 (coe v0))
-- Once.Adequacy.ImageResolved.Lib.σ
d_σ_454 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_σ_454 v0
  = coe MAlonzo.Code.Once.Lang.Module.d_moduleSig_134 (coe v0)
-- Once.Adequacy.ImageResolved.Lib.G
d_G_456 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_G_456 = erased
-- Once.Adequacy.ImageResolved.Lib.inD
d_inD_462 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_inD_462 v0 ~v1 v2 = du_inD_462 v0 v2
du_inD_462 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_inD_462 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
      (coe
         MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
         (MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'image_1216
               (coe d_tbl_444 (coe v0))))
         v1)
-- Once.Adequacy.ImageResolved.Lib.ce-linked
d_ce'45'linked_472 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ce'45'linked_472 v0 v1 ~v2 v3 ~v4 = du_ce'45'linked_472 v0 v1 v3
du_ce'45'linked_472 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ce'45'linked_472 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             MAlonzo.Code.Once.Adequacy.ProgramLinked.d_link'45'walk_2354
             (coe
                MAlonzo.Code.Once.Lang.Module.d_moduleSig'45'ef_130
                (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v1)))
             (coe
                MAlonzo.Code.Once.Compile.C_cscope_410
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   MAlonzo.Code.Once.Compile.d_cimps_406
                   (coe MAlonzo.Code.Once.Compile.d_emptyCScope_412))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe v1) (coe du_mt_492 (coe v1) (coe v3))
             (coe du_b_490 (coe v1) (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Once.Adequacy.ProgramLinked.du_linv'8320'_2718)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Adequacy.TelePosition.du_entries'45'distinct_466
                   (coe v0) (coe v1))
                (coe
                   MAlonzo.Code.Once.Adequacy.TelePosition.d_none'45'in'45'empty_478
                   (coe
                      MAlonzo.Code.Data.List.Base.du_map_22
                      (coe MAlonzo.Code.Once.Adequacy.TelePosition.d_entryName_94)
                      (coe v1))))
             (coe (\ v4 v5 -> v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved.Lib._.b
d_b_490 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12
d_b_490 ~v0 v1 ~v2 v3 ~v4 = du_b_490 v1 v3
du_b_490 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12
du_b_490 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.FunBundle.du_ce'45'bundle_880
      (coe MAlonzo.Code.Once.Compile.d_emptyCScope_412) (coe v0) (coe v1)
-- Once.Adequacy.ImageResolved.Lib._.mt
d_mt_492 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50
d_mt_492 ~v0 v1 ~v2 v3 ~v4 = du_mt_492 v1 v3
du_mt_492 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50
du_mt_492 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.AcceptSound.du_ce'45'sound_294
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Once.Compile.d_emptyCScope_412) (coe v0) (coe v1)
-- Once.Adequacy.ImageResolved.Lib._.u
d_u_496 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_u_496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_u_496 v6
du_u_496 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_u_496 v0 = coe v0
-- Once.Adequacy.ImageResolved.Lib.ef-linked
d_ef'45'linked_512 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ef'45'linked_512 v0 v1 ~v2 = du_ef'45'linked_512 v0 v1
du_ef'45'linked_512 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ef'45'linked_512 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             du_ce'45'linked_472 (coe v0) (coe v2)
             (coe
                MAlonzo.Code.Once.Compile.d_compileEntries_506
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Once.Compile.d_emptyCScope_412) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved.Lib.table-linked
d_table'45'linked_520 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_table'45'linked_520 v0
  = coe
      du_ef'45'linked_512 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_632
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
         (coe v0))
-- Once.Adequacy.ImageResolved.Lib.rt-linked
d_rt'45'linked_524 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rt'45'linked_524 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.du_rewrite'45'program'45'linked_234
         (coe d_lp_446 (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe d_table'45'linked_520 (coe v0))))
-- Once.Adequacy.ImageResolved.Lib.call-G
d_call'45'G_532 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_call'45'G_532 v0 v1 v2 v3 v4
  = let v5
          = d_linked'45'entry_38
              (coe
                 MAlonzo.Code.Once.Compile.d_rewrite'45'table_1090
                 (coe
                    MAlonzo.Code.Once.Compile.d_tableOfResult_1066
                    (coe
                       MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_816
                       (coe MAlonzo.Code.Once.IR.C_Heap_8)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe
                          MAlonzo.Code.Once.Parser.d_guardDistinct_542
                          (coe
                             MAlonzo.Code.Once.Parser.d_thenExtract_626
                             (coe
                                MAlonzo.Code.Once.Parser.d_sigsAdjacent_554
                                (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                             (coe
                                MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_220
                                (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                                (coe
                                   MAlonzo.Code.Once.Parser.d_sigsFirst_622
                                   (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0)))
                                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))))
              (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> let v10
                           = coe
                               du_entry'8712'fns_106 (coe (0 :: Integer))
                               (coe
                                  MAlonzo.Code.Once.Compile.d_rewrite'45'table_1090
                                  (coe
                                     MAlonzo.Code.Once.Compile.d_tableOfResult_1066
                                     (coe
                                        MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_816
                                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                        (coe
                                           MAlonzo.Code.Once.Parser.d_guardDistinct_542
                                           (coe
                                              MAlonzo.Code.Once.Parser.d_thenExtract_626
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_sigsAdjacent_554
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                    (coe v0))
                                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_220
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_extractAliases_76
                                                    (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_sigsFirst_622
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                       (coe v0)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))))
                               (coe v8) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                            -> coe
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                 (coe
                                    du_inD_462 (coe v0)
                                    (coe
                                       du_defd'45'self_12
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_lib'45'image_1216
                                          (coe d_tbl_444 (coe v0)))
                                       (coe v12)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                          erased)))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ImageResolved.Lib.calls-ok
d_calls'45'ok_578 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_calls'45'ok_578 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266
      (MAlonzo.Code.Once.Compile.d_calls'45'of_1140
         (coe
            MAlonzo.Code.Once.Compile.d_rewrite'45'program_1096
            (coe d_lp_446 (coe v0))))
      (\ v1 v2 ->
         coe
           du_split_586 (coe v0) (coe v2)
           (coe
              MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                 (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
              (coe v1)
              (coe
                 MAlonzo.Code.Once.Compile.d_block'45'syms_1134
                 (coe
                    MAlonzo.Code.Once.Compile.d_program'45'blocks_1100
                    (coe d_lp_446 (coe v0))))))
-- Once.Adequacy.ImageResolved.Lib._.split
d_split_586 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_split_586 v0 ~v1 v2 v3 = du_split_586 v0 v2 v3
du_split_586 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_split_586 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                              (coe
                                 MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                                 (MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_lib'45'image_1216
                                       (coe d_tbl_444 (coe v0))))
                                 (MAlonzo.Code.Once.Compile.d_block'45'syms_1134
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_program'45'blocks_1100
                                       (coe d_lp_446 (coe v0))))
                                 v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'filter'8314'_510
                          (MAlonzo.Code.Once.Compile.d_is'45'extern'63'_1150
                             (coe d_lp_446 (coe v0)))
                          (MAlonzo.Code.Once.Compile.d_calls'45'of_1140
                             (coe
                                MAlonzo.Code.Once.Compile.d_rewrite'45'program_1096
                                (coe d_lp_446 (coe v0))))
                          v1 erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved.Lib.tbl-leaves
d_tbl'45'leaves_610 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_tbl'45'leaves_610 ~v0 v1 v2 = du_tbl'45'leaves_610 v1 v2
du_tbl'45'leaves_610 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_tbl'45'leaves_610 v0 v1
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
                du_tbl'45'leaves_610 (coe v3)
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
-- Once.Adequacy.ImageResolved.Lib.sl-tbl
d_sl'45'tbl_622 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sl'45'tbl_622 v0
  = coe
      du_tbl'45'leaves_610 (coe d_rt_448 (coe v0))
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
                  (coe
                     MAlonzo.Code.Once.Compile.d_rewrite'45'program_1096
                     (coe d_lp_446 (coe v0)))))
            (coe d_calls'45'ok_578 (coe v0))))
-- Once.Adequacy.ImageResolved.Lib.resolved
d_resolved_624 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_resolved_624 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
      (\ v1 v2 -> coe du_flat_632 v2)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_arefs_44
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
            (coe (0 :: Integer)) (coe d_rt_448 (coe v0))))
      (coe
         du_closes'45'FI_176 (coe d_D_450 (coe v0))
         (coe d_call'45'G_532 (coe v0)) (coe (0 :: Integer))
         (coe d_rt_448 (coe v0))
         (coe
            (\ v1 v2 v3 v4 ->
               coe
                 du_inD_462 (coe v0)
                 (coe
                    du_defd'45'self_12
                    (coe
                       MAlonzo.Code.Once.Compile.d_lib'45'image_1216
                       (coe d_tbl_444 (coe v0)))
                    (coe v2) (coe v4))))
         (coe d_rt'45'linked_524 (coe v0)) (coe d_sl'45'tbl_622 (coe v0)))
-- Once.Adequacy.ImageResolved.Lib._.flat
d_flat_632 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_flat_632 ~v0 ~v1 v2 = du_flat_632 v2
du_flat_632 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_flat_632 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageResolved.lib-resolved
d_lib'45'resolved_646 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_lib'45'resolved_646 = coe d_resolved_624
