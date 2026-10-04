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

module MAlonzo.Code.Once.CCC.Codegen.NodesOK where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.NodesOK.sigop-syms
d_sigop'45'syms_12 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_sigop'45'syms_12 ~v0 ~v1 v2 v3 = du_sigop'45'syms_12 v2 v3
du_sigop'45'syms_12 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_sigop'45'syms_12 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
                (coe
                   MAlonzo.Code.Once.SigOp.Info.d_name_178
                   (coe
                      MAlonzo.Code.Once.Arith.SigOp.Compare.d_cmp'45'block'45'info_24
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v0)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.NodesOK.SigLeaves
d_SigLeaves_28 ::
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> ()) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_SigLeaves_28 = erased
-- Once.CCC.Codegen.NodesOK._.NodesOK
d_NodesOK_102 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_NodesOK_102 = erased
-- Once.CCC.Codegen.NodesOK._.nodes-from
d_nodes'45'from_144 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny -> AgdaAny
d_nodes'45'from_144 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_nodes'45'from_144 v3 v4 v5 v6 v7 v8
du_nodes'45'from_144 ::
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny -> AgdaAny
du_nodes'45'from_144 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_nodes'45'from_144 (coe v0) (coe v7) (coe v2) (coe v9) (coe v11)
                              (coe v13))
                           (coe
                              du_nodes'45'from_144 (coe v0) (coe v1) (coe v7) (coe v10) (coe v12)
                              (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_nodes'45'from_144 (coe v0) (coe v1) (coe v11) (coe v9)
                                     (coe v13) (coe v15))
                                  (coe
                                     du_nodes'45'from_144 (coe v0) (coe v1) (coe v12) (coe v10)
                                     (coe v14) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_case_68 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_nodes'45'from_144 (coe v0) (coe v11) (coe v2) (coe v9)
                                     (coe v13) (coe v15))
                                  (coe
                                     du_nodes'45'from_144 (coe v0) (coe v12) (coe v2) (coe v10)
                                     (coe v14) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_curry_84 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
               -> coe
                    du_nodes'45'from_144 (coe v0)
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                    (coe v11) (coe v9) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_In_94 v7
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v7
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           du_nodes'45'from_144 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13) (coe v2)))
                           (coe v2) (coe v10) (coe v4) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v7
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v7
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_Ana_120 v7 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
               -> coe
                    du_nodes'45'from_144 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v1))
                    (coe v9) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v7 v8
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_SigOp_130 v6 v7 v8 -> coe v5
      MAlonzo.Code.Once.IR.C_Call_136 v8 -> coe v0 v8 v1 v2 v4
      _ -> MAlonzo.RTE.mazUnreachableError
