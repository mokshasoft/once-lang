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

module MAlonzo.Code.Once.Adequacy.TeleWalk where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.TelePosition
import qualified MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Core.AbsTy
import qualified MAlonzo.Code.Once.Spec.Core.Meaning
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTyping
import qualified MAlonzo.Code.Once.Spec.Core.Telescope
import qualified MAlonzo.Code.Once.Spec.Core.Translate
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.TeleWalk.ι
d_ι_12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_ι_12 ~v0 v1 v2 = du_ι_12 v1 v2
du_ι_12 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
du_ι_12 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_468 (coe v0)
      (coe v1)
-- Once.Adequacy.TeleWalk.φ
d_φ_14 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_φ_14 ~v0 v1 v2 = du_φ_14 v1 v2
du_φ_14 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
du_φ_14 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_540
      (coe du_ι_12 (coe v0) (coe v1))
-- Once.Adequacy.TeleWalk._.Inv
d_Inv_68 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.TeleWalk._.NS
d_NS_72 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 -> ()
d_NS_72 = erased
-- Once.Adequacy.TeleWalk._.Inv.irf
d_irf_100 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
d_irf_100 v0
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.d_irf_126 (coe v0)
-- Once.Adequacy.TeleWalk._.Inv.irs
d_irs_102 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
d_irs_102 v0
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.d_irs_128 (coe v0)
-- Once.Adequacy.TeleWalk._.Inv.iself
d_iself_104 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_iself_104 v0
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.d_iself_130 (coe v0)
-- Once.Adequacy.TeleWalk._.Inv.rel
d_rel_106 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rel_106 v0
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.d_rel_138 (coe v0)
-- Once.Adequacy.TeleWalk._.MonoStep.Dc
d_Dc_110 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_Dc_110 ~v0 v1 ~v2 = du_Dc_110 v1
du_Dc_110 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_Dc_110 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_Dc_432 (coe v0) v1
      v2 v3 v5 v6 v7 v10 v11 v13
-- Once.Adequacy.TeleWalk._.MonoStep.M
d_M_114 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_M_114 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        v17 v18
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_M_444 (coe v0)
      (coe v1) (coe v2) v10 v13 v16
-- Once.Adequacy.TeleWalk._.MonoStep.bodyD
d_bodyD_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
d_bodyD_120 ~v0 v1 ~v2 = du_bodyD_120 v1
du_bodyD_120 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
du_bodyD_120 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_bodyD_418 (coe v0)
      v1 v2 v3 v5 v6 v7 v10 v11 v13
-- Once.Adequacy.TeleWalk._.MonoStep.e
d_e_132 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_132 ~v0 ~v1 ~v2 = du_e_132
du_e_132 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_132 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_e_424 v9 v10 v13
-- Once.Adequacy.TeleWalk._.MonoStep.δ
d_δ_146 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
d_δ_146 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        v17 v18
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_δ_412 (coe v0)
      (coe v1) (coe v2) v3 v4 v6
-- Once.Adequacy.TeleWalk.RunAt
d_RunAt_154 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_RunAt_154 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_868
      (coe du_ι_12 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
            (coe du_φ_14 (coe v1) (coe v2)) (coe v3))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe MAlonzo.Code.Once.Type.C_Unit_120))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe MAlonzo.Code.Once.Type.C_Unit_120))
         (coe MAlonzo.Code.Once.Compile.d_mainCall_814)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe v4)
-- Once.Adequacy.TeleWalk.K-subst
d_K'45'subst_168 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_K'45'subst_168 = erased
-- Once.Adequacy.TeleWalk.skip-later
d_skip'45'later_186 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'later_186 = erased
-- Once.Adequacy.TeleWalk.later-not-main
d_later'45'not'45'main_214 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_later'45'not'45'main_214 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_later'45'not'45'main_214 v4 v5 v6
du_later'45'not'45'main_214 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_later'45'not'45'main_214 v0 v1 v2
  = coe
      du_un_230
      (coe
         MAlonzo.Code.Once.Compile.d_tableOf'45'go_856
         (coe
            MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_332
            (coe v0) (coe v1))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_later'45'ns_902
         (coe v0) (coe v1) (coe du_mainImps_224)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
            (coe
               (\ v3 v4 ->
                  coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (\ v5 -> coe v4 erased)
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
            (coe
               MAlonzo.Code.Data.List.Base.du_map_22
               (coe MAlonzo.Code.Once.Adequacy.TelePosition.d_entryName_64)
               (coe v0))
            (coe v2))
         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
-- Once.Adequacy.TeleWalk._.mainImps
d_mainImps_224 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_mainImps_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_mainImps_224
du_mainImps_224 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_mainImps_224
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("main" :: Data.Text.Text))
         (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_188))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.TeleWalk._.un
d_un_230 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_un_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 = du_un_230 v7 v8
du_un_230 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_un_230 v0 v1
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
                           seq (coe v11)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v10
                              (coe du_un_230 (coe v3) (coe v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.from-sem
d_from'45'sem_270 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_from'45'sem_270 = erased
-- Once.Adequacy.TeleWalk.here-main
d_here'45'main_428 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_here'45'main_428 = erased
-- Once.Adequacy.TeleWalk._._.Dc
d_Dc_478 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_Dc_478 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
         v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_Dc_478 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_Dc_478 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_Dc_478 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_Dc_432 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Parser.C_mkFunInfo_114
         (coe ("main" :: Data.Text.Text)) (coe v7) (coe v8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_188) (coe v9)
-- Once.Adequacy.TeleWalk._._.M
d_M_482 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_M_482 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
        ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_M_482 v0 v1 v2 v10 v16
du_M_482 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_M_482 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_M_444 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_188) (coe v4)
-- Once.Adequacy.TeleWalk._._.bodyD
d_bodyD_488 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
d_bodyD_488 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_bodyD_488 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyD_488 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
du_bodyD_488 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_bodyD_418 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Parser.C_mkFunInfo_114
         (coe ("main" :: Data.Text.Text)) (coe v7) (coe v8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_188) (coe v9)
-- Once.Adequacy.TeleWalk._._.e
d_e_500 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer -> MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_500 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
        ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_e_500 v12 v13 v16
du_e_500 ::
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_500 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_e_424
      (coe
         MAlonzo.Code.Once.Parser.C_mkFunInfo_114
         (coe ("main" :: Data.Text.Text)) (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_188) (coe v2)
-- Once.Adequacy.TeleWalk._._.δ
d_δ_514 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
d_δ_514 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
        ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_δ_514 v0 v1 v2 v3 v4 v6
du_δ_514 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
du_δ_514 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_δ_412 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.TeleWalk._.later
d_later_522 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_later_522 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24
  = du_later_522 v18 v20
du_later_522 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_later_522 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_tableOf'45'go_856
      (coe
         MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_332
         (coe v0) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.TeleWalk._.ir-side
d_ir'45'side_526 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'side_526 = erased
-- Once.Adequacy.TeleWalk._.core≡
d_core'8801'_532 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_core'8801'_532 = erased
-- Once.Adequacy.TeleWalk.walk
d_walk_570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_walk_570 = erased
-- Once.Adequacy.TeleWalk.walk-mono
d_walk'45'mono_620 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_walk'45'mono_620 = erased
-- Once.Adequacy.TeleWalk.walk-mono-d
d_walk'45'mono'45'd_674 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_94 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_walk'45'mono'45'd_674 = erased
