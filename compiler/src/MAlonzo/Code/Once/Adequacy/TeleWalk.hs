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
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.GradedRelation
import qualified MAlonzo.Code.Once.Adequacy.TableCall
import qualified MAlonzo.Code.Once.Adequacy.TelePosition
import qualified MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.EvalRel
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.Core.AbsTy
import qualified MAlonzo.Code.Once.Lang.Core.Abstract
import qualified MAlonzo.Code.Once.Lang.Core.Meaning
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.PolyTyping
import qualified MAlonzo.Code.Once.Lang.Core.Schema
import qualified MAlonzo.Code.Once.Lang.Core.Telescope
import qualified MAlonzo.Code.Once.Lang.Core.Translate
import qualified MAlonzo.Code.Once.Lang.Core.Typing
import qualified MAlonzo.Code.Once.Lang.Elaboration
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Instance
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.TeleWalk.ι
d_ι_12 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
d_ι_12 ~v0 v1 v2 = du_ι_12 v1 v2
du_ι_12 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
du_ι_12 v0 v1
  = coe MAlonzo.Code.Once.Lang.Trace.C_interp_192 (coe v0) (coe v1)
-- Once.Adequacy.TeleWalk.φ
d_φ_14 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8
d_φ_14 ~v0 v1 v2 = du_φ_14 v1 v2
du_φ_14 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8
du_φ_14 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262
      (coe du_ι_12 (coe v0) (coe v1))
-- Once.Adequacy.TeleWalk._.Inv
d_Inv_38 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.TeleWalk._.NS
d_NS_42 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 -> ()
d_NS_42 = erased
-- Once.Adequacy.TeleWalk._.Inv.irf
d_irf_66 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_irf_66 v0
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.d_irf_152 (coe v0)
-- Once.Adequacy.TeleWalk._.Inv.irs
d_irs_68 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_irs_68 v0
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.d_irs_154 (coe v0)
-- Once.Adequacy.TeleWalk._.Inv.iself
d_iself_70 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_iself_70 v0
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.d_iself_156 (coe v0)
-- Once.Adequacy.TeleWalk._.Inv.rel
d_rel_72 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rel_72 v0
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.d_rel_164 (coe v0)
-- Once.Adequacy.TeleWalk._.MonoStep.Dc
d_Dc_76 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_Dc_76 ~v0 v1 ~v2 = du_Dc_76 v1
du_Dc_76 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_Dc_76 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_Dc_458 (coe v0) v1
      v2 v3 v5 v6 v7 v10 v11 v13
-- Once.Adequacy.TeleWalk._.MonoStep.bodyD
d_bodyD_86 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
d_bodyD_86 ~v0 v1 ~v2 = du_bodyD_86 v1
du_bodyD_86 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
du_bodyD_86 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_bodyD_444 (coe v0)
      v1 v2 v3 v5 v6 v7 v10 v11 v13
-- Once.Adequacy.TeleWalk._.MonoStep.e
d_e_98 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_98 ~v0 ~v1 ~v2 = du_e_98
du_e_98 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_98 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_e_450 v9 v10 v13
-- Once.Adequacy.TeleWalk._.MonoStep.δ
d_δ_112 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ_112 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
        v17 v18
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_δ_438 (coe v0)
      (coe v1) (coe v2) v3 v4 v6
-- Once.Adequacy.TeleWalk.Agree
d_Agree_120 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100 -> ()
d_Agree_120 = erased
-- Once.Adequacy.TeleWalk.ret-inv
d_ret'45'inv_136 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  AgdaAny
d_ret'45'inv_136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_ret'45'inv_136 v8
du_ret'45'inv_136 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  AgdaAny
du_ret'45'inv_136 v0
  = coe
      du_inv_154
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
         (coe v0))
-- Once.Adequacy.TeleWalk._.inv
d_inv_154 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  AgdaAny
d_inv_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 v14
  = du_inv_154 v14
du_inv_154 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  AgdaAny
du_inv_154 v0
  = case coe v0 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.K-subst
d_K'45'subst_166 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_K'45'subst_166 = erased
-- Once.Adequacy.TeleWalk.skip-later
d_skip'45'later_184 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'later_184 = erased
-- Once.Adequacy.TeleWalk.later-not-main
d_later'45'not'45'main_212 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_later'45'not'45'main_212 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_later'45'not'45'main_212 v4 v5 v6
du_later'45'not'45'main_212 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_later'45'not'45'main_212 v0 v1 v2
  = coe
      du_un_228
      (coe
         MAlonzo.Code.Once.Compile.d_tableOf'45'go_1066
         (coe
            MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_348
            (coe v0) (coe v1))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_later'45'ns_902
         (coe v0) (coe v1) (coe du_mainImps_222)
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
d_mainImps_222 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_mainImps_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_mainImps_222
du_mainImps_222 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_mainImps_222
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("main" :: Data.Text.Text))
         (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.TeleWalk._.un
d_un_228 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_un_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 = du_un_228 v7 v8
du_un_228 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_un_228 v0 v1
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
                              (coe du_un_228 (coe v3) (coe v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.from-sem
d_from'45'sem_266 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_from'45'sem_266 = erased
-- Once.Adequacy.TeleWalk.here-main
d_here'45'main_420 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_here'45'main_420 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13
                   ~v14 v15 v16 ~v17 v18 ~v19 v20 v21 ~v22 ~v23
  = du_here'45'main_420
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18 v20 v21
du_here'45'main_420 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_here'45'main_420 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.d_GM'45'D_1246 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38)
      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
      (coe
         MAlonzo.Code.Once.Lang.Core.Meaning.du_'10214'_'10215'_502 v1
         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
         (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v1)
               (coe v3) (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                  (coe MAlonzo.Code.Once.Compile.d_cimps_442 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                     (coe
                        MAlonzo.Code.Once.Compile.d_telePolys_454
                        (MAlonzo.Code.Once.Compile.d_ctele_444 (coe v5))))
                  (coe MAlonzo.Code.Once.Compile.d_csig_440 (coe v5)))
               (coe v12) (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe
                  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_V_456 (coe v5)
                  (coe v7) (coe v8) (coe v9))
               (coe v13)))
         MAlonzo.Code.Once.Lang.Module.d_EffUU_150
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v1)
               (coe v3) (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                  (coe MAlonzo.Code.Once.Compile.d_cimps_442 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                     (coe
                        MAlonzo.Code.Once.Compile.d_telePolys_454
                        (MAlonzo.Code.Once.Compile.d_ctele_444 (coe v5))))
                  (coe MAlonzo.Code.Once.Compile.d_csig_440 (coe v5)))
               (coe v12) (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe
                  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_V_456 (coe v5)
                  (coe v7) (coe v8) (coe v9))
               (coe v13)))
         v0
         (coe
            MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_δ_438 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
         (coe
            MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_M_470 (coe v0)
            (coe v1) (coe v2) (coe v10)
            (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150) (coe v14))
         (coe
            (\ v18 -> coe v18 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (coe
         MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
         (coe du_φ_14 (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Once.Compile.d_tableOf'45'go_1066
            (coe
               MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_348
               (coe v15) (coe v16))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Compile.d_irFunOf_1056
                  (coe
                     MAlonzo.Code.Once.Compile.C_mkCompiledFun_312
                     (coe
                        MAlonzo.Code.Once.Spec.Name.d_bare_14
                        (coe ("main" :: Data.Text.Text)))
                     (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150) (coe v14)))
               (coe v10)))
         (coe
            MAlonzo.Code.Once.Spec.Name.d_bare_14
            (coe ("main" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_ret'45'inv_136
            (coe
               MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_relM_480 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
               (coe v8) (coe v9) (coe v10)
               (coe
                  MAlonzo.Code.Once.Parser.C_mkFunInfo_114
                  (coe ("main" :: Data.Text.Text)) (coe v11) (coe v12)
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
               (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150) (coe v13) (coe v14)
               (coe v17)))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
         (coe
            MAlonzo.Code.Once.Adequacy.TableCall.du_uncurry'45'app_248 (coe v0)
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
            (coe
               MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
               (coe du_φ_14 (coe v1) (coe v2)) (coe v10))
            (coe v14)
            (coe
               MAlonzo.Code.Once.Denotation.EvalRel.du_E'8242'_348 v0
               (coe
                  MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
                     (coe du_φ_14 (coe v1) (coe v2)) (coe v10))
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
                     (coe
                        MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
                        (coe du_φ_14 (coe v1) (coe v2)) (coe v10))))
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150))
               v14 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
            (coe
               MAlonzo.Code.Once.Denotation.EvalRel.d_eval'45'rel_392 v0
               (coe
                  MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
                     (coe du_φ_14 (coe v1) (coe v2)) (coe v10))
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
                     (coe
                        MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
                        (coe du_φ_14 (coe v1) (coe v2)) (coe v10))))
               (coe
                  MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
                  (coe
                     MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
                     (coe du_φ_14 (coe v1) (coe v2)) (coe v10))
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
                     (coe
                        MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
                        (coe du_φ_14 (coe v1) (coe v2)) (coe v10))))
               (MAlonzo.Code.Once.Denotation.EvalRel.d_table'45'self_656
                  (coe v0) (coe du_φ_14 (coe v1) (coe v2)) (coe v10))
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150))
               v14 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Once.Adequacy.TeleWalk._._.Dc
d_Dc_468 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_Dc_468 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
         v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_Dc_468 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_Dc_468 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_Dc_468 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_Dc_458 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Parser.C_mkFunInfo_114
         (coe ("main" :: Data.Text.Text)) (coe v7) (coe v8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150) (coe v9)
-- Once.Adequacy.TeleWalk._._.bodyD
d_bodyD_478 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
d_bodyD_478 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_bodyD_478 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyD_478 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
du_bodyD_478 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_bodyD_444 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Parser.C_mkFunInfo_114
         (coe ("main" :: Data.Text.Text)) (coe v7) (coe v8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150) (coe v9)
-- Once.Adequacy.TeleWalk._._.e
d_e_490 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
        ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_e_490 v12 v13 v16
du_e_490 ::
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_490 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_e_450
      (coe
         MAlonzo.Code.Once.Parser.C_mkFunInfo_114
         (coe ("main" :: Data.Text.Text)) (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150) (coe v2)
-- Once.Adequacy.TeleWalk._._.δ
d_δ_504 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ_504 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
        ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_δ_504 v0 v1 v2 v3 v4 v6
du_δ_504 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
du_δ_504 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_δ_438 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.TeleWalk._.later
d_later_512 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_later_512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20 ~v21 ~v22 ~v23
  = du_later_512 v18 v20
du_later_512 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_later_512 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_tableOf'45'go_1066
      (coe
         MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_348
         (coe v0) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.TeleWalk._.ir-tree
d_ir'45'tree_514 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'tree_514 = erased
-- Once.Adequacy.TeleWalk._.core≡
d_core'8801'_518 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_core'8801'_518 = erased
-- Once.Adequacy.TeleWalk._.core-eq
d_core'45'eq_522 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_core'45'eq_522 = erased
-- Once.Adequacy.TeleWalk.walk
d_walk_556 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_walk_556 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Module.C_ffi_64 v21 v25 v26 v27 v28
        -> case coe v4 of
             (:) v29 v30
               -> case coe v29 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v31
                      -> case coe v6 of
                           MAlonzo.Code.Once.Adequacy.FunBundle.C_bffi_32 v34 v36 v37 v38 v44
                             -> coe
                                  d_walk_556 (coe v0) (coe v1) (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Compile.C_cscope_446
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v31))
                                           (coe v21))
                                        (coe MAlonzo.Code.Once.Compile.d_csig_440 (coe v3)))
                                     (coe MAlonzo.Code.Once.Compile.d_cimps_442 (coe v3))
                                     (coe MAlonzo.Code.Once.Compile.d_ctele_444 (coe v3)))
                                  (coe v30) (coe v28) (coe v44) (coe v7) (coe v8) (coe v9) (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Translate.C_s'45'ffi_76 v26 v27
                                     (coe
                                        v17
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v31))
                                           (coe v21))
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                           erased))
                                     v11)
                                  (coe v12) (coe v13) (coe v14) (coe v15)
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_inv'45'sig_290
                                     (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v31))
                                     (coe v27) (coe v16))
                                  (coe
                                     (\ v45 v46 ->
                                        coe
                                          v17 v45
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                             v46)))
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'sig_292
                                     (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_78 v21 v22 v24 v29 v30 v31
        -> case coe v4 of
             (:) v32 v33
               -> case coe v32 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v34
                      -> case coe v34 of
                           MAlonzo.Code.Once.Parser.C_mkFunInfo_114 v35 v36 v37 v38
                             -> coe
                                  seq (coe v24)
                                  (case coe v6 of
                                     MAlonzo.Code.Once.Adequacy.FunBundle.C_bcons_70 v42 v43 v44 v45 v46 v47 v48 v53 v57
                                       -> coe
                                            seq (coe v44)
                                            (coe
                                               du_walk'45'mono_610 (coe v0) (coe v1) (coe v2)
                                               (coe v3) (coe v33) (coe v35) (coe v36) (coe v37)
                                               (coe v22) (coe v29) (coe v30) (coe v31) (coe v48)
                                               (coe v57) (coe v7) (coe v8) (coe v9) (coe v10)
                                               (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                                               (coe v16) (coe v17) (coe v18))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_88 v22 v24 v25
        -> case coe v4 of
             (:) v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v28
                      -> coe
                           seq (coe v22)
                           (case coe v6 of
                              MAlonzo.Code.Once.Adequacy.FunBundle.C_bpoly_90 v32 v33 v34 v35 v38
                                -> coe
                                     d_walk_556 (coe v0) (coe v1) (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Compile.C_cscope_446
                                        (coe MAlonzo.Code.Once.Compile.d_csig_440 (coe v3))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Module.d_imps_16
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                              (coe v3)))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v28)
                                              (coe MAlonzo.Code.Once.Compile.d_ctop_450 (coe v3)))
                                           (coe MAlonzo.Code.Once.Compile.d_ctele_444 (coe v3))))
                                     (coe v27) (coe v25) (coe v38) (coe v7)
                                     (coe addInt (coe (1 :: Integer)) (coe v8))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v9
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.PolyTy.C_schema_822
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Instance.d_arityOf_88
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v28)))
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Schema.d_kindsOf_352
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v28)))
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.AbsTy.d_absTy_82
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.Instance.d_arityOf_88
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_pfunType_126
                                                    (coe v28)))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Core.Schema.d_kindsOf_352
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_pfunType_126
                                                    (coe v28)))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_pfunType_126
                                                    (coe v28))))))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Telescope.C_def_28 v10
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Abstract.du_absTm_744
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Core.Schema.d_schemaOf_394
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_pfunType_126
                                                    (coe v28))))
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Schema.d_kindsOf_352
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v28)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Core.Translate.d_polyElab_700
                                                 (coe v1) (coe v8) (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                                    (coe v3))
                                                 (coe v28)
                                                 (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                                 (coe v11) (coe v12) (coe v13) (coe v24))))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Translate.du_polyBody_720
                                           (coe v1) (coe v8) (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                              (coe v3))
                                           (coe v28)
                                           (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                           (coe v11) (coe v12) (coe v13) (coe v24)))
                                     (coe v11)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Translate.du_wkI_138
                                        (coe
                                           MAlonzo.Code.Once.Lang.Module.d_imps_16
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                              (coe v3)))
                                        (coe v12))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Translate.C_t'45'def_126
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Translate.du_wkT_156
                                           (coe
                                              MAlonzo.Code.Data.List.Base.du_map_22
                                              (coe
                                                 (\ v39 ->
                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe v39)))
                                              (coe MAlonzo.Code.Once.Compile.d_ctele_444 (coe v3)))
                                           (coe v13)))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Translate.du_polySg_672
                                        (coe v14) (coe v28))
                                     (coe v15)
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_inv'45'poly_666
                                        v0 v1 v2 v8 v9 v3 v10 v11 v12 v13 v15 v28
                                        (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) v24 v16
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'head_260
                                           (coe v18)))
                                     (coe v17)
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'poly_304
                                        (coe v3) (coe v27) (coe v18))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.walk-mono
d_walk'45'mono_610 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_walk'45'mono_610 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 ~v10 ~v11 ~v12
                   v13 v14 v15 v16 ~v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28
                   v29 v30
  = du_walk'45'mono_610
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v13 v14 v15 v16 v18 v19 v20 v21 v22 v23
      v24 v25 v26 v27 v28 v29 v30
du_walk'45'mono_610 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_walk'45'mono_610 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25
  = case coe v14 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
        -> coe
             seq (coe v26)
             (case coe v25 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                  -> coe
                       seq (coe v27)
                       (coe
                          du_here'45'main_420 (coe v0) (coe v1) (coe v2) (coe v15) (coe v16)
                          (coe v3) (coe v17) (coe v18) (coe v19) (coe v20) (coe v22) (coe v6)
                          (coe v7) (coe v10) (coe v12) (coe v4) (coe v13) (coe v23))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
        -> coe
             du_walk'45'mono'45'd_660 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v26) (coe v15) (coe v16)
             (coe v17) (coe v18) (coe v19) (coe v20) (coe v21) (coe v22)
             (coe v23) (coe v24) (coe v25)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v5)
                (coe ("main" :: Data.Text.Text)))
             (coe
                MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v8)
                (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.walk-mono-d
d_walk'45'mono'45'd_660 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_walk'45'mono'45'd_660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28
  = du_walk'45'mono'45'd_660
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16 v17 v18 v19
      v20 v21 v22 v23 v24 v25 v26 v27 v28
du_walk'45'mono'45'd_660 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_walk'45'mono'45'd_660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
  = let v28
          = case coe v26 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                -> coe
                     seq (coe v28)
                     (coe
                        seq (coe v29)
                        (coe
                           d_walk_556 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.Compile.C_cscope_446
                              (coe MAlonzo.Code.Once.Compile.d_csig_440 (coe v3))
                              (coe
                                 MAlonzo.Code.Once.Compile.d_cimps_442
                                 (coe
                                    MAlonzo.Code.Once.Compile.d_extendScope_488 (coe v3) (coe v5)
                                    (coe v8)))
                              (coe MAlonzo.Code.Once.Compile.d_ctele_444 (coe v3)))
                           (coe v4) (coe v11) (coe v13) (coe v14)
                           (coe addInt (coe (1 :: Integer)) (coe v15))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v16
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.PolyTy.C_schema_822
                                 (coe (0 :: Integer))
                                 (\ v30 -> coe MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.PolyTy.d_'8968'_'8969'_298
                                    (coe (0 :: Integer)) (coe v8))))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Telescope.C_def_28 v17
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Abstract.du_absTm_744
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
                                    (coe
                                       MAlonzo.Code.Once.Lang.Core.Translate.d_monoSchema_8
                                       (coe v8)))
                                 (\ v30 -> coe MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.Lang.Core.Translate.d_monoElab_610 (coe v1)
                                       (coe v15) (coe v16)
                                       (coe
                                          MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.Parser.C_mkFunInfo_114 (coe v5) (coe v6)
                                          (coe v7) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                       (coe v8) (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                       (coe v18) (coe v19) (coe v20) (coe v10))))
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Translate.du_monoBody_628 (coe v1)
                                 (coe v15) (coe v16)
                                 (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Parser.C_mkFunInfo_114 (coe v5) (coe v6)
                                    (coe v7) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                 (coe v8) (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                 (coe v18) (coe v19) (coe v20) (coe v10)))
                           (coe v18)
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Translate.C_i'45'def_102
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Translate.du_wkI_138
                                 (coe MAlonzo.Code.Once.Compile.d_cimps_442 (coe v3)) (coe v19)))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Translate.du_wkT_156
                              (coe
                                 MAlonzo.Code.Once.Compile.d_telePolys_454
                                 (MAlonzo.Code.Once.Compile.d_ctele_444 (coe v3)))
                              (coe v20))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Translate.du_monoSg_652 (coe v16)
                              (coe v8) (coe v21) (coe v9))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Compile.d_irFunOf_1056
                                 (coe
                                    MAlonzo.Code.Once.Compile.C_mkCompiledFun_312
                                    (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v5)) (coe v8)
                                    (coe v12)))
                              (coe v22))
                           (coe
                              MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_inv'45'mono_516 v0
                              v1 v2 v15 v16 v3 v17 v18 v19 v20 v22
                              (coe
                                 MAlonzo.Code.Once.Parser.C_mkFunInfo_114 (coe v5) (coe v6) (coe v7)
                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                              v8 v9 (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) v10 v12
                              erased v23
                              (coe
                                 MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'head_260
                                 (coe v25)))
                           (coe v24)
                           (coe
                              MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'fun_272
                              (coe v4) (coe v25))))
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v25 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
           -> let v31
                    = case coe v26 of
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                          -> case coe v31 of
                               MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                 -> case coe v32 of
                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                        -> coe
                                             d_walk_556 (coe v0) (coe v1) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.Compile.C_cscope_446
                                                (coe MAlonzo.Code.Once.Compile.d_csig_440 (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_cimps_442
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.d_extendScope_488
                                                      (coe v3) (coe v5) (coe v8)))
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_ctele_444 (coe v3)))
                                             (coe v4) (coe v11) (coe v13) (coe v14)
                                             (coe addInt (coe (1 :: Integer)) (coe v15))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834
                                                v16
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.PolyTy.C_schema_822
                                                   (coe (0 :: Integer))
                                                   (\ v34 ->
                                                      coe
                                                        MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Core.PolyTy.d_'8968'_'8969'_298
                                                      (coe (0 :: Integer)) (coe v8))))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Core.Telescope.C_def_28 v17
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.Abstract.du_absTm_744
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Core.Translate.d_monoSchema_8
                                                         (coe v8)))
                                                   (\ v34 ->
                                                      coe
                                                        MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Core.Translate.d_monoElab_610
                                                         (coe v1) (coe v15) (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                                            (coe v3))
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.C_mkFunInfo_114
                                                            (coe v5) (coe v6) (coe v7) (coe v31))
                                                         (coe v8)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                                         (coe v18) (coe v19) (coe v20) (coe v10))))
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.Translate.du_monoBody_628
                                                   (coe v1) (coe v15) (coe v16)
                                                   (coe
                                                      MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                                      (coe v3))
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.C_mkFunInfo_114
                                                      (coe v5) (coe v6) (coe v7) (coe v31))
                                                   (coe v8)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                                   (coe v18) (coe v19) (coe v20) (coe v10)))
                                             (coe v18)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Core.Translate.C_i'45'def_102
                                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.Translate.du_wkI_138
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.d_cimps_442
                                                      (coe v3))
                                                   (coe v19)))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Core.Translate.du_wkT_156
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_telePolys_454
                                                   (MAlonzo.Code.Once.Compile.d_ctele_444 (coe v3)))
                                                (coe v20))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Core.Translate.du_monoSg_652
                                                (coe v16) (coe v8) (coe v21) (coe v9))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_irFunOf_1056
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_312
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Name.d_bare_14
                                                         (coe v5))
                                                      (coe v8) (coe v12)))
                                                (coe v22))
                                             (coe
                                                MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_inv'45'mono_516
                                                v0 v1 v2 v15 v16 v3 v17 v18 v19 v20 v22
                                                (coe
                                                   MAlonzo.Code.Once.Parser.C_mkFunInfo_114 (coe v5)
                                                   (coe v6) (coe v7) (coe v31))
                                                v8 v9
                                                (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                                v10 v12 erased v23
                                                (coe
                                                   MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'head_260
                                                   (coe v25)))
                                             (coe v24)
                                             (coe
                                                MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'fun_272
                                                (coe v4) (coe v25))
                                      _ -> coe v28
                               _ -> coe v28
                        _ -> MAlonzo.RTE.mazUnreachableError in
              coe
                (case coe v29 of
                   MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v34 v35
                     -> case coe v26 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v36 v37
                            -> if coe v36
                                 then case coe v37 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v38
                                          -> case coe v27 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v39 v40
                                                 -> if coe v39
                                                      then case coe v40 of
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v41
                                                               -> coe
                                                                    du_here'45'main_420 (coe v0)
                                                                    (coe v1) (coe v2) (coe v15)
                                                                    (coe v16) (coe v3) (coe v17)
                                                                    (coe v18) (coe v19) (coe v20)
                                                                    (coe v22) (coe v6) (coe v7)
                                                                    (coe v10) (coe v12) (coe v4)
                                                                    (coe v13) (coe v23)
                                                             _ -> coe v31
                                                      else (case coe v40 of
                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                -> coe
                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                              _ -> coe v31)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> coe v31
                                 else (case coe v37 of
                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                           -> coe
                                                d_walk_556 (coe v0) (coe v1) (coe v2)
                                                (coe
                                                   MAlonzo.Code.Once.Compile.C_cscope_446
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.d_csig_440 (coe v3))
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.d_cimps_442
                                                      (coe
                                                         MAlonzo.Code.Once.Compile.d_extendScope_488
                                                         (coe v3) (coe v5) (coe v8)))
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.d_ctele_444
                                                      (coe v3)))
                                                (coe v4) (coe v11) (coe v13) (coe v14)
                                                (coe addInt (coe (1 :: Integer)) (coe v15))
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834
                                                   v16
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Core.PolyTy.C_schema_822
                                                      (coe (0 :: Integer))
                                                      (\ v39 ->
                                                         coe
                                                           MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Core.PolyTy.d_'8968'_'8969'_298
                                                         (coe (0 :: Integer)) (coe v8))))
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.Telescope.C_def_28
                                                   v17
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Core.Abstract.du_absTm_744
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Core.Translate.d_monoSchema_8
                                                            (coe v8)))
                                                      (\ v39 ->
                                                         coe
                                                           MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Core.Translate.d_monoElab_610
                                                            (coe v1) (coe v15) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                                               (coe v3))
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.C_mkFunInfo_114
                                                               (coe v5) (coe v6) (coe v7) (coe v36))
                                                            (coe v8)
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                                            (coe v18) (coe v19) (coe v20)
                                                            (coe v10))))
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Core.Translate.du_monoBody_628
                                                      (coe v1) (coe v15) (coe v16)
                                                      (coe
                                                         MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                                         (coe v3))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.C_mkFunInfo_114
                                                         (coe v5) (coe v6) (coe v7) (coe v36))
                                                      (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                                      (coe v18) (coe v19) (coe v20) (coe v10)))
                                                (coe v18)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.Translate.C_i'45'def_102
                                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Core.Translate.du_wkI_138
                                                      (coe
                                                         MAlonzo.Code.Once.Compile.d_cimps_442
                                                         (coe v3))
                                                      (coe v19)))
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.Translate.du_wkT_156
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.d_telePolys_454
                                                      (MAlonzo.Code.Once.Compile.d_ctele_444
                                                         (coe v3)))
                                                   (coe v20))
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.Translate.du_monoSg_652
                                                   (coe v16) (coe v8) (coe v21) (coe v9))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.d_irFunOf_1056
                                                      (coe
                                                         MAlonzo.Code.Once.Compile.C_mkCompiledFun_312
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Name.d_bare_14
                                                            (coe v5))
                                                         (coe v8) (coe v12)))
                                                   (coe v22))
                                                (coe
                                                   MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.du_inv'45'mono_516
                                                   v0 v1 v2 v15 v16 v3 v17 v18 v19 v20 v22
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.C_mkFunInfo_114
                                                      (coe v5) (coe v6) (coe v7) (coe v36))
                                                   v8 v9
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                                   v10 v12 erased v23
                                                   (coe
                                                      MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'head_260
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                                                            v34 v35)
                                                         (coe v30))))
                                                (coe v24)
                                                (coe
                                                   MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'fun_272
                                                   (coe v4)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                                                         v34 v35)
                                                      (coe v30)))
                                         _ -> coe v31)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v31)
         _ -> MAlonzo.RTE.mazUnreachableError)
