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

module MAlonzo.Code.Once.Adequacy.FaithfulLemmas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.FaithfulLemmas.forget-inject
d_forget'45'inject_42 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'inject_42 = erased
-- Once.Adequacy.FaithfulLemmas.transport-apply-bind
d_transport'45'apply'45'bind_120 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_transport'45'apply'45'bind_120 = erased
-- Once.Adequacy.FaithfulLemmas.subst-T-returnT
d_subst'45'T'45'returnT_136 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'returnT_136 = erased
-- Once.Adequacy.FaithfulLemmas.subst-arrow
d_subst'45'arrow_164 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arrow_164 = erased
-- Once.Adequacy.FaithfulLemmas.morph-app-bridge
d_morph'45'app'45'bridge_186 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_morph'45'app'45'bridge_186 = erased
-- Once.Adequacy.FaithfulLemmas._.w'
d_w''_204 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> AgdaAny
d_w''_204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 = du_w''_204 v6
du_w''_204 :: AgdaAny -> AgdaAny
du_w''_204 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.app-⟨⟩-clean
d_app'45''10216''10217''45'clean_210 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45''10216''10217''45'clean_210 = erased
-- Once.Adequacy.FaithfulLemmas._.ih-evalᴰ
d_ih'45'eval'7472'_220 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'45'eval'7472'_220 = erased
-- Once.Adequacy.FaithfulLemmas.morph-app-bridge-fun
d_morph'45'app'45'bridge'45'fun_254 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_morph'45'app'45'bridge'45'fun_254 = erased
-- Once.Adequacy.FaithfulLemmas.cata-body
d_cata'45'body_284 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'body_284 = erased
-- Once.Adequacy.FaithfulLemmas._.algIR
d_algIR_308 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_algIR_308 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_algIR_308 v3 v4 v5 v7
du_algIR_308 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_algIR_308 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1)))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1)))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
            (coe
               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1))))
      (coe MAlonzo.Code.Once.IR.C_apply_92)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_246
               (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1))
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                  (coe v1))
               (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3))
            (coe MAlonzo.Code.Once.IR.C_terminal_74))
         (coe MAlonzo.Code.Once.IR.C_id_22)
         (coe MAlonzo.Code.Once.IR.C_Heap_8))
-- Once.Adequacy.FaithfulLemmas._.Cata-IR
d_Cata'45'IR_310 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_Cata'45'IR_310 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10
  = du_Cata'45'IR_310 v3 v4 v5 v6 v7
du_Cata'45'IR_310 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_Cata'45'IR_310 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.C_Cata_106
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v3))
      (coe du_algIR_308 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Adequacy.FaithfulLemmas._.elab-cata-reduce
d_elab'45'cata'45'reduce_316 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elab'45'cata'45'reduce_316 = erased
-- Once.Adequacy.FaithfulLemmas._.alg-eq
d_alg'45'eq_332 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alg'45'eq_332 = erased
-- Once.Adequacy.FaithfulLemmas._.fold-eq
d_fold'45'eq_342 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'eq_342 = erased
-- Once.Adequacy.FaithfulLemmas.evalᴰ-subst-cod
d_eval'7472''45'subst'45'cod_366 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'cod_366 = erased
-- Once.Adequacy.FaithfulLemmas.valueT-subst
d_valueT'45'subst_384 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_valueT'45'subst_384 = erased
-- Once.Adequacy.FaithfulLemmas.ana-ev-bridge
d_ana'45'ev'45'bridge_410 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'ev'45'bridge_410 = erased
-- Once.Adequacy.FaithfulLemmas._.p
d_p_434 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_p_434 ~v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 = du_p_434 v1 v2 v3 v4
du_p_434 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_p_434 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1))))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1)))
      (coe MAlonzo.Code.Once.IR.C_apply_92)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_246
               (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v1) (coe v2)
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1)))
               (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3))
            (coe MAlonzo.Code.Once.IR.C_terminal_74))
         (coe MAlonzo.Code.Once.IR.C_id_22)
         (coe MAlonzo.Code.Once.IR.C_Heap_8))
-- Once.Adequacy.FaithfulLemmas._.seed-e
d_seed'45'e_436 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> AgdaAny
d_seed'45'e_436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_seed'45'e_436 v6
du_seed'45'e_436 :: AgdaAny -> AgdaAny
du_seed'45'e_436 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.v0T
d_v0T_440 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v0T_440 v0 v1 v2 v3 v4 ~v5 v6 ~v7 = du_v0T_440 v0 v1 v2 v3 v4 v6
du_v0T_440 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_v0T_440 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1) (coe v2)))
      (coe du_p_434 (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2)))
         (coe v5))
-- Once.Adequacy.FaithfulLemmas._.v0
d_v0_442 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> AgdaAny
d_v0_442 v0 v1 v2 v3 v4 ~v5 v6 v7 = du_v0_442 v0 v1 v2 v3 v4 v6 v7
du_v0_442 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
du_v0_442 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
      (coe
         du_v0T_440 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe v6)
-- Once.Adequacy.FaithfulLemmas._.eE
d_eE_444 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eE_444 = erased
-- Once.Adequacy.FaithfulLemmas._.eS
d_eS_446 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eS_446 = erased
-- Once.Adequacy.FaithfulLemmas._.step-e-eq
d_step'45'e'45'eq_450 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'e'45'eq_450 = erased
-- Once.Adequacy.FaithfulLemmas._.step-s-eq
d_step'45's'45'eq_454 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45's'45'eq_454 = erased
-- Once.Adequacy.FaithfulLemmas._.trace-eq
d_trace'45'eq_462 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'eq_462 = erased
-- Once.Adequacy.FaithfulLemmas._.R
d_R_468 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> AgdaAny -> AgdaAny -> ()
d_R_468 = erased
-- Once.Adequacy.FaithfulLemmas._.child-e
d_child'45'e_476 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_child'45'e_476 v0 v1 v2 v3 v4 ~v5 ~v6 v7 v8
  = du_child'45'e_476 v0 v1 v2 v3 v4 v7 v8
du_child'45'e_476 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_child'45'e_476 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_ana'45'events_44 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.d_eraseF_40 (coe v1))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
      (coe du_p_434 (coe v1) (coe v2) (coe v3) (coe v4)) (coe v6)
      (coe v5)
-- Once.Adequacy.FaithfulLemmas._.child-s
d_child'45's_482 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_child'45's_482 v0 v1 v2 v3 v4 ~v5 ~v6 v7 v8
  = du_child'45's_482 v0 v1 v2 v3 v4 v7 v8
du_child'45's_482 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_child'45's_482 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.SourceDenote.d_ana'45'events'738'_194
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_246
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v2) (coe v3)
            (coe
               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1) (coe v2)))
         (coe v4) (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe v6) (coe v5)
-- Once.Adequacy.FaithfulLemmas._.child-R
d_child'45'R_490 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_child'45'R_490 = erased
-- Once.Adequacy.FaithfulLemmas._.ve-eq
d_ve'45'eq_506 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ve'45'eq_506 = erased
-- Once.Adequacy.FaithfulLemmas._.vs-eq
d_vs'45'eq_514 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vs'45'eq_514 = erased
-- Once.Adequacy.FaithfulLemmas._.events-eq
d_events'45'eq_524 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events'45'eq_524 = erased
-- Once.Adequacy.FaithfulLemmas.ana-body
d_ana'45'body_554 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'body_554 = erased
-- Once.Adequacy.FaithfulLemmas._.coalgIR
d_coalgIR_578 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_coalgIR_578 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_coalgIR_578 v3 v4 v5 v7
du_coalgIR_578 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_coalgIR_578 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1))))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1)))
      (coe MAlonzo.Code.Once.IR.C_apply_92)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_246
               (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1)))
               (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3))
            (coe MAlonzo.Code.Once.IR.C_terminal_74))
         (coe MAlonzo.Code.Once.IR.C_id_22)
         (coe MAlonzo.Code.Once.IR.C_Heap_8))
-- Once.Adequacy.FaithfulLemmas._.coalg'
d_coalg''_580 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_coalg''_580 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_coalg''_580 v3 v4 v5 v7
du_coalg''_580 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_coalg''_580 v0 v1 v2 v3
  = coe du_coalgIR_578 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.FaithfulLemmas._.Ana-IR
d_Ana'45'IR_584 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_Ana'45'IR_584 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10
  = du_Ana'45'IR_584 v3 v4 v5 v6 v7
du_Ana'45'IR_584 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_Ana'45'IR_584 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.C_Ana_126
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v3))
      (coe du_coalg''_580 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Adequacy.FaithfulLemmas._.elab-ana-reduce
d_elab'45'ana'45'reduce_588 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elab'45'ana'45'reduce_588 = erased
-- Once.Adequacy.FaithfulLemmas._.cL-e
d_cL'45'e_600 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> AgdaAny -> AgdaAny
d_cL'45'e_600 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10 v11
  = du_cL'45'e_600 v0 v3 v4 v5 v7 v11
du_cL'45'e_600 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
du_cL'45'e_600 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_40 (coe v1)))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
            (coe
               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
               (coe MAlonzo.Code.Once.IRTy.d_eraseF_40 (coe v1))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
               (coe
                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                  (coe MAlonzo.Code.Once.IRTy.d_eraseF_40 (coe v1))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2)))
               (coe du_coalg''_580 (coe v1) (coe v2) (coe v3) (coe v4))
               (coe
                  MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2)))
                  (coe v5)))
            (coe (0 :: Integer))))
-- Once.Adequacy.FaithfulLemmas._.cR
d_cR_606 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> AgdaAny -> AgdaAny
d_cR_606 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10 v11
  = du_cR_606 v0 v3 v4 v5 v7 v11
du_cR_606 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
du_cR_606 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96 (coe v1)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe
               MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
               (coe
                  MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_246
                  (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v2)
                     (coe
                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                        (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))
                     (coe
                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1) (coe v2)))
                  (coe v4) (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
               (0 :: Integer)
               (MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                  (coe v2) (coe v5)))
            (coe (0 :: Integer))))
-- Once.Adequacy.FaithfulLemmas._.subst-νS-cong
d_subst'45'νS'45'cong_620 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'νS'45'cong_620 = erased
-- Once.Adequacy.FaithfulLemmas._.seed-eq
d_seed'45'eq_630 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seed'45'eq_630 = erased
-- Once.Adequacy.FaithfulLemmas._.trace-at
d_trace'45'at_642 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'at_642 = erased
-- Once.Adequacy.FaithfulLemmas._.subst-fn-cod
d_subst'45'fn'45'cod_664 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'fn'45'cod_664 = erased
-- Once.Adequacy.FaithfulLemmas._.v0
d_v0_668 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> AgdaAny -> AgdaAny
d_v0_668 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10 v11
  = du_v0_668 v0 v3 v4 v5 v7 v11
du_v0_668 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
du_v0_668 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
            (coe
               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1) (coe v2)))
         (coe du_coalgIR_578 (coe v1) (coe v2) (coe v3) (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
            (coe
               MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2)))
            (coe v5)))
      (coe (0 :: Integer))
-- Once.Adequacy.FaithfulLemmas._.erased-eq
d_erased'45'eq_684 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_erased'45'eq_684 = erased
-- Once.Adequacy.FaithfulLemmas._.step-s-eq
d_step'45's'45'eq_704 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45's'45'eq_704 = erased
-- Once.Adequacy.FaithfulLemmas._.surface-eq
d_surface'45'eq_714 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_surface'45'eq_714 = erased
-- Once.Adequacy.FaithfulLemmas._.ceq
d_ceq_734 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ceq_734 = erased
-- Once.Adequacy.FaithfulLemmas._.value-at
d_value'45'at_760 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_value'45'at_760 = erased
-- Once.Adequacy.FaithfulLemmas._.per-a
d_per'45'a_774 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_per'45'a_774 = erased
