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
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.FaithfulLemmas.forget-inject
d_forget'45'inject_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'inject_10 = erased
-- Once.Adequacy.FaithfulLemmas.morph-app-bridge
d_morph'45'app'45'bridge_80 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_morph'45'app'45'bridge_80 = erased
-- Once.Adequacy.FaithfulLemmas.morph-app-bridge-fun
d_morph'45'app'45'bridge'45'fun_112 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_morph'45'app'45'bridge'45'fun_112 = erased
-- Once.Adequacy.FaithfulLemmas.cata-body
d_cata'45'body_142 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'body_142 = erased
-- Once.Adequacy.FaithfulLemmas._.algIR
d_algIR_164 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.CCC.IR.T_IR_18
d_algIR_164 ~v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_algIR_164 v2 v3 v4 v6
du_algIR_164 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_18
du_algIR_164 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__32
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
            (coe
               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
            (coe v1))
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1)))
      (coe MAlonzo.Code.Once.CCC.IR.C_apply_98)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_40
         (coe
            MAlonzo.Code.Once.CCC.IR.C__'8728'__32
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du_'10214'_'10215''7580'_38
               (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_108
               (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                  (coe v1))
               (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10) (coe v3))
            (coe MAlonzo.Code.Once.CCC.IR.C_terminal_76))
         (coe MAlonzo.Code.Once.CCC.IR.C_id_24)
         (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
-- Once.Adequacy.FaithfulLemmas._.alg-eq
d_alg'45'eq_168 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alg'45'eq_168 = erased
-- Once.Adequacy.FaithfulLemmas.ana-ev-bridge
d_ana'45'ev'45'bridge_200 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'ev'45'bridge_200 = erased
-- Once.Adequacy.FaithfulLemmas._.coalgIR
d_coalgIR_224 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.CCC.IR.T_IR_18
d_coalgIR_224 v0 v1 v2 v3 ~v4 ~v5 ~v6 = du_coalgIR_224 v0 v1 v2 v3
du_coalgIR_224 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_18
du_coalgIR_224 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__32
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v1) (coe v2)
            (coe
               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1)))
         (coe v1))
      (coe MAlonzo.Code.Once.CCC.IR.C_apply_98)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_40
         (coe
            MAlonzo.Code.Once.CCC.IR.C__'8728'__32
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du_'10214'_'10215''7580'_38
               (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_108
               (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v1) (coe v2)
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1)))
               (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10) (coe v3))
            (coe MAlonzo.Code.Once.CCC.IR.C_terminal_76))
         (coe MAlonzo.Code.Once.CCC.IR.C_id_24)
         (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
-- Once.Adequacy.FaithfulLemmas._.stepˢ
d_step'738'_226 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step'738'_226 v0 v1 v2 v3 ~v4 v5 ~v6
  = du_step'738'_226 v0 v1 v2 v3 v5
du_step'738'_226 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step'738'_226 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_98
         (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v1) (coe v2)
            (coe
               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1)))
         (coe v3) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         (\ v5 ->
            coe
              v5
              (MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30
                 (coe v1) (coe v4))))
-- Once.Adequacy.FaithfulLemmas._.step-eq
d_step'45'eq_230 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_230 = erased
-- Once.Adequacy.FaithfulLemmas.ana-body
d_ana'45'body_264 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'body_264 = erased
