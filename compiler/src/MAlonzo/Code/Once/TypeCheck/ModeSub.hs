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

module MAlonzo.Code.Once.TypeCheck.ModeSub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Laws.ModeAgreement
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.TypeCheck.ModeSub.just≢nothing
d_just'8802'nothing_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_12 = erased
-- Once.TypeCheck.ModeSub.ex
d_ex_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ex_18 = erased
-- Once.TypeCheck.ModeSub.arrow-at
d_arrow'45'at_40 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286
d_arrow'45'at_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_arrow'45'at_40 v8
du_arrow'45'at_40 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286
du_arrow'45'at_40 v0 = coe v0
-- Once.TypeCheck.ModeSub.sub-dom
d_sub'45'dom_60 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_sub'45'dom_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sub'45'dom_60 v6
du_sub'45'dom_60 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_sub'45'dom_60 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56 v8 v9 v10 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.sub-cod
d_sub'45'cod_76 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_sub'45'cod_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sub'45'cod_76 v6
du_sub'45'cod_76 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_sub'45'cod_76 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56 v8 v9 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub._≼_
d__'8828'__80 a0 a1 = ()
data T__'8828'__80
  = C_'8828''45'sub_86 MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 |
    C_'8828''45'guard_96 MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 |
    C_'8828''45'prod_106 T__'8828'__80 T__'8828'__80
-- Once.TypeCheck.ModeSub.≼-g
d_'8828''45'g_122 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  T__'8828'__80 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_'8828''45'g_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_'8828''45'g_122 v7
du_'8828''45'g_122 ::
  T__'8828'__80 -> MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_'8828''45'g_122 v0
  = case coe v0 of
      C_'8828''45'sub_86 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.≼-same
d_'8828''45'same_138 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  T__'8828'__80 -> MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_'8828''45'same_138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8828''45'same_138 v6
du_'8828''45'same_138 ::
  T__'8828'__80 -> MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_'8828''45'same_138 v0
  = case coe v0 of
      C_'8828''45'sub_86 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.≼-s
d_'8828''45's_156 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  T__'8828'__80 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_'8828''45's_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_'8828''45's_156 v7
du_'8828''45's_156 ::
  T__'8828'__80 -> MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_'8828''45's_156 v0
  = case coe v0 of
      C_'8828''45'sub_86 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.di-dom
d_di'45'dom_180 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_di'45'dom_180 v0 v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11
  = du_di'45'dom_180 v0 v1 v3 v4 v5 v7 v10 v11
du_di'45'dom_180 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_di'45'dom_180 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_800 v11 v14 v16 v17 v18
        -> coe
             du_dom'45'along_208
             (coe
                MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'ii_494
                (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v14))
                   (coe v2))
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
                   (coe v5) (coe v4))
                (coe v16) (coe v7))
             (coe v17)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_824 v13 v14 v15 v16 v17 v18 v23 v24 v25 v26
        -> coe
             seq (coe v7) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_864 v12 v15 v16 v17 v18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_874 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_886 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_898 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_908 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_916 v10
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_936 v15 v16 v17 v18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_956 v15 v16 v17 v18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_972 v13 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub._.dom-along
d_dom'45'along_208 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_dom'45'along_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                   v24 v25
  = du_dom'45'along_208 v24 v25
du_dom'45'along_208 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_dom'45'along_208 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.TypeCheck.ModeSub.≡-sub
d_'8801''45'sub_252 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_'8801''45'sub_252 v0 ~v1 ~v2 = du_'8801''45'sub_252 v0
du_'8801''45'sub_252 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_'8801''45'sub_252 v0
  = coe
      MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102 (coe v0)
-- Once.TypeCheck.ModeSub.sub-along
d_sub'45'along_262 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_sub'45'along_262 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_sub'45'along_262 v4 v5
du_sub'45'along_262 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_sub'45'along_262 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.TypeCheck.ModeSub.apply-sub
d_apply'45'sub_276 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_apply'45'sub_276 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_apply'45'sub_276 v2 v5
du_apply'45'sub_276 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_apply'45'sub_276 v0 v1
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102 (coe v0))
-- Once.TypeCheck.ModeSub.di-cod
d_di'45'cod_294 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_di'45'cod_294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_di'45'cod_294 v6 v7
du_di'45'cod_294 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_di'45'cod_294 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe seq (coe v5) (coe du_sub'45'cod_76 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.guard-pair
d_guard'45'pair_308 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 -> T__'8828'__80
d_guard'45'pair_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_guard'45'pair_308 v6
du_guard'45'pair_308 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 -> T__'8828'__80
du_guard'45'pair_308 v0 = coe C_'8828''45'guard_96 v0
-- Once.TypeCheck.ModeSub.poly-sub
d_poly'45'sub_352 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
d_poly'45'sub_352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_poly'45'sub_352 v9
du_poly'45'sub_352 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30
du_poly'45'sub_352 v0 = coe du_'8801''45'sub_252 (coe v0)
-- Once.TypeCheck.ModeSub.ic-sub
d_ic'45'sub_378 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8828'__80
d_ic'45'sub_378 v0 v1 v2 v3 ~v4 ~v5 v6 v7
  = du_ic'45'sub_378 v0 v1 v2 v3 v6 v7
du_ic'45'sub_378 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8828'__80
du_ic'45'sub_378 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_442 v9
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_454 v10
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_466 v10
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_476 v9
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_486 v9
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'morph'45'check_498 v10
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'morph'45'check_510 v10
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_530 v10 v13 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_554 v10 v12 v14 v15 v16 v17 v18 v19
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_574 v13 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_594 v13 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'curry'45'check_614 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_630 v11 v12 v13 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'ana'45'check_648 v12 v13 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v8 v11 v12
        -> coe
             C_'8828''45'sub_86
             (coe
                du_sub'45'along_262
                (coe
                   MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'ii_494
                   (coe v0) (coe v1) (coe v2) (coe v8) (coe v4) (coe v11))
                (coe v12))
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved'45'guard_674 v11 v12 v14 v15
        -> let v16
                 = seq
                     (coe v4)
                     (case coe v12 of
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v18 v19
                          -> case coe v19 of
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v22 v23
                                 -> case coe v23 of
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v26 v27
                                        -> case coe v27 of
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v30 v31
                                               -> case coe v31 of
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v34 v35
                                                      -> case coe v35 of
                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v38 v39
                                                             -> case coe v39 of
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v42 v43
                                                                    -> coe
                                                                         seq (coe v43)
                                                                         (coe
                                                                            MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError
                        _ -> MAlonzo.RTE.mazUnreachableError) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v17
                  -> case coe v3 of
                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                         -> case coe v4 of
                              MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
                                -> case coe v12 of
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v24 v25
                                       -> case coe v25 of
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v28 v29
                                              -> case coe v29 of
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v32 v33
                                                     -> case coe v33 of
                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v36 v37
                                                            -> case coe v37 of
                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v40 v41
                                                                   -> case coe v41 of
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v44 v45
                                                                          -> case coe v45 of
                                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v48 v49
                                                                                 -> case coe v49 of
                                                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v52 v53
                                                                                        -> coe
                                                                                             MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                      _ -> coe v16
                                                                               _ -> coe v16
                                                                        _ -> coe v16
                                                                 _ -> coe v16
                                                          _ -> coe v16
                                                   _ -> coe v16
                                            _ -> coe v16
                                     _ -> coe v16
                              MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v24 v26
                                -> coe du_guard'45'pair_308 (coe v14)
                              MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v26
                                -> case coe v17 of
                                     MAlonzo.Code.Once.Spec.Name.C_canonical_12 v27
                                       -> case coe v27 of
                                            (:) v28 v29
                                              -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                            _ -> coe v16
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v16
                _ -> coe v16)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'lit'45'check_712 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v17 v18
                      -> case coe v4 of
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_138 v24 v25 v26 v27
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 v28 v29
                                    -> coe
                                         C_'8828''45'prod_106
                                         (coe
                                            du_ic'45'sub_378 (coe v0) (coe v15) (coe v28) (coe v17)
                                            (coe v26) (coe v13))
                                         (coe
                                            du_ic'45'sub_378 (coe v0) (coe v16) (coe v29) (coe v18)
                                            (coe v27) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_722 v9 v10 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_734 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_334 v16 v18 v19
                      -> coe
                           C_'8828''45'sub_86
                           (coe
                              du_apply'45'sub_276 (coe v2)
                              (coe
                                 MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'ii_494
                                 (coe v0) (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                       (coe v2))
                                    (coe v16))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                       (coe v3))
                                    (coe v8))
                                 (coe v19) (coe v11)))
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_350 v16 v18 v20 v21
                      -> coe
                           seq (coe v20) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'app'45'check_746 v10 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'app'45'check_758 v10 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'app'45'check_768 v9 v10
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_782 v9 v10 v11 v16
        -> coe
             seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.dc-sub
d_dc'45'sub_396 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8828'__80
d_dc'45'sub_396 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_800 v13 v16 v18 v19 v20
        -> coe
             C_'8828''45'sub_86
             (coe
                du_sub'45'cod_76
                (coe
                   du_'8828''45'g_122
                   (coe
                      du_ic'45'sub_378 (coe v0) (coe v1)
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v13)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v16))
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v2)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                         (coe v4))
                      (coe v18) (coe v9))))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_824 v15 v16 v17 v18 v19 v20 v25 v26 v27 v28
        -> let v29
                 = case coe v9 of
                     MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v31 v34 v35
                       -> coe
                            C_'8828''45'sub_86
                            (coe
                               du_di'45'cod_294
                               (coe
                                  MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                  (coe v0) (coe v1) (coe v3) (coe v31) (coe v6) (coe v7)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_824 v15 v16 v17 v18
                                     v19 v20 v25 v26 v27 v28)
                                  (coe v34))
                               (coe v35))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v30
                  -> case coe v9 of
                       MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v33 v36 v37
                         -> coe
                              C_'8828''45'sub_86
                              (coe
                                 du_di'45'cod_294
                                 (coe
                                    MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                    (coe v0) (coe v1) (coe v3) (coe v33) (coe v6) (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_824 v15 v16 v17 v18
                                       v19 v20 v25 v26 v27 v28)
                                    (coe v36))
                                 (coe v37))
                       MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_782 v34 v35 v36 v41
                         -> case coe v27 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                -> coe
                                     seq (coe v43)
                                     (case coe v41 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                          -> coe
                                               seq (coe v45)
                                               (coe
                                                  C_'8828''45'sub_86
                                                  (coe du_poly'45'sub_352 (coe v3)))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v29)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_844 v15 v18 v19
        -> let v20
                 = case coe v9 of
                     MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v22 v25 v26
                       -> coe
                            C_'8828''45'sub_86
                            (coe
                               du_di'45'cod_294
                               (coe
                                  MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                  (coe v0) (coe v1) (coe v3) (coe v22) (coe v6) (coe v7)
                                  (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_844 v15 v18 v19)
                                  (coe v25))
                               (coe v26))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v21 v22
                  -> case coe v9 of
                       MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v25 v28 v29
                         -> coe
                              C_'8828''45'sub_86
                              (coe
                                 du_di'45'cod_294
                                 (coe
                                    MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                    (coe v0) (coe v1) (coe v3) (coe v25) (coe v6) (coe v7)
                                    (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_844 v15 v18 v19)
                                    (coe v28))
                                 (coe v29))
                       MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_696 v29 v32 v34
                         -> coe
                              du_ic'45'sub_378
                              (coe
                                 MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                                 (coe v21) (coe v2))
                              (coe v22) (coe v3) (coe v4) (coe v19) (coe v34)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v20)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_864 v14 v17 v18 v19 v20
        -> let v21
                 = case coe v9 of
                     MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v23 v26 v27
                       -> coe
                            C_'8828''45'sub_86
                            (coe
                               du_di'45'cod_294
                               (coe
                                  MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                  (coe v0) (coe v1) (coe v3) (coe v23) (coe v6) (coe v7)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_864 v14 v17 v18
                                     v19 v20)
                                  (coe v26))
                               (coe v27))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
                  -> let v24
                           = case coe v9 of
                               MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v26 v29 v30
                                 -> coe
                                      C_'8828''45'sub_86
                                      (coe
                                         du_di'45'cod_294
                                         (coe
                                            MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                            (coe v0) (coe v1) (coe v3) (coe v26) (coe v6) (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_864 v14
                                               v17 v18 v19 v20)
                                            (coe v29))
                                         (coe v30))
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v22 of
                          MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
                            -> case coe v9 of
                                 MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_530 v31 v34 v35 v36 v37
                                   -> coe
                                        du_cg'45'sub_416 (coe v0) (coe v26) (coe v14) (coe v3)
                                        (coe v4) (coe v5) (coe v17) (coe v34) (coe v20) (coe v37)
                                 MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_554 v31 v33 v35 v36 v37 v38 v39 v40
                                   -> coe
                                        C_'8828''45'sub_86
                                        (coe
                                           du_di'45'cod_294
                                           (coe
                                              MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                              (coe v0) (coe v26) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                 (coe v31)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                    (coe v35))
                                                 (coe v33))
                                              (coe v17) (coe v36) (coe v20) (coe v38))
                                           (coe v39))
                                 MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v29 v32 v33
                                   -> coe
                                        C_'8828''45'sub_86
                                        (coe
                                           du_di'45'cod_294
                                           (coe
                                              MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                              (coe v0) (coe v1) (coe v3) (coe v29) (coe v6) (coe v7)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_864
                                                 v14 v17 v18 v19 v20)
                                              (coe v32))
                                           (coe v33))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v24)
                _ -> coe v21)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_874 v13
        -> case coe v9 of
             MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_442 v17
               -> coe
                    C_'8828''45'sub_86
                    (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102 (coe v2))
             MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v16 v19 v20
               -> coe
                    C_'8828''45'sub_86
                    (coe
                       du_di'45'cod_294
                       (coe
                          MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                          (coe v0) (coe v1) (coe v3) (coe v16) (coe v6) (coe v7)
                          (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'id_874 v13) (coe v19))
                       (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_886 v14
        -> let v15
                 = case coe v9 of
                     MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v17 v20 v21
                       -> coe
                            C_'8828''45'sub_86
                            (coe
                               du_di'45'cod_294
                               (coe
                                  MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                  (coe v0) (coe v1) (coe v3) (coe v17) (coe v6) (coe v7)
                                  (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_886 v14) (coe v20))
                               (coe v21))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
                  -> case coe v9 of
                       MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_454 v22
                         -> coe
                              C_'8828''45'sub_86
                              (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102 (coe v3))
                       MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v20 v23 v24
                         -> coe
                              C_'8828''45'sub_86
                              (coe
                                 du_di'45'cod_294
                                 (coe
                                    MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                    (coe v0) (coe v1) (coe v3) (coe v20) (coe v6) (coe v7)
                                    (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_886 v14)
                                    (coe v23))
                                 (coe v24))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v15)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_898 v14
        -> let v15
                 = case coe v9 of
                     MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v17 v20 v21
                       -> coe
                            C_'8828''45'sub_86
                            (coe
                               du_di'45'cod_294
                               (coe
                                  MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                  (coe v0) (coe v1) (coe v3) (coe v17) (coe v6) (coe v7)
                                  (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_898 v14) (coe v20))
                               (coe v21))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
                  -> case coe v9 of
                       MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_466 v22
                         -> coe
                              C_'8828''45'sub_86
                              (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102 (coe v3))
                       MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v20 v23 v24
                         -> coe
                              C_'8828''45'sub_86
                              (coe
                                 du_di'45'cod_294
                                 (coe
                                    MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                    (coe v0) (coe v1) (coe v3) (coe v20) (coe v6) (coe v7)
                                    (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_898 v14)
                                    (coe v23))
                                 (coe v24))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v15)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_908 v13
        -> case coe v9 of
             MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_476 v17
               -> coe
                    C_'8828''45'sub_86
                    (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102
                       (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
             MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v16 v19 v20
               -> coe
                    C_'8828''45'sub_86
                    (coe
                       du_di'45'cod_294
                       (coe
                          MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                          (coe v0) (coe v1) (coe v3) (coe v16) (coe v6) (coe v7)
                          (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_908 v13)
                          (coe v19))
                       (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_916 v12
        -> case coe v9 of
             MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_486 v16
               -> coe
                    C_'8828''45'sub_86
                    (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_34)
             MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v15 v18 v19
               -> coe
                    C_'8828''45'sub_86
                    (coe
                       du_di'45'cod_294
                       (coe
                          MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                          (coe v0) (coe v1) (coe v3) (coe v15) (coe v6) (coe v7)
                          (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_916 v12)
                          (coe v18))
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_936 v17 v18 v19 v20
        -> let v21
                 = case coe v9 of
                     MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v23 v26 v27
                       -> coe
                            C_'8828''45'sub_86
                            (coe
                               du_di'45'cod_294
                               (coe
                                  MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                  (coe v0) (coe v1) (coe v3) (coe v23) (coe v6) (coe v7)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Typing.C_d'45'case_936 v17 v18 v19 v20)
                                  (coe v26))
                               (coe v27))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
                  -> let v24
                           = case coe v9 of
                               MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v26 v29 v30
                                 -> coe
                                      C_'8828''45'sub_86
                                      (coe
                                         du_di'45'cod_294
                                         (coe
                                            MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                            (coe v0) (coe v1) (coe v3) (coe v26) (coe v6) (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.C_d'45'case_936 v17 v18
                                               v19 v20)
                                            (coe v29))
                                         (coe v30))
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v22 of
                          MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
                            -> let v27
                                     = case coe v9 of
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v29 v32 v33
                                           -> coe
                                                C_'8828''45'sub_86
                                                (coe
                                                   du_di'45'cod_294
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                                      (coe v0) (coe v1) (coe v3) (coe v29) (coe v6)
                                                      (coe v7)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Typing.C_d'45'case_936
                                                         v17 v18 v19 v20)
                                                      (coe v32))
                                                   (coe v33))
                                         _ -> MAlonzo.RTE.mazUnreachableError in
                               coe
                                 (case coe v2 of
                                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v28 v29
                                      -> case coe v9 of
                                           MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_574 v37 v38 v39 v40
                                             -> coe
                                                  d_dc'45'sub_396 (coe v0) (coe v26) (coe v28)
                                                  (coe v3) (coe v4) (coe v5) (coe v17) (coe v37)
                                                  (coe v19) (coe v39)
                                           MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v32 v35 v36
                                             -> coe
                                                  C_'8828''45'sub_86
                                                  (coe
                                                     du_di'45'cod_294
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                                        (coe v0) (coe v1) (coe v3) (coe v32)
                                                        (coe v6) (coe v7)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Typing.C_d'45'case_936
                                                           v17 v18 v19 v20)
                                                        (coe v35))
                                                     (coe v36))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> coe v27)
                          _ -> coe v24)
                _ -> coe v21)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_956 v17 v18 v19 v20
        -> let v21
                 = case coe v9 of
                     MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v23 v26 v27
                       -> coe
                            C_'8828''45'sub_86
                            (coe
                               du_di'45'cod_294
                               (coe
                                  MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                  (coe v0) (coe v1) (coe v3) (coe v23) (coe v6) (coe v7)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_956 v17 v18 v19 v20)
                                  (coe v26))
                               (coe v27))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
                  -> let v24
                           = case coe v9 of
                               MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v26 v29 v30
                                 -> coe
                                      C_'8828''45'sub_86
                                      (coe
                                         du_di'45'cod_294
                                         (coe
                                            MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                            (coe v0) (coe v1) (coe v3) (coe v26) (coe v6) (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_956 v17 v18
                                               v19 v20)
                                            (coe v29))
                                         (coe v30))
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v22 of
                          MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
                            -> let v27
                                     = case coe v9 of
                                         MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v29 v32 v33
                                           -> coe
                                                C_'8828''45'sub_86
                                                (coe
                                                   du_di'45'cod_294
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                                      (coe v0) (coe v1) (coe v3) (coe v29) (coe v6)
                                                      (coe v7)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_956
                                                         v17 v18 v19 v20)
                                                      (coe v32))
                                                   (coe v33))
                                         _ -> MAlonzo.RTE.mazUnreachableError in
                               coe
                                 (case coe v3 of
                                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v28 v29
                                      -> case coe v9 of
                                           MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_594 v37 v38 v39 v40
                                             -> case coe v4 of
                                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 v41 v42
                                                    -> coe
                                                         C_'8828''45'prod_106
                                                         (d_dc'45'sub_396
                                                            (coe v0) (coe v26) (coe v2) (coe v28)
                                                            (coe v41) (coe v5) (coe v17) (coe v37)
                                                            (coe v19) (coe v39))
                                                         (d_dc'45'sub_396
                                                            (coe v0) (coe v23) (coe v2) (coe v29)
                                                            (coe v42) (coe v5) (coe v18) (coe v38)
                                                            (coe v20) (coe v40))
                                                  _ -> coe v27
                                           MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v32 v35 v36
                                             -> coe
                                                  C_'8828''45'sub_86
                                                  (coe
                                                     du_di'45'cod_294
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                                        (coe v0) (coe v1) (coe v3) (coe v32)
                                                        (coe v6) (coe v7)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_956
                                                           v17 v18 v19 v20)
                                                        (coe v35))
                                                     (coe v36))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> coe v27)
                          _ -> coe v24)
                _ -> coe v21)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_972 v15 v16 v17 v18
        -> let v19
                 = case coe v9 of
                     MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v21 v24 v25
                       -> coe
                            C_'8828''45'sub_86
                            (coe
                               du_di'45'cod_294
                               (coe
                                  MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                  (coe v0) (coe v1) (coe v3) (coe v21) (coe v6) (coe v7)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_972 v15 v16 v17 v18)
                                  (coe v24))
                               (coe v25))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
                  -> let v22
                           = case coe v9 of
                               MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v24 v27 v28
                                 -> coe
                                      C_'8828''45'sub_86
                                      (coe
                                         du_di'45'cod_294
                                         (coe
                                            MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                            (coe v0) (coe v1) (coe v3) (coe v24) (coe v6) (coe v7)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_972 v15 v16
                                               v17 v18)
                                            (coe v27))
                                         (coe v28))
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v2 of
                          MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v23
                            -> case coe v9 of
                                 MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_630 v29 v30 v31 v32
                                   -> coe
                                        C_'8828''45'sub_86
                                        (coe
                                           du_sub'45'cod_76
                                           (coe
                                              du_'8828''45'same_138
                                              (coe
                                                 du_ic'45'sub_378 (coe v0) (coe v21)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                       (coe v23) (coe v3))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                       (coe v5))
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                       (coe v23) (coe v4))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                       (coe v5))
                                                    (coe v4))
                                                 (coe v18) (coe v32))))
                                 MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v26 v29 v30
                                   -> coe
                                        C_'8828''45'sub_86
                                        (coe
                                           du_di'45'cod_294
                                           (coe
                                              MAlonzo.Code.Once.Lang.Laws.ModeAgreement.du_agree'45'di_560
                                              (coe v0) (coe v1) (coe v3) (coe v26) (coe v6) (coe v7)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_972 v15
                                                 v16 v17 v18)
                                              (coe v29))
                                           (coe v30))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v22)
                _ -> coe v19)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.cg-sub
d_cg'45'sub_416 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8828'__80
d_cg'45'sub_416 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9 v10 v11
  = du_cg'45'sub_416 v0 v1 v2 v4 v5 v6 v7 v8 v10 v11
du_cg'45'sub_416 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T__'8828'__80
du_cg'45'sub_416 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      d_dc'45'sub_396 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
