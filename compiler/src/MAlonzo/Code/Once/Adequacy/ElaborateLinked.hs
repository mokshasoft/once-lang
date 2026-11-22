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

module MAlonzo.Code.Once.Adequacy.ElaborateLinked where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.ContractLaws
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.CoerceIR
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Concrete
import qualified MAlonzo.Code.Once.Type.Core
import qualified MAlonzo.Code.Once.TypeCheck.Table
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ElaborateLinked.linkedAt-cons
d_linkedAt'45'cons_18 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny
d_linkedAt'45'cons_18 v0 ~v1 v2 v3 v4 v5
  = du_linkedAt'45'cons_18 v0 v2 v3 v4 v5
du_linkedAt'45'cons_18 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny
du_linkedAt'45'cons_18 v0 v1 v2 v3 v4
  = coe
      du_go_42 (coe v4)
      (coe
         MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__4
         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__232
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0))
         (coe v2))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__232
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0))
         (coe v3))
-- Once.Adequacy.ElaborateLinked._.go
d_go_42 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
d_go_42 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_42 v5 v6 v7 v8
du_go_42 ::
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_go_42 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (case coe v2 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (case coe v3 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                          -> if coe v8
                                               then coe
                                                      seq (coe v9)
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               else coe seq (coe v9) (coe v0)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe seq (coe v7) (coe v0)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v5) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.linkedAt-here
d_linkedAt'45'here_48 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> AgdaAny
d_linkedAt'45'here_48 v0 ~v1 = du_linkedAt'45'here_48 v0
du_linkedAt'45'here_48 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 -> AgdaAny
du_linkedAt'45'here_48 v0
  = coe
      du_go_64
      (coe
         MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__4
         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v0))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v0)))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__232
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0)))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__232
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0)))
-- Once.Adequacy.ElaborateLinked._.go
d_go_64 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
d_go_64 ~v0 ~v1 v2 v3 v4 = du_go_64 v2 v3 v4
du_go_64 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_go_64 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (case coe v2 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                          -> if coe v7
                                               then coe
                                                      seq (coe v8)
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               else coe
                                                      seq (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.linked-mono
d_linked'45'mono_88 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_linked'45'mono_88 ~v0 ~v1 ~v2 v3 v4 v5
  = du_linked'45'mono_88 v3 v4 v5
du_linked'45'mono_88 ::
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_linked'45'mono_88 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.Program.du_leaves'45'map_474
      (coe (\ v3 v4 v5 -> coe v0 v3 v4 v5)) (coe (\ v3 v4 v5 v6 -> v6))
      (coe v1) (coe v2)
-- Once.Adequacy.ElaborateLinked.decl-[]
d_decl'45''91''93'_110 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> AgdaAny -> AgdaAny
d_decl'45''91''93'_110 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_decl'45''91''93'_110 v4
du_decl'45''91''93'_110 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> AgdaAny
du_decl'45''91''93'_110 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ElaborateLinked.linked-σ
d_linked'45'σ_132 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_linked'45'σ_132 ~v0 ~v1 v2 v3 = du_linked'45'σ_132 v2 v3
du_linked'45'σ_132 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_linked'45'σ_132 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.du_leaves'45'map_474
      (coe (\ v2 v3 v4 v5 -> v5))
      (coe
         (\ v2 v3 v4 v5 ->
            coe
              du_decl'45''91''93'_110
              (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v4))))
      (coe v0) (coe v1)
-- Once.Adequacy.ElaborateLinked.linkedAt-++
d_linkedAt'45''43''43'_154 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny
d_linkedAt'45''43''43'_154 v0 ~v1 v2 v3 v4 v5
  = du_linkedAt'45''43''43'_154 v0 v2 v3 v4 v5
du_linkedAt'45''43''43'_154 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny
du_linkedAt'45''43''43'_154 v0 v1 v2 v3 v4
  = case coe v0 of
      [] -> coe v4
      (:) v5 v6
        -> coe
             du_linkedAt'45'cons_18 (coe v5) (coe v1) (coe v2) (coe v3)
             (coe
                du_linkedAt'45''43''43'_154 (coe v6) (coe v1) (coe v2) (coe v3)
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.linkedAt-[]
d_linkedAt'45''91''93'_176 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_linkedAt'45''91''93'_176 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_linkedAt'45''91''93'_176
du_linkedAt'45''91''93'_176 :: AgdaAny
du_linkedAt'45''91''93'_176 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.DeclIn
d_DeclIn_178 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_DeclIn_178 = erased
-- Once.Adequacy.ElaborateLinked.RefLinked
d_RefLinked_188 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_RefLinked_188 = erased
-- Once.Adequacy.ElaborateLinked.Refs-map
d_Refs'45'map_234 ::
  Integer ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()) ->
  (MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> AgdaAny -> AgdaAny
d_Refs'45'map_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10 ~v11
                  ~v12 v13 v14 v15
  = du_Refs'45'map_234 v7 v8 v9 v13 v14 v15
du_Refs'45'map_234 ::
  (MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> AgdaAny -> AgdaAny
du_Refs'45'map_234 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_20 v8
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v9 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> coe
                    du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v18) (coe v15)
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_54 v8 v9 v10 v12 v13 v14
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v3))
                       (coe v13) (coe v15))
                    (coe
                       du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v10) (coe v14)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_74 v8 v9 v10 v12 v14 v15 v16
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v10)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v12)
                                           (coe v21))
                                        (coe v19))
                                     (coe v15) (coe v22))
                                  (coe
                                     du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v10)
                                     (coe v16) (coe v23))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_88 v8 v9 v12 v13
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v14) (coe v12)
                              (coe v16))
                           (coe
                              du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v15) (coe v13)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_100 v10 v11
        -> coe
             du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v3) (coe v10))
             (coe v11) (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_112 v9 v11
        -> coe
             du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v9) (coe v3))
             (coe v11) (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_124 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
               -> coe
                    du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v12) (coe v11)
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_136 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
               -> coe
                    du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v13) (coe v11)
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_158 v8 v9 v10 v11 v12 v13 v14 v16 v17 v18
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
               -> case coe v20 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                              (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v13) (coe v14))
                              (coe v16) (coe v19))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v3) (coe v17)
                                 (coe v21))
                              (coe
                                 du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                                 (coe v22)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_unit_164
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_174 v10
        -> coe
             du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v10) (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_190 v8 v9 v10 v11 v13 v14
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v11) (coe v13)
                       (coe v15))
                    (coe
                       du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_196 v8
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_float_204 v8
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_num_218 v9 v10 v11 v12 v13 v14
        -> coe
             du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Theory.du_symDom_86 (coe v9) (coe v11))
             (coe v14) (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_230 v9 v11 v12
        -> coe
             du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v9) (coe v12)
             (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_238 v8 v9 v10
        -> coe v0 v8 v9 v5
      MAlonzo.Code.Once.Surface.Syntax.C_closure_246 v9
        -> coe v1 v3 v9 v5
      MAlonzo.Code.Once.Surface.Syntax.C_poly_256 v8 -> coe v2 v3 v8 v5
      MAlonzo.Code.Once.Surface.Syntax.C_closed_264 v9
        -> coe
             du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
             (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_276 v11
        -> coe v5
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_288 v8 v9 v11 v12
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                    (coe
                       du_Refs'45'map_234 (coe v0) (coe v1) (coe v2) (coe v9) (coe v12)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_306 v8 v9 v11 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v20))
                                        (coe v18))
                                     (coe v14) (coe v21))
                                  (coe
                                     du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v16)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v20))
                                        (coe v11))
                                     (coe v15) (coe v22))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_324 v8 v9 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v16 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v19 v20
                      -> case coe v17 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                             -> case coe v5 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe v19)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v22))
                                               (coe v18))
                                            (coe v14) (coe v23))
                                         (coe
                                            du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v22))
                                               (coe v18))
                                            (coe v15) (coe v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_342 v8 v9 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                      -> case coe v18 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v21 v22
                             -> case coe v5 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe v16)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v20))
                                               (coe v21))
                                            (coe v14) (coe v23))
                                         (coe
                                            du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe v16)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v20))
                                               (coe v22))
                                            (coe v15) (coe v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_360 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                             -> coe
                                  du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v15) (coe v18))
                                     (coe
                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                     (coe v20))
                                  (coe v14) (coe v5)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_376 v8 v10 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                             -> coe
                                  du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v18)
                                        (coe v17))
                                     (coe
                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v20))
                                     (coe v17))
                                  (coe v14) (coe v5)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_394 v8 v10 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v19 v20
                      -> coe
                           du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v16)
                              (coe
                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                 (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v20)))
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v19)
                                 (coe v16)))
                           (coe v15) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_406 v8 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
               -> coe
                    du_Refs'45'map_234 (coe v0) (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_fin_42
                             (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                       (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v14) (coe v12)))
                    (coe v11) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.Linked-subst
d_Linked'45'subst_586 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IRTy.T_IRTy_6) ->
  (AgdaAny -> MAlonzo.Code.Once.IRTy.T_IRTy_6) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_Linked'45'subst_586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_Linked'45'subst_586 v9
du_Linked'45'subst_586 :: AgdaAny -> AgdaAny
du_Linked'45'subst_586 v0 = coe v0
-- Once.Adequacy.ElaborateLinked.linked-[]
d_linked'45''91''93'_604 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_linked'45''91''93'_604 ~v0 ~v1 v2 v3
  = du_linked'45''91''93'_604 v2 v3
du_linked'45''91''93'_604 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_linked'45''91''93'_604 v0 v1
  = coe
      du_linked'45'mono_88
      (\ v2 v3 v4 v5 -> coe du_linkedAt'45''91''93'_176) (coe v0)
      (coe v1)
-- Once.Adequacy.ElaborateLinked.restrictEnv-cf
d_restrictEnv'45'cf_628 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 -> AgdaAny
d_restrictEnv'45'cf_628 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_restrictEnv'45'cf_628 v3 v4 v5 v7
du_restrictEnv'45'cf_628 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 -> AgdaAny
du_restrictEnv'45'cf_628 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v5 v6
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v15 v16
                      -> case coe v2 of
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v18 v19
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                                           -> coe
                                                du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                (coe v19) (coe v13)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                      (coe v19) (coe v13))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                      (coe v19) (coe v13))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                      (coe v19) (coe v13))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                   (coe v19) (coe v13))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                      (coe v19) (coe v13))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                      (coe v19) (coe v13))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                      (coe v19) (coe v13))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                   (coe v19) (coe v13))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                      (coe v19) (coe v13))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                      (coe v19) (coe v13))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      du_restrictEnv'45'cf_628 (coe v5) (coe v16)
                                                      (coe v19) (coe v13))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.projUsed-cf
d_projUsed'45'cf_688 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_projUsed'45'cf_688 ~v0 ~v1 ~v2 v3 v4
  = du_projUsed'45'cf_688 v3 v4
du_projUsed'45'cf_688 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_projUsed'45'cf_688 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du_projUsed'45'cf_688 (coe v3) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.eraseCtx-cf
d_eraseCtx'45'cf_710 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> AgdaAny
d_eraseCtx'45'cf_710 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_eraseCtx'45'cf_710 v3 v5
du_eraseCtx'45'cf_710 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> AgdaAny
du_eraseCtx'45'cf_710 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_eraseCtx'45'cf_710 (coe v3) (coe v7))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe du_eraseCtx'45'cf_710 (coe v3) (coe v7))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe du_eraseCtx'45'cf_710 (coe v3) (coe v7))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.bindEnv-cf
d_bindEnv'45'cf_752 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> AgdaAny
d_bindEnv'45'cf_752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_bindEnv'45'cf_752 v7
du_bindEnv'45'cf_752 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> AgdaAny
du_bindEnv'45'cf_752 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ElaborateLinked.coeIR-cf
d_coeIR'45'cf_768 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 -> AgdaAny
d_coeIR'45'cf_768 ~v0 ~v1 v2 v3 v4 = du_coeIR'45'cf_768 v2 v3 v4
du_coeIR'45'cf_768 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 -> AgdaAny
du_coeIR'45'cf_768 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'var_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v10 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe du_coeIR'45'cf_768 (coe v15) (coe v20) (coe v11))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe du_coeIR'45'cf_768 (coe v15) (coe v20) (coe v11))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     du_coeIR'45'cf_768 (coe v18) (coe v13)
                                                     (coe v10))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe du_coeIR'45'cf_768 (coe v15) (coe v20) (coe v11))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     du_coeIR'45'cf_768 (coe v18) (coe v13)
                                                     (coe v10))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe du_coeIR'45'cf_768 (coe v9) (coe v11) (coe v7))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe du_coeIR'45'cf_768 (coe v10) (coe v12) (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe du_coeIR'45'cf_768 (coe v9) (coe v11) (coe v7)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe du_coeIR'45'cf_768 (coe v10) (coe v12) (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'μ_64
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v6
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.runCoe-linked
d_runCoe'45'linked_804 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_runCoe'45'linked_804 ~v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 v8
  = du_runCoe'45'linked_804 v1 v3 v4 v6 v8
du_runCoe'45'linked_804 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 -> AgdaAny -> AgdaAny
du_runCoe'45'linked_804 v0 v1 v2 v3 v4
  = coe
      du_go_824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Surface.CoerceIR.du_voidFree'63'_350 (coe v1)
         (coe v2) (coe v3))
-- Once.Adequacy.ElaborateLinked._.go
d_go_824 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
d_go_824 ~v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 v9
  = du_go_824 v1 v3 v4 v6 v8 v9
du_go_824 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_go_824 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe seq (coe v7) (coe v4)
             else coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          du_linked'45''91''93'_604
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0) (coe v1))
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0) (coe v2))
                          (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_38
                             (coe v0) (coe v1) (coe v2) (coe v3))
                          (coe du_coeIR'45'cf_768 (coe v1) (coe v2) (coe v3)))
                       (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.eff-decl
d_eff'45'decl_844 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_eff'45'decl_844 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8
  = du_eff'45'decl_844 v0 v5 v6 v7
du_eff'45'decl_844 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
du_eff'45'decl_844 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             else coe
                    seq (coe v5)
                    (case coe v2 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe seq (coe v7) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              else coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Once.ContractLaws.du_answer'45''8712'_100
                                        (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.Linked-substᶜ
d_Linked'45'subst'7580'_878 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_Linked'45'subst'7580'_878 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_Linked'45'subst'7580'_878 v7
du_Linked'45'subst'7580'_878 :: AgdaAny -> AgdaAny
du_Linked'45'subst'7580'_878 v0 = coe v0
-- Once.Adequacy.ElaborateLinked.sigOpIR-linked
d_sigOpIR'45'linked_892 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_sigOpIR'45'linked_892 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sigOpIR'45'linked_892 v0 v3 v5 v6
du_sigOpIR'45'linked_892 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
du_sigOpIR'45'linked_892 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v5
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.ContractLaws.du_value'45''8712'_68 (coe v0)
                   (coe v3))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> coe
                           seq (coe v12)
                           (case coe v13 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.ContractLaws.du_value'45''8712'_68
                                               (coe v0) (coe v3))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               du_eff'45'decl_844 (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58
                                                  (coe v11))
                                               (coe
                                                  MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64
                                                  (coe v11))
                                               (coe v3))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        du_eff'45'decl_844 (coe v0)
                                        (coe MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58 (coe v11))
                                        (coe MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64 (coe v11))
                                        (coe v3))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked.sigOp-linked
d_sigOp'45'linked_1034 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_sigOp'45'linked_1034 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9
  = du_sigOp'45'linked_1034 v0 v5 v8 v9
du_sigOp'45'linked_1034 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
du_sigOp'45'linked_1034 v0 v1 v2 v3
  = coe du_sigOpIR'45'linked_892 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ElaborateLinked._.L
d_L_1056 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_L_1056 = erased
-- Once.Adequacy.ElaborateLinked._.cf
d_cf_1064 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_cf_1064 ~v0 ~v1 v2 v3 = du_cf_1064 v2 v3
du_cf_1064 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_cf_1064 v0 v1 = coe du_linked'45''91''93'_604 (coe v0) (coe v1)
-- Once.Adequacy.ElaborateLinked._.rE
d_rE_1080 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 -> AgdaAny
d_rE_1080 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 v8
  = du_rE_1080 v2 v4 v5 v6 v8
du_rE_1080 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 -> AgdaAny
du_rE_1080 v0 v1 v2 v3 v4
  = coe
      du_cf_1064
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
         (coe v0)
         (coe
            MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
            (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v1) (coe v2))))
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
         (coe v0)
         (coe
            MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
            (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v1) (coe v3))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_126 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
      (coe du_restrictEnv'45'cf_628 (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.ElaborateLinked._.bE
d_bE_1102 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> AgdaAny
d_bE_1102 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 v8
  = du_bE_1102 v2 v4 v5 v6 v8
du_bE_1102 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> AgdaAny
du_bE_1102 v0 v1 v2 v3 v4
  = coe
      du_cf_1064
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0)
            (coe
               MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
               (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v1) (coe v2))))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0) (coe v3)))
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
         (coe v0)
         (coe
            MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
            (coe
               MAlonzo.Code.Once.Context.du__'8638'__64
               (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v1 v3)
               (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v4 v2))))
      (coe MAlonzo.Code.Once.Surface.Elaborate.du_bindEnv_278 (coe v4))
      (coe du_bindEnv'45'cf_752 (coe v4))
-- Once.Adequacy.ElaborateLinked._.elaborate-linked′
d_elaborate'45'linked'8242'_1128 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> AgdaAny -> AgdaAny
d_elaborate'45'linked'8242'_1128 v0 ~v1 v2 ~v3 v4 v5 ~v6 v7 v8 v9
  = du_elaborate'45'linked'8242'_1128 v0 v2 v4 v5 v7 v8 v9
du_elaborate'45'linked'8242'_1128 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> AgdaAny -> AgdaAny
du_elaborate'45'linked'8242'_1128 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_20 v9
        -> coe
             du_cf_1064
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                (coe v1)
                (coe
                   MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                   (coe
                      MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Spec.Context.d_singleUse_50 (coe v2) (coe v9)
                         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))))
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                (coe v1)
                (coe
                   MAlonzo.Code.Once.Spec.Context.du_lookup_22 (coe v3) (coe v9)))
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_projUsed_186 (coe v3)
                (coe v9))
             (coe du_projUsed'45'cf_688 (coe v3) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v10 v16
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  seq (coe v10)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                        (coe addInt (coe (1 :: Integer)) (coe v2))
                                        (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v17)
                                        (coe v19) (coe v16) (coe v6))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                            (coe addInt (coe (1 :: Integer)) (coe v2))
                                            (coe
                                               MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v17)
                                            (coe v19) (coe v16) (coe v6))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                         (coe addInt (coe (1 :: Integer)) (coe v2))
                                         (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v17)
                                         (coe v19) (coe v16) (coe v6)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                            (coe addInt (coe (1 :: Integer)) (coe v2))
                                            (coe
                                               MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v17)
                                            (coe v19) (coe v16) (coe v6))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                         (coe addInt (coe (1 :: Integer)) (coe v2))
                                         (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v17)
                                         (coe v19) (coe v16) (coe v6)
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                         (coe addInt (coe (1 :: Integer)) (coe v2))
                                         (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v17)
                                         (coe v19) (coe v16) (coe v6)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_54 v9 v10 v11 v13 v14 v15
        -> case coe v13 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v13)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                          (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                                    (coe v4))
                                 (coe v14) (coe v16))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                    (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v13)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                                       (coe v4))
                                    (coe v14) (coe v16))
                                 (coe
                                    du_rE_1080 (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v13) (coe v10)))
                                    (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v13) (coe v10)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                    (coe v3) (coe v11) (coe v15) (coe v17))
                                 (coe
                                    du_rE_1080 (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v13) (coe v10)))
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180
                                       (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v13) (coe v10))
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe v13) (coe v10)))
                                       (coe
                                          MAlonzo.Code.Once.Context.du_'8849''7512''45''42'One_194
                                          (coe v10))
                                       (coe
                                          MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                          (coe v9)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe v13) (coe v10)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                    (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v13)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                                       (coe v4))
                                    (coe v14) (coe v16))
                                 (coe
                                    du_rE_1080 (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v13) (coe v10)))
                                    (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v13) (coe v10)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                    (coe v3) (coe v11) (coe v15) (coe v17))
                                 (coe
                                    du_rE_1080 (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v13) (coe v10)))
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180
                                       (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v13) (coe v10))
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe v13) (coe v10)))
                                       (coe
                                          MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                          (coe v10))
                                       (coe
                                          MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                          (coe v9)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe v13) (coe v10)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_74 v9 v10 v11 v13 v15 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                      -> case coe v13 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  du_elaborate'45'linked'8242'_1128 (coe v0)
                                                  (coe v1) (coe v2) (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                     (coe v11)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe v13) (coe v22))
                                                     (coe v20))
                                                  (coe v16) (coe v23))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     du_elaborate'45'linked'8242'_1128 (coe v0)
                                                     (coe v1) (coe v2) (coe v3)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                        (coe v11)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                           (coe v13) (coe v22))
                                                        (coe v20))
                                                     (coe v16) (coe v23))
                                                  (coe
                                                     du_rE_1080 (coe v1) (coe v3)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                        (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                           (coe v13) (coe v10)))
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                                        (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                           (coe v13) (coe v10)))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     du_elaborate'45'linked'8242'_1128 (coe v0)
                                                     (coe v1) (coe v2) (coe v3) (coe v11) (coe v17)
                                                     (coe v24))
                                                  (coe
                                                     du_rE_1080 (coe v1) (coe v3)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                        (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                           (coe v13) (coe v10)))
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                           (coe v13) (coe v10))
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                           (coe v9)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                              (coe v13) (coe v10)))
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du_'8849''7512''45''42'One_194
                                                           (coe v10))
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                                           (coe v9)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                              (coe v13) (coe v10))))))))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     du_elaborate'45'linked'8242'_1128 (coe v0)
                                                     (coe v1) (coe v2) (coe v3)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                        (coe v11)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                           (coe v13) (coe v22))
                                                        (coe v20))
                                                     (coe v16) (coe v23))
                                                  (coe
                                                     du_cf_1064
                                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                        (coe v1)
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                           (coe
                                                              MAlonzo.Code.Once.Context.du__'8638'__64
                                                              (coe v3)
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                 (coe v9)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                    (coe v13) (coe v10))))))
                                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                        (coe v1)
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                           (coe
                                                              MAlonzo.Code.Once.Context.du__'8638'__64
                                                              (coe v3) (coe v9))))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Elaborate.du_env'737'_210
                                                        (coe v1) (coe v3) (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                           (coe v13) (coe v10)))
                                                     (coe
                                                        du_restrictEnv'45'cf_628 (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                           (coe v9)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                              (coe v13) (coe v10)))
                                                        (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                                           (coe v9)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                              (coe v13) (coe v10))))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     du_elaborate'45'linked'8242'_1128 (coe v0)
                                                     (coe v1) (coe v2) (coe v3) (coe v11) (coe v17)
                                                     (coe v24))
                                                  (coe
                                                     du_cf_1064
                                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                        (coe v1)
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                           (coe
                                                              MAlonzo.Code.Once.Context.du__'8638'__64
                                                              (coe v3)
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                 (coe v9)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                    (coe v13) (coe v10))))))
                                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                        (coe v1)
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                           (coe
                                                              MAlonzo.Code.Once.Context.du__'8638'__64
                                                              (coe v3) (coe v10))))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Elaborate.du_env'691'ω_254
                                                        (coe v1) (coe v3) (coe v9) (coe v10))
                                                     (coe
                                                        du_restrictEnv'45'cf_628 (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                           (coe v9)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                              (coe v13) (coe v10)))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180
                                                           (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                              (coe v13) (coe v10))
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                              (coe v9)
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                 (coe v13) (coe v10)))
                                                           (coe
                                                              MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                                              (coe v10))
                                                           (coe
                                                              MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                                              (coe v9)
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                 (coe v13) (coe v10)))))))))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_88 v9 v10 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                 (coe v3) (coe v15) (coe v13) (coe v17))
                              (coe
                                 du_cf_1064
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                    (coe v1)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                       (coe
                                          MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                             (coe v9) (coe v10)))))
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                    (coe v1)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                       (coe
                                          MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3)
                                          (coe v9))))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Elaborate.du_env'737'_210 (coe v1)
                                    (coe v3) (coe v9) (coe v10))
                                 (coe
                                    du_restrictEnv'45'cf_628 (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                       (coe v10))
                                    (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                       (coe v9) (coe v10)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                 (coe v3) (coe v16) (coe v14) (coe v18))
                              (coe
                                 du_cf_1064
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                    (coe v1)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                       (coe
                                          MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                             (coe v9) (coe v10)))))
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                    (coe v1)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                       (coe
                                          MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3)
                                          (coe v10))))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Elaborate.du_env'691'_232 (coe v1)
                                    (coe v3) (coe v9) (coe v10))
                                 (coe
                                    du_restrictEnv'45'cf_628 (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                       (coe v10))
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                       (coe v9) (coe v10)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_100 v11 v12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                (coe v3)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v4) (coe v11))
                (coe v12) (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_112 v10 v12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                (coe v3)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v10) (coe v4))
                (coe v12) (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_124 v12
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v13) (coe v12) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_136 v12
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v14) (coe v12) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_158 v9 v10 v11 v12 v13 v14 v15 v17 v18 v19
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
               -> case coe v21 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                    (coe addInt (coe (1 :: Integer)) (coe v2))
                                    (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v14)
                                    (coe v4) (coe v18) (coe v22))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe du_bE_1102 (coe v1) (coe v3) (coe v10) (coe v14) (coe v12))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             du_rE_1080 (coe v1) (coe v3)
                                             (coe
                                                MAlonzo.Code.Once.Context.du__'8852''7512'__22
                                                (coe v10) (coe v11))
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Once.Context.du_'8849''7512''45''8852''737'_232
                                                (coe v10) (coe v11)))
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                    (coe addInt (coe (1 :: Integer)) (coe v2))
                                    (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v15)
                                    (coe v4) (coe v19) (coe v23))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe du_bE_1102 (coe v1) (coe v3) (coe v11) (coe v15) (coe v13))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             du_rE_1080 (coe v1) (coe v3)
                                             (coe
                                                MAlonzo.Code.Once.Context.du__'8852''7512'__22
                                                (coe v10) (coe v11))
                                             (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.Context.du_'8849''7512''45''8852''691'_248
                                                (coe v10) (coe v11)))
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_rE_1080 (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v10)
                                          (coe v11)))
                                    (coe
                                       MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v10)
                                       (coe v11))
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v10)
                                          (coe v11))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v14)
                                          (coe v15))
                                       (coe v17) (coe v20))
                                    (coe
                                       du_rE_1080 (coe v1) (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                          (coe
                                             MAlonzo.Code.Once.Context.du__'8852''7512'__22
                                             (coe v10) (coe v11)))
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                          (coe v9)
                                          (coe
                                             MAlonzo.Code.Once.Context.du__'8852''7512'__22
                                             (coe v10) (coe v11)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_unit_164
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_174 v11
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v11)
                (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_190 v9 v10 v11 v12 v14 v15
        -> case coe v11 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> coe
                           du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                           (coe addInt (coe (1 :: Integer)) (coe v2))
                           (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v12) (coe v4)
                           (coe v15) (coe v17)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                              (coe addInt (coe (1 :: Integer)) (coe v2))
                              (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v12) (coe v4)
                              (coe v15) (coe v17))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe du_bE_1102 (coe v1) (coe v3) (coe v10) (coe v12) (coe v11))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_rE_1080 (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v11) (coe v9)))
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                       (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v11) (coe v9))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                       (coe v3) (coe v12) (coe v14) (coe v16))
                                    (coe
                                       du_rE_1080 (coe v1) (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                          (coe v10)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe v11) (coe v9)))
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180
                                          (coe v9)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe v11) (coe v9))
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                (coe v11) (coe v9)))
                                          (coe
                                             MAlonzo.Code.Once.Context.du_'8849''7512''45''42'One_194
                                             (coe v9))
                                          (coe
                                             MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                (coe v11) (coe v9))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                              (coe addInt (coe (1 :: Integer)) (coe v2))
                              (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v12) (coe v4)
                              (coe v15) (coe v17))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe du_bE_1102 (coe v1) (coe v3) (coe v10) (coe v12) (coe v11))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_rE_1080 (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v11) (coe v9)))
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                       (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                          (coe v11) (coe v9))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                       (coe v3) (coe v12) (coe v14) (coe v16))
                                    (coe
                                       du_rE_1080 (coe v1) (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                          (coe v10)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe v11) (coe v9)))
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180
                                          (coe v9)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe v11) (coe v9))
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                (coe v11) (coe v9)))
                                          (coe
                                             MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                             (coe v9))
                                          (coe
                                             MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                (coe v11) (coe v9))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_196 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_float_204 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_num_218 v10 v11 v12 v13 v14 v15
        -> coe
             seq (coe v10)
             (coe
                seq (coe v12)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Spec.Theory.du_symDom_86 (coe v10) (coe v12))
                      (coe v15) (coe v6))))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_230 v10 v12 v13
        -> coe
             du_runCoe'45'linked_804 (coe v1) (coe v10) (coe v4) (coe v12)
             (coe
                du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v10) (coe v13) (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_238 v9 v10 v11
        -> coe du_sigOp'45'linked_1034 (coe v0) (coe v9) (coe v11) (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_246 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_256 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_closed_264 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12) (coe v4) (coe v10)
                (coe v6))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_276 v12
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_cf_1064
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1) (coe v13))
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1) (coe v15))
                       (MAlonzo.Code.Once.TypeCheck.Table.d_mapIR_84
                          (coe v1) (coe v13) (coe v15) (coe v12))
                       (coe
                          du_linked'45'σ_132
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1) (coe v13))
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1) (coe v15))
                          (MAlonzo.Code.Once.TypeCheck.Table.d_mapIR_84
                             (coe v1) (coe v13) (coe v15) (coe v12))
                          v6))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_288 v9 v10 v12 v13
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_cf_1064
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1) (coe v10))
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1) (coe v4))
                       (MAlonzo.Code.Once.TypeCheck.Table.d_mapIR_84
                          (coe v1) (coe v10) (coe v4) (coe v12))
                       (coe
                          du_linked'45'σ_132
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1) (coe v10))
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1) (coe v4))
                          (MAlonzo.Code.Once.TypeCheck.Table.d_mapIR_84
                             (coe v1) (coe v10) (coe v4) (coe v12))
                          v14))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v10) (coe v13) (coe v15))
                       (coe
                          du_rE_1080 (coe v1) (coe v3)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                             (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44 (coe v2))
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44 (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206 (coe v9))
                             (coe
                                MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44 (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_306 v9 v10 v12 v15 v16
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                           (coe v2) (coe v3)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                              (coe v12)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v21))
                                              (coe v19))
                                           (coe v15) (coe v22))
                                        (coe
                                           du_cf_1064
                                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                 (coe
                                                    MAlonzo.Code.Once.Context.du__'8638'__64
                                                    (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                       (coe v9)
                                                       (coe
                                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v10))))))
                                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                 (coe
                                                    MAlonzo.Code.Once.Context.du__'8638'__64
                                                    (coe v3) (coe v9))))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Elaborate.du_env'737'_210
                                              (coe v1) (coe v3) (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v10)))
                                           (coe
                                              du_restrictEnv'45'cf_628 (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                    (coe v10)))
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                    (coe v10))))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1)
                                           (coe v2) (coe v3)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                              (coe v17)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v21))
                                              (coe v12))
                                           (coe v16) (coe v23))
                                        (coe
                                           du_cf_1064
                                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                 (coe
                                                    MAlonzo.Code.Once.Context.du__'8638'__64
                                                    (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                       (coe v9)
                                                       (coe
                                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v10))))))
                                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                 (coe
                                                    MAlonzo.Code.Once.Context.du__'8638'__64
                                                    (coe v3) (coe v10))))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Elaborate.du_env'691'ω_254
                                              (coe v1) (coe v3) (coe v9) (coe v10))
                                           (coe
                                              du_restrictEnv'45'cf_628 (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                    (coe v10)))
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180
                                                 (coe v10)
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                    (coe v10))
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                    (coe v9)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v10)))
                                                 (coe
                                                    MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                                    (coe v10))
                                                 (coe
                                                    MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                                    (coe v9)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v10))))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_324 v9 v10 v15 v16
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v20 v21
                      -> case coe v18 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v22 v23
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  du_elaborate'45'linked'8242'_1128 (coe v0)
                                                  (coe v1) (coe v2) (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                     (coe v20)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v23))
                                                     (coe v19))
                                                  (coe v15) (coe v24))
                                               (coe
                                                  du_cf_1064
                                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du__'8638'__64
                                                           (coe v3)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                              (coe v9) (coe v10)))))
                                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du__'8638'__64
                                                           (coe v3) (coe v9))))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Elaborate.du_env'737'_210
                                                     (coe v1) (coe v3) (coe v9) (coe v10))
                                                  (coe
                                                     du_restrictEnv'45'cf_628 (coe v3)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                        (coe v9) (coe v10))
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                                        (coe v9) (coe v10)))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  du_elaborate'45'linked'8242'_1128 (coe v0)
                                                  (coe v1) (coe v2) (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                     (coe v21)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v23))
                                                     (coe v19))
                                                  (coe v16) (coe v25))
                                               (coe
                                                  du_cf_1064
                                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du__'8638'__64
                                                           (coe v3)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                              (coe v9) (coe v10)))))
                                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du__'8638'__64
                                                           (coe v3) (coe v10))))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Elaborate.du_env'691'_232
                                                     (coe v1) (coe v3) (coe v9) (coe v10))
                                                  (coe
                                                     du_restrictEnv'45'cf_628 (coe v3)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                        (coe v9) (coe v10))
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                                        (coe v9) (coe v10))))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_342 v9 v10 v15 v16
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v19 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v22 v23
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  du_elaborate'45'linked'8242'_1128 (coe v0)
                                                  (coe v1) (coe v2) (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                     (coe v17)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v21))
                                                     (coe v22))
                                                  (coe v15) (coe v24))
                                               (coe
                                                  du_cf_1064
                                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du__'8638'__64
                                                           (coe v3)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                              (coe v9) (coe v10)))))
                                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du__'8638'__64
                                                           (coe v3) (coe v9))))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Elaborate.du_env'737'_210
                                                     (coe v1) (coe v3) (coe v9) (coe v10))
                                                  (coe
                                                     du_restrictEnv'45'cf_628 (coe v3)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                        (coe v9) (coe v10))
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126
                                                        (coe v9) (coe v10)))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  du_elaborate'45'linked'8242'_1128 (coe v0)
                                                  (coe v1) (coe v2) (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                     (coe v17)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v21))
                                                     (coe v23))
                                                  (coe v16) (coe v25))
                                               (coe
                                                  du_cf_1064
                                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du__'8638'__64
                                                           (coe v3)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                              (coe v9) (coe v10)))))
                                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                        (coe
                                                           MAlonzo.Code.Once.Context.du__'8638'__64
                                                           (coe v3) (coe v10))))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Elaborate.du_env'691'_232
                                                     (coe v1) (coe v3) (coe v9) (coe v10))
                                                  (coe
                                                     du_restrictEnv'45'cf_628 (coe v3)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                        (coe v9) (coe v10))
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                                        (coe v9) (coe v10))))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_360 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v22 v23
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                  (coe
                                     du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                     (coe v3)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v16)
                                           (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v23))
                                        (coe v21))
                                     (coe v15) (coe v6))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_376 v9 v11 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v16 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v19
                      -> case coe v17 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                        (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                              (coe v19) (coe v18))
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v21))
                                           (coe v18))
                                        (coe v15) (coe v6))
                                     (coe
                                        du_rE_1080 (coe v1) (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                                        (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                           (coe v9))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_394 v9 v11 v15 v16
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v20 v21
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v21)))
                                    (coe
                                       MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v20)
                                       (coe v17)))
                                 (coe v16) (coe v6))
                              (coe
                                 du_rE_1080 (coe v1) (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_406 v9 v12
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                             (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v15) (coe v13)))
                          (coe v12) (coe v6))
                       (coe
                          du_rE_1080 (coe v1) (coe v3)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                             (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ElaborateLinked._.bin
d_bin_1150 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin_1150 v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_bin_1150 v0 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_bin_1150 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin_1150 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v6) (coe v8) (coe v10))
         (coe
            du_cf_1064
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
               (coe v1)
               (coe
                  MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                  (coe
                     MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v4)
                        (coe v5)))))
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
               (coe v1)
               (coe
                  MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                  (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3) (coe v4))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_env'737'_210 (coe v1)
               (coe v3) (coe v4) (coe v5))
            (coe
               du_restrictEnv'45'cf_628 (coe v3)
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v4)
                  (coe v5))
               (coe v4)
               (coe
                  MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126 (coe v4)
                  (coe v5)))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v7) (coe v9) (coe v11))
         (coe
            du_cf_1064
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
               (coe v1)
               (coe
                  MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                  (coe
                     MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v4)
                        (coe v5)))))
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
               (coe v1)
               (coe
                  MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                  (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3) (coe v5))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_env'691'_232 (coe v1)
               (coe v3) (coe v4) (coe v5))
            (coe
               du_restrictEnv'45'cf_628 (coe v3)
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v4)
                  (coe v5))
               (coe v5)
               (coe
                  MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142 (coe v4)
                  (coe v5)))))
-- Once.Adequacy.ElaborateLinked._.elaborate-linked
d_elaborate'45'linked_1700 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elaborate'45'linked_1700 v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_elaborate'45'linked_1700 v0 v2 v4 v5 v6 v7 v8 v9
du_elaborate'45'linked_1700 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elaborate'45'linked_1700 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_elaborate'45'linked'8242'_1128 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v5) (coe v6) (coe v7))
      (coe
         du_cf_1064
         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
            (coe v1)
            (coe
               MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14 (coe v3)))
         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
            (coe v1)
            (coe
               MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
               (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v3) (coe v4))))
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_eraseCtx_896 (coe v1)
            (coe v3) (coe v4))
         (coe du_eraseCtx'45'cf_710 (coe v3) (coe v4)))
