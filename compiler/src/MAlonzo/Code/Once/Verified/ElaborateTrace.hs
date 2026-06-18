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

module MAlonzo.Code.Once.Verified.ElaborateTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.Verified.DenotTrace
import qualified MAlonzo.Code.Once.Verified.SourceSemantics
import qualified MAlonzo.Code.Once.Verified.Trace
import qualified MAlonzo.Code.Once.Verified.TraceMonad
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Verified.ElaborateTrace.take-determines
d_take'45'determines_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'determines_16 = erased
-- Once.Verified.ElaborateTrace.distribute-inl-probe
d_distribute'45'inl'45'probe_76 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distribute'45'inl'45'probe_76 = erased
-- Once.Verified.ElaborateTrace.cname
d_cname_84 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_cname_84 v0
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
      (coe
         MAlonzo.Code.Data.List.Base.du_replicate_278 (coe v0) (coe 'a'))
-- Once.Verified.ElaborateTrace.n∸si≢n
d_n'8760'si'8802'n_92 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8760'si'8802'n_92 = erased
-- Once.Verified.ElaborateTrace.cname-inj
d_cname'45'inj_106 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cname'45'inj_106 = erased
-- Once.Verified.ElaborateTrace.cname-≢
d_cname'45''8802'_118 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cname'45''8802'_118 = erased
-- Once.Verified.ElaborateTrace.lookupEnv-skip
d_lookupEnv'45'skip_132 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupEnv'45'skip_132 = erased
-- Once.Verified.ElaborateTrace._._~⟨_⟩_
d__'126''10216'_'10217'__178 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> ()
d__'126''10216'_'10217'__178 = erased
-- Once.Verified.ElaborateTrace._.CompSim
d_CompSim_182 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_CompSim_182 = erased
-- Once.Verified.ElaborateTrace._.ResultRel
d_ResultRel_186 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> ()
d_ResultRel_186 = erased
-- Once.Verified.ElaborateTrace._.EnvRel
d_EnvRel_272 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 -> AgdaAny -> ()
d_EnvRel_272 = erased
-- Once.Verified.ElaborateTrace._.proj-trace
d_proj'45'trace_304 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'45'trace_304 = erased
-- Once.Verified.ElaborateTrace._.envrel-lookup
d_envrel'45'lookup_336 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_envrel'45'lookup_336 ~v0 v1 v2 v3 ~v4 v5 v6
  = du_envrel'45'lookup_336 v1 v2 v3 v5 v6
du_envrel'45'lookup_336 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_envrel'45'lookup_336 v0 v1 v2 v3 v4
  = let v5 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v7 v8 v9
           -> case coe v2 of
                MAlonzo.Code.Data.Fin.Base.C_zero_12
                  -> case coe v3 of
                       (:) v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> case coe v4 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                              -> let v19
                                                       = coe
                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                           erased
                                                           (\ v19 ->
                                                              coe
                                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                (coe d_cname_84 (coe v5)))
                                                           (coe
                                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                              (coe d_cname_84 (coe v5))
                                                              (coe d_cname_84 (coe v5))) in
                                                 coe
                                                   (case coe v19 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                        -> if coe v20
                                                             then coe
                                                                    seq (coe v21)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v14)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          erased (coe v18)))
                                                             else coe
                                                                    seq (coe v21)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Data.Fin.Base.C_suc_16 v11
                  -> case coe v3 of
                       (:) v12 v13
                         -> coe
                              seq (coe v12)
                              (case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                   -> case coe v15 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                          -> let v18
                                                   = coe
                                                       du_envrel'45'lookup_336 (coe v5) (coe v7)
                                                       (coe v11) (coe v13) (coe v16) in
                                             coe
                                               (case coe v18 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                    -> case coe v20 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v19)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased (coe v22))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.ElaborateTrace._.cs-var
d_cs'45'var_470 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'var_470 ~v0 v1 v2 v3 ~v4 v5 v6
  = du_cs'45'var_470 v1 v2 v3 v5 v6
du_cs'45'var_470 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'var_470 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_envrel'45'lookup_336 (coe v0) (coe v1) (coe v2) (coe v3)
              (coe v4) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v9)))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.ElaborateTrace._._.op-eq
d_op'45'eq_512 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq_512 = erased
-- Once.Verified.ElaborateTrace._.cs-lam
d_cs'45'lam_548 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'lam_548 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_cs'45'lam_548 v1 v9 v10 v11
du_cs'45'lam_548 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'lam_548 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Verified.SourceSemantics.C_Vclos_46 (coe v1)
            (coe d_cname_84 (coe v0)) (coe v2))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe du_vsim_584 (coe v3))))))
-- Once.Verified.ElaborateTrace._._.op-eq
d_op'45'eq_578 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq_578 = erased
-- Once.Verified.ElaborateTrace._._.vsim
d_vsim_584 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_vsim_584 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12 v13
           v14
  = du_vsim_584 v11 v12 v13 v14
du_vsim_584 ::
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_vsim_584 v0 v1 v2 v3
  = let v4 = coe v0 v1 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> case coe v10 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> coe
                                     seq (coe v12)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe addInt (coe (1 :: Integer)) (coe v5))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                 (coe v12)))))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.ElaborateTrace._.cs-unit
d_cs'45'unit_628 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'unit_628 ~v0 ~v1 ~v2 ~v3 = du_cs'45'unit_628
du_cs'45'unit_628 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'unit_628
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Once.Verified.SourceSemantics.C_Vunit_36)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
-- Once.Verified.ElaborateTrace._.cs-int
d_cs'45'int_648 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'int_648 ~v0 ~v1 v2 ~v3 ~v4 = du_cs'45'int_648 v2
du_cs'45'int_648 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'int_648 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Verified.SourceSemantics.C_Vint_32
            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
-- Once.Verified.ElaborateTrace._.cs-str
d_cs'45'str_670 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'str_670 ~v0 ~v1 v2 ~v3 ~v4 = du_cs'45'str_670 v2
du_cs'45'str_670 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'str_670 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Once.Verified.SourceSemantics.C_Vstr_34 (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
-- Once.Verified.ElaborateTrace._.cs-pair
d_cs'45'pair_708 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'pair_708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12
  = du_cs'45'pair_708 v11 v12
du_cs'45'pair_708 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'pair_708 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v1 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> case coe v15 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                         -> case coe v17 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                -> case coe v19 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                       -> coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe
                                                                               addInt
                                                                               (coe (1 :: Integer))
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                  (coe v2)
                                                                                  (coe v12)))
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Verified.SourceSemantics.C_Vpair_38
                                                                                  (coe v4)
                                                                                  (coe v14))
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                     (coe v6)
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                        (coe v16)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     erased
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        erased
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v11)
                                                                                           (coe
                                                                                              v21))))))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._._.op-eq
d_op'45'eq_760 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq_760 = erased
-- Once.Verified.ElaborateTrace._.cs-let
d_cs'45'let_806 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'let_806 ~v0 v1 v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 v12
                v13
  = du_cs'45'let_806 v1 v2 v4 v7 v12 v13
du_cs'45'let_806 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'let_806 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> case coe v13 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                    -> let v16
                                             = coe
                                                 v5 v8
                                                 (coe
                                                    MAlonzo.Code.Once.Verified.TraceMonad.du_valueT_70
                                                    (coe
                                                       MAlonzo.Code.Once.Verified.DenotTrace.d_eval'7472'_154
                                                       (coe v0) (coe v1) (coe v2) (coe v3))
                                                    (coe (0 :: Integer)))
                                                 v15 in
                                       coe
                                         (case coe v16 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                              -> case coe v18 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                     -> case coe v20 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                            -> case coe v22 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                   -> case coe v24 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                          -> coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe
                                                                                  addInt
                                                                                  (coe
                                                                                     (1 :: Integer))
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                     (coe v6)
                                                                                     (coe v17)))
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe v19)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                        (coe v10)
                                                                                        (coe v21))
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        erased
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           erased
                                                                                           (coe
                                                                                              v26)))))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._._.op-eq
d_op'45'eq_902 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq_902 = erased
-- Once.Verified.ElaborateTrace._.cs-app
d_cs'45'app_950 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'app_950 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11 v12
                v13
  = du_cs'45'app_950 v1 v2 v6 v8 v12 v13
du_cs'45'app_950 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'app_950 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> case coe v13 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                    -> case coe v5 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                           -> case coe v17 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                  -> case coe v19 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                         -> case coe v21 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                -> case coe v23 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                       -> let v26
                                                                                = coe
                                                                                    v15 v18
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Verified.TraceMonad.du_valueT_70
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Verified.DenotTrace.d_eval'7472'_154
                                                                                          (coe v0)
                                                                                          (coe v1)
                                                                                          (coe v2)
                                                                                          (coe v3))
                                                                                       (coe
                                                                                          (0 ::
                                                                                             Integer)))
                                                                                    v25 in
                                                                          coe
                                                                            (case coe v26 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                 -> case coe v28 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                        -> case coe
                                                                                                  v30 of
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                               -> case coe
                                                                                                         v32 of
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                      -> case coe
                                                                                                                v34 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                             -> coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                  (coe
                                                                                                                     addInt
                                                                                                                     (coe
                                                                                                                        (1 ::
                                                                                                                           Integer))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                        (coe
                                                                                                                           v6)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                           (coe
                                                                                                                              v16)
                                                                                                                           (coe
                                                                                                                              v27))))
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                     (coe
                                                                                                                        v29)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                                                           (coe
                                                                                                                              v10)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                                                              (coe
                                                                                                                                 v20)
                                                                                                                              (coe
                                                                                                                                 v31)))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           erased
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                              erased
                                                                                                                              (coe
                                                                                                                                 v36)))))
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._._.op-eq
d_op'45'eq_1066 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq_1066 = erased
-- Once.Verified.ElaborateTrace._._.tr-eq
d_tr'45'eq_1084 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tr'45'eq_1084 = erased
-- Once.Verified.ElaborateTrace._.cs-case
d_cs'45'case_1142 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'case_1142 ~v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
                  ~v13 ~v14 ~v15 v16 v17 v18
  = du_cs'45'case_1142 v1 v2 v3 v5 v9 v16 v17 v18
du_cs'45'case_1142 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'case_1142 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v13 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> case coe v15 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                    -> let v18
                                             = coe
                                                 MAlonzo.Code.Once.Verified.DenotTrace.d_eval'7472'_154
                                                 v0
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'43'__128 (coe v1)
                                                    (coe v2))
                                                 v3 v4 (0 :: Integer) in
                                       coe
                                         (case coe v18 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                              -> case coe v20 of
                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                                                     -> case coe v10 of
                                                          MAlonzo.Code.Once.Verified.SourceSemantics.C_Vinl_40 v22
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    addInt (coe (1 :: Integer))
                                                                    (coe
                                                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                       (coe v8)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                          (coe v6 v22 v21 v17))))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                          (coe v6 v22 v21 v17)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                          (coe v12)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                   (coe
                                                                                      v6 v22 v21
                                                                                      v17)))))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          erased
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             erased
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                            (coe
                                                                                               v6
                                                                                               v22
                                                                                               v21
                                                                                               v17))))))))))
                                                          _ -> erased
                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                                                     -> case coe v10 of
                                                          MAlonzo.Code.Once.Verified.SourceSemantics.C_Vinr_42 v22
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    addInt (coe (1 :: Integer))
                                                                    (coe
                                                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                       (coe v8)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                          (coe v7 v22 v21 v17))))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                          (coe v7 v22 v21 v17)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                          (coe v12)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                   (coe
                                                                                      v7 v22 v21
                                                                                      v17)))))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          erased
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             erased
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                            (coe
                                                                                               v7
                                                                                               v22
                                                                                               v21
                                                                                               v17))))))))))
                                                          _ -> erased
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.op-eq-destruct-l
d_op'45'eq'45'destruct'45'l_1174 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq'45'destruct'45'l_1174 = erased
-- Once.Verified.ElaborateTrace._.op-eq-destruct-r
d_op'45'eq'45'destruct'45'r_1246 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq'45'destruct'45'r_1246 = erased
-- Once.Verified.ElaborateTrace._.op-eq-builtin1
d_op'45'eq'45'builtin1_1962 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq'45'builtin1_1962 = erased
-- Once.Verified.ElaborateTrace._.cs-fst
d_cs'45'fst_2026 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'fst_2026 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_cs'45'fst_2026 v9
du_cs'45'fst_2026 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'fst_2026 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Verified.SourceSemantics.C_Vpair_38 v11 v12
                                           -> case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe addInt (coe (2 :: Integer)) (coe v1))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v11)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v5)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased (coe v13)))))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.cs-snd
d_cs'45'snd_2370 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'snd_2370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_cs'45'snd_2370 v9
du_cs'45'snd_2370 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'snd_2370 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Verified.SourceSemantics.C_Vpair_38 v11 v12
                                           -> case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe addInt (coe (2 :: Integer)) (coe v1))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v5)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased (coe v14)))))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.cs-inl
d_cs'45'inl_2716 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'inl_2716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_cs'45'inl_2716 v10
du_cs'45'inl_2716 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'inl_2716 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe addInt (coe (2 :: Integer)) (coe v1))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.Verified.SourceSemantics.C_Vinl_40
                                               (coe v3))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased (coe v10)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.cs-inr
d_cs'45'inr_2772 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'inr_2772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_cs'45'inr_2772 v10
du_cs'45'inr_2772 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'inr_2772 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe addInt (coe (2 :: Integer)) (coe v1))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.Verified.SourceSemantics.C_Vinr_42
                                               (coe v3))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased (coe v10)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.cs-absurd
d_cs'45'absurd_2822 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'absurd_2822 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_cs'45'absurd_2822
du_cs'45'absurd_2822 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'absurd_2822
  = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
-- Once.Verified.ElaborateTrace._.int-val
d_int'45'val_2838 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_int'45'val_2838 ~v0 v1 ~v2 v3 = du_int'45'val_2838 v1 v3
du_int'45'val_2838 ::
  MAlonzo.Code.Once.Verified.SourceSemantics.T_Value_30 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_int'45'val_2838 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Verified.SourceSemantics.C_Vint_32 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.op-eq-binop
d_op'45'eq'45'binop_2892 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq'45'binop_2892 = erased
-- Once.Verified.ElaborateTrace._.cs-add
d_cs'45'add_2960 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'add_2960 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_cs'45'add_2960 v9 v10
du_cs'45'add_2960 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'add_2960 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v1 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> case coe v15 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                         -> case coe v17 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                -> case coe v19 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                       -> let v22
                                                                                = coe
                                                                                    du_int'45'val_2838
                                                                                    (coe v4)
                                                                                    (coe v11) in
                                                                          coe
                                                                            (let v23
                                                                                   = coe
                                                                                       du_int'45'val_2838
                                                                                       (coe v14)
                                                                                       (coe v21) in
                                                                             coe
                                                                               (case coe v22 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                    -> coe
                                                                                         seq
                                                                                         (coe v25)
                                                                                         (case coe
                                                                                                 v23 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                              -> coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v27)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                      (coe
                                                                                                         addInt
                                                                                                         (coe
                                                                                                            (1 ::
                                                                                                               Integer))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                            (coe
                                                                                                               v2)
                                                                                                            (coe
                                                                                                               v12)))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Verified.SourceSemantics.C_Vint_32
                                                                                                            (coe
                                                                                                               addInt
                                                                                                               (coe
                                                                                                                  v24)
                                                                                                               (coe
                                                                                                                  v26)))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                                               (coe
                                                                                                                  v6)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                                                  (coe
                                                                                                                     v16)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               erased
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                  erased
                                                                                                                  erased)))))
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.cs-sub
d_cs'45'sub_3080 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'sub_3080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_cs'45'sub_3080 v9 v10
du_cs'45'sub_3080 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'sub_3080 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v1 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> case coe v15 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                         -> case coe v17 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                -> case coe v19 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                       -> let v22
                                                                                = coe
                                                                                    du_int'45'val_2838
                                                                                    (coe v4)
                                                                                    (coe v11) in
                                                                          coe
                                                                            (let v23
                                                                                   = coe
                                                                                       du_int'45'val_2838
                                                                                       (coe v14)
                                                                                       (coe v21) in
                                                                             coe
                                                                               (case coe v22 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                    -> coe
                                                                                         seq
                                                                                         (coe v25)
                                                                                         (case coe
                                                                                                 v23 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                              -> coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v27)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                      (coe
                                                                                                         addInt
                                                                                                         (coe
                                                                                                            (1 ::
                                                                                                               Integer))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                            (coe
                                                                                                               v2)
                                                                                                            (coe
                                                                                                               v12)))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Verified.SourceSemantics.C_Vint_32
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                                               v24
                                                                                                               v26))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                                               (coe
                                                                                                                  v6)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                                                  (coe
                                                                                                                     v16)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               erased
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                  erased
                                                                                                                  erased)))))
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.cs-mul
d_cs'45'mul_3200 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'mul_3200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_cs'45'mul_3200 v9 v10
du_cs'45'mul_3200 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'mul_3200 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v1 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> case coe v15 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                         -> case coe v17 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                -> case coe v19 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                       -> let v22
                                                                                = coe
                                                                                    du_int'45'val_2838
                                                                                    (coe v4)
                                                                                    (coe v11) in
                                                                          coe
                                                                            (let v23
                                                                                   = coe
                                                                                       du_int'45'val_2838
                                                                                       (coe v14)
                                                                                       (coe v21) in
                                                                             coe
                                                                               (case coe v22 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                    -> coe
                                                                                         seq
                                                                                         (coe v25)
                                                                                         (case coe
                                                                                                 v23 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                              -> coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v27)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                      (coe
                                                                                                         addInt
                                                                                                         (coe
                                                                                                            (1 ::
                                                                                                               Integer))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                            (coe
                                                                                                               v2)
                                                                                                            (coe
                                                                                                               v12)))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Verified.SourceSemantics.C_Vint_32
                                                                                                            (coe
                                                                                                               mulInt
                                                                                                               (coe
                                                                                                                  v24)
                                                                                                               (coe
                                                                                                                  v26)))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                                               (coe
                                                                                                                  v6)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                                                  (coe
                                                                                                                     v16)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               erased
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                  erased
                                                                                                                  erased)))))
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.cs-neg
d_cs'45'neg_3312 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'neg_3312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_cs'45'neg_3312 v6
du_cs'45'neg_3312 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'neg_3312 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> let v11 = coe du_int'45'val_2838 (coe v3) (coe v10) in
                                       coe
                                         (case coe v11 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                              -> coe
                                                   seq (coe v13)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe addInt (coe (1 :: Integer)) (coe v1))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Verified.SourceSemantics.C_Vint_32
                                                            (coe (0 :: Integer)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v5)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               erased
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  erased erased)))))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._._.op-eq
d_op'45'eq_3372 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'eq_3372 = erased
-- Once.Verified.ElaborateTrace._.cs-arr
d_cs'45'arr_3406 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cs'45'arr_3406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_cs'45'arr_3406 v9
du_cs'45'arr_3406 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cs'45'arr_3406 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased (coe v10)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.erase
d_erase_3436 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_erase_3436 ~v0 v1 ~v2 ~v3 v4 v5 = du_erase_3436 v1 v4 v5
du_erase_3436 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
du_erase_3436 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_182 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
             (coe
                d_cname_84
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0
                   (addInt
                      (coe (1 :: Integer))
                      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v5)))))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198 v6 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 (coe d_cname_84 (coe v0))
                    (coe
                       du_erase_3436 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v14)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_214 v5 v6 v7 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
             (coe
                du_erase_3436 (coe v0)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v7)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v9)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v1))
                (coe v10))
             (coe du_erase_3436 (coe v0) (coe v7) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_228 v5 v6 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                    (coe
                       du_erase_3436 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                          (coe v13))
                       (coe v9))
                    (coe du_erase_3436 (coe v0) (coe v7) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v5 v6 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46
                    (coe du_erase_3436 (coe v0) (coe v11) (coe v9))
                    (coe du_erase_3436 (coe v0) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
             (coe
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                (coe ("fst" :: Data.Text.Text)))
             (coe
                du_erase_3436 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v7))
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v6 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
             (coe
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                (coe ("snd" :: Data.Text.Text)))
             (coe
                du_erase_3436 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v6) (coe v1))
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_278 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                       (coe ("inl" :: Data.Text.Text)))
                    (coe du_erase_3436 (coe v0) (coe v9) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_290 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                       (coe ("inr" :: Data.Text.Text)))
                    (coe du_erase_3436 (coe v0) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_312 v5 v6 v7 v8 v9 v10 v11 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48
             (coe
                du_erase_3436 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v10) (coe v11))
                (coe v13))
             (coe d_cname_84 (coe v0))
             (coe
                du_erase_3436 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
                (coe v14))
             (coe d_cname_84 (coe v0))
             (coe
                du_erase_3436 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
                (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_318
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_328 v7
        -> coe
             du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_124)
             (coe v7)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v5 v6 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 (coe d_cname_84 (coe v0))
             (coe du_erase_3436 (coe v0) (coe v8) (coe v10))
             (coe
                du_erase_3436 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_int_350 v5
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_str_356 v5
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_add_366 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_376 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_386 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_div_396 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_406 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_414 v6
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_424 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_le_434 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_444 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_454 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_464 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_474 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28)
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v7))
             (coe
                du_erase_3436 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_486 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
               -> coe
                    du_erase_3436 (coe v0)
                    (coe MAlonzo.Code.Once.Type.d__'8658'__150 (coe v9) (coe v11))
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494 v6
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_502 v6
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_512 v5
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_524 v8
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_536 v5 v6 v8 v9
        -> coe du_erase_3436 (coe v0) (coe v6) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_cata_548 v8 v9
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
      MAlonzo.Code.Once.Surface.Syntax.C_ana_560 v8 v9
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.ElaborateTrace._.canonical-no-shadow
d_canonical'45'no'45'shadow_3560
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.ElaborateTrace._.canonical-no-shadow"
-- Once.Verified.ElaborateTrace._.bridge
d_bridge_3580 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bridge_3580 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = coe d_bridge'45'hole_3600 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 in
    coe
      (case coe v6 of
         MAlonzo.Code.Once.Surface.Syntax.C_var_182 v13
           -> coe
                du_cs'45'var_470 (coe v2) (coe v3) (coe v13) (coe v8) (coe v9)
         MAlonzo.Code.Once.Surface.Syntax.C_lam_198 v14 v19
           -> case coe v5 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v20 v21 v22
                  -> coe
                       du_cs'45'lam_548 (coe v2) (coe v8)
                       (coe
                          du_erase_3436 (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v22)
                          (coe v19))
                       (coe
                          (\ v23 v24 v25 ->
                             d_bridge_3580
                               (coe v0) (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v3) (coe v20))
                               (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v14 v4)
                               (coe v22) (coe v19)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v24))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe d_cname_84 (coe v2)) (coe v23))
                                  (coe v8))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                     (coe v25)))))
                _ -> coe v10
         MAlonzo.Code.Once.Surface.Syntax.C_app_214 v13 v14 v15 v17 v18 v19
           -> coe
                du_cs'45'app_950
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_'10214'_'10215''7580'_44
                   (coe v3))
                (coe v15)
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_118 (coe v3)
                   (coe v15) (coe v1) (coe v19))
                (coe v7)
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v15)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v17)
                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                      (coe v5))
                   (coe v18) (coe v7) (coe v8) (coe v9))
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                   (coe v15) (coe v19) (coe v7) (coe v8) (coe v9))
         MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v13 v14 v17 v18
           -> case coe v5 of
                MAlonzo.Code.Once.Type.C__'42'__126 v19 v20
                  -> coe
                       du_cs'45'pair_708
                       (coe
                          d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                          (coe v19) (coe v17) (coe v7) (coe v8) (coe v9))
                       (coe
                          d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                          (coe v20) (coe v18) (coe v7) (coe v8) (coe v9))
                _ -> coe v10
         MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v15 v16
           -> coe
                du_cs'45'fst_2026
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v5) (coe v15))
                   (coe v16) (coe v7) (coe v8) (coe v9))
         MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v14 v16
           -> coe
                du_cs'45'snd_2370
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v14) (coe v5))
                   (coe v16) (coe v7) (coe v8) (coe v9))
         MAlonzo.Code.Once.Surface.Syntax.C_inl''_278 v16
           -> case coe v5 of
                MAlonzo.Code.Once.Type.C__'43'__128 v17 v18
                  -> coe
                       du_cs'45'inl_2716
                       (coe
                          d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v17) (coe v16) (coe v7) (coe v8) (coe v9))
                _ -> coe v10
         MAlonzo.Code.Once.Surface.Syntax.C_inr''_290 v16
           -> case coe v5 of
                MAlonzo.Code.Once.Type.C__'43'__128 v17 v18
                  -> coe
                       du_cs'45'inr_2772
                       (coe
                          d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v18) (coe v16) (coe v7) (coe v8) (coe v9))
                _ -> coe v10
         MAlonzo.Code.Once.Surface.Syntax.C_case''_312 v13 v14 v15 v16 v17 v18 v19 v21 v22 v23
           -> coe
                du_cs'45'case_1142
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_'10214'_'10215''7580'_44
                   (coe v3))
                (coe v18) (coe v19)
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_118 (coe v3)
                   (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v18) (coe v19))
                   (coe v1) (coe v21))
                (coe v7)
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                   (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v18) (coe v19))
                   (coe v21) (coe v7) (coe v8) (coe v9))
                (coe
                   (\ v24 v25 v26 ->
                      d_bridge_3580
                        (coe v0) (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v3) (coe v18))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v16 v14)
                        (coe v5) (coe v22)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v25))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe d_cname_84 (coe v2)) (coe v24))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v26)))))
                (coe
                   (\ v24 v25 v26 ->
                      d_bridge_3580
                        (coe v0) (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v3) (coe v19))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v17 v15)
                        (coe v5) (coe v23)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v25))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe d_cname_84 (coe v2)) (coe v24))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v26)))))
         MAlonzo.Code.Once.Surface.Syntax.C_unit_318
           -> coe du_cs'45'unit_628
         MAlonzo.Code.Once.Surface.Syntax.C_absurd_328 v15
           -> coe du_cs'45'absurd_2822
         MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v13 v14 v15 v16 v18 v19
           -> coe
                du_cs'45'let_806
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_'10214'_'10215''7580'_44
                   (coe v3))
                (coe v16)
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_118 (coe v3)
                   (coe v16) (coe v1) (coe v18))
                (coe v7)
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                   (coe v16) (coe v18) (coe v7) (coe v8) (coe v9))
                (coe
                   (\ v20 v21 v22 ->
                      d_bridge_3580
                        (coe v0) (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v3) (coe v16))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v15 v14)
                        (coe v5) (coe v19)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v21))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe d_cname_84 (coe v2)) (coe v20))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v22)))))
         MAlonzo.Code.Once.Surface.Syntax.C_int_350 v13
           -> coe du_cs'45'int_648 (coe v13)
         MAlonzo.Code.Once.Surface.Syntax.C_str_356 v13
           -> coe du_cs'45'str_670 (coe v13)
         MAlonzo.Code.Once.Surface.Syntax.C_add_366 v13 v14 v15 v16
           -> coe
                du_cs'45'add_2960
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                   (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v15) (coe v7) (coe v8)
                   (coe v9))
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                   (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v16) (coe v7) (coe v8)
                   (coe v9))
         MAlonzo.Code.Once.Surface.Syntax.C_sub_376 v13 v14 v15 v16
           -> coe
                du_cs'45'sub_3080
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                   (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v15) (coe v7) (coe v8)
                   (coe v9))
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                   (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v16) (coe v7) (coe v8)
                   (coe v9))
         MAlonzo.Code.Once.Surface.Syntax.C_mul_386 v13 v14 v15 v16
           -> coe
                du_cs'45'mul_3200
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                   (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v15) (coe v7) (coe v8)
                   (coe v9))
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                   (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v16) (coe v7) (coe v8)
                   (coe v9))
         MAlonzo.Code.Once.Surface.Syntax.C_neg_414 v14
           -> coe
                du_cs'45'neg_3312
                (coe
                   d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v14) (coe v7) (coe v8)
                   (coe v9))
         MAlonzo.Code.Once.Surface.Syntax.C_arr''_486 v16
           -> case coe v5 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v17 v18 v19
                  -> coe
                       du_cs'45'arr_3406
                       (coe
                          d_bridge_3580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe MAlonzo.Code.Once.Type.d__'8658'__150 (coe v17) (coe v19))
                          (coe v16) (coe v7) (coe v8) (coe v9))
                _ -> coe v10
         _ -> coe v10)
-- Once.Verified.ElaborateTrace._.bridge-hole
d_bridge'45'hole_3600
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.ElaborateTrace._.bridge-hole"
-- Once.Verified.ElaborateTrace._.bridge-main
d_bridge'45'main_3874 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bridge'45'main_3874 v0 v1 v2 v3 v4
  = coe
      d_bridge_3580 (coe v0) (coe v1) (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v2) (coe v3)
      (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
