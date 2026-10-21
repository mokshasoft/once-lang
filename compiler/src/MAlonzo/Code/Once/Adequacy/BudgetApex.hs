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

module MAlonzo.Code.Once.Adequacy.BudgetApex where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Adequacy.FuelTrace
import qualified MAlonzo.Code.Once.Adequacy.MachineTrace
import qualified MAlonzo.Code.Once.Denotation.TraceTr
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Spec.Trace

-- Once.Adequacy.BudgetApex.budget-apex
d_budget'45'apex_22 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_budget'45'apex_22 ~v0 v1 v2 v3 ~v4 v5 v6
  = du_budget'45'apex_22 v1 v2 v3 v5 v6
du_budget'45'apex_22 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_budget'45'apex_22 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.FuelTrace.du_agree'45''8776'_1164
      (coe v0)
      (coe MAlonzo.Code.Once.Denotation.TraceTr.du_δ'8734'_78 (coe v2))
      (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3)))
      (coe du_ag_40 (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.BudgetApex._.ag
d_ag_40 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ag_40 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 = du_ag_40 v3 v5 v6 v7
du_ag_40 ::
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ag_40 v0 v1 v2 v3
  = let v4 = coe v2 (addInt (coe (1 :: Integer)) (coe v3)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Once.Denotation.TraceTr.du_approx'45'runB_268 (coe v0)
                 (coe addInt (coe (1 :: Integer)) (coe v3))
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                 (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1)) in
       coe
         (case coe v4 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
              -> case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              (coe
                                                 (\ v14 ->
                                                    coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'pred_2980
                                                         v6 (coe v9 erased))
                                                      (coe
                                                         du_'8804''45'pred'8242'_70
                                                         (coe v13 erased))))))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.BudgetApex._._.≤-pred′
d_'8804''45'pred'8242'_70 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Trace.T_Interp_182 ->
  () ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'pred'8242'_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_'8804''45'pred'8242'_70 v16
du_'8804''45'pred'8242'_70 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'pred'8242'_70 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
