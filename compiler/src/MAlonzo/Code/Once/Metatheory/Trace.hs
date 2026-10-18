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

module MAlonzo.Code.Once.Metatheory.Trace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Delay
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Trace

-- Once.Metatheory.Trace.S
d_S_6 :: () -> ()
d_S_6 = erased
-- Once.Metatheory.Trace._.WB-refl
d_WB'45'refl_22 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_WB'45'refl_22 ~v0 ~v1 v2 ~v3 = du_WB'45'refl_22 v2
du_WB'45'refl_22 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_WB'45'refl_22 v0
  = coe
      MAlonzo.Code.Once.Spec.Trace.C_constructor_108
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe du_reflStep_32 (coe v0) (coe v1)))))
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe du_reflStep_32 (coe v0) (coe v1))))))
-- Once.Metatheory.Trace._.reflStep
d_reflStep_32 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_reflStep_32 ~v0 ~v1 v2 v3 = du_reflStep_32 v2 v3
du_reflStep_32 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_reflStep_32 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Trace.C_returned_12 v3
               -> coe MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42 (coe v0 v3)
             MAlonzo.Code.Once.Spec.Trace.C_halted_14
               -> coe MAlonzo.Code.Once.Spec.Trace.C_halted'8776'_44
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe du_WB'45'refl_22 (coe v0))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._.flipEnd
d_flipEnd_66 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
d_flipEnd_66 ~v0 ~v1 v2 v3 v4 v5 = du_flipEnd_66 v2 v3 v4 v5
du_flipEnd_66 ::
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
du_flipEnd_66 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Trace.C_returned_12 v7
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Trace.C_returned_12 v8
                      -> coe
                           MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42 (coe v2 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Trace.C_halted'8776'_44 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._.WB-sym
d_WB'45'sym_82 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_WB'45'sym_82 ~v0 ~v1 v2 ~v3 ~v4 v5 = du_WB'45'sym_82 v2 v5
du_WB'45'sym_82 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_WB'45'sym_82 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Trace.C_constructor_108
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v2 v3 ->
               coe
                 du_turn_118 (coe v0) (coe v2)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v1)) v2 v3)))
         (coe
            (\ v2 v3 ->
               coe
                 du_turn'8242'_134 (coe v0) (coe v2)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v1)) v2 v3))))
-- Once.Metatheory.Trace._.symStep
d_symStep_100 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> AgdaAny
d_symStep_100 ~v0 ~v1 v2 v3 v4 v5 = du_symStep_100 v2 v3 v4 v5
du_symStep_100 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> AgdaAny
du_symStep_100 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe du_flipEnd_66 (coe v4) (coe v5) (coe v0) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                         (coe du_WB'45'sym_82 (coe v0) (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.turn
d_turn_118 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_turn_118 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 = du_turn_118 v2 v7 v8
du_turn_118 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_turn_118 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                       (coe du_symStep_100 (coe v0) (coe v3) (coe v1) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.turn′
d_turn'8242'_134 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_turn'8242'_134 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_turn'8242'_134 v2 v7 v8
du_turn'8242'_134 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_turn'8242'_134 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                       (coe du_symStep_100 (coe v0) (coe v1) (coe v3) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.endT
d_endT_194 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
d_endT_194 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_endT_194 v2 v3 v4 v5 v6 v7
du_endT_194 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
du_endT_194 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Trace.C_returned_12 v9
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Trace.C_returned_12 v10
                      -> case coe v5 of
                           MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Spec.Trace.C_returned_12 v14
                                    -> coe
                                         MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42
                                         (coe v0 v9 v10 v14 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Trace.C_halted'8776'_44
        -> coe seq (coe v5) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.Comp
d_Comp_200 a0 a1 a2 a3 a4 a5 = ()
data T_Comp_200
  = C_ends_208 MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
               MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 |
    C_calls_218 MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
                MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
-- Once.Metatheory.Trace._._.comp
d_comp_234 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> AgdaAny -> T_Comp_200
d_comp_234 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 = du_comp_234 v3 v4 v5 v6 v7
du_comp_234 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> AgdaAny -> T_Comp_200
du_comp_234 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> coe seq (coe v1) (coe seq (coe v2) (coe C_ends_208 v3 v4))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> coe C_calls_218 v7 v9
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.WB-trans
d_WB'45'trans_258 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_WB'45'trans_258 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7
  = du_WB'45'trans_258 v2 v6 v7
du_WB'45'trans_258 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_WB'45'trans_258 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Trace.C_constructor_108
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe du_fw_290 (coe v0) (coe v1) (coe v2))
         (coe du_bw_334 (coe v0) (coe v1) (coe v2)))
-- Once.Metatheory.Trace._._.transStep
d_transStep_270 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Comp_200 -> AgdaAny
d_transStep_270 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_transStep_270 v2 v3 v4 v5 v6
du_transStep_270 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Comp_200 -> AgdaAny
du_transStep_270 v0 v1 v2 v3 v4
  = case coe v4 of
      C_ends_208 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_endT_194 (coe v0) (coe v10) (coe v11) (coe v12) (coe v8)
                                  (coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_calls_218 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
               -> case coe v11 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v2 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                             -> case coe v14 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> case coe v3 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                                           -> case coe v17 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased
                                                       (coe
                                                          du_WB'45'trans_258 (coe v0) (coe v9)
                                                          (coe v10))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._.fw
d_fw_290 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fw_290 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_fw_290 v2 v6 v7 v8 v9
du_fw_290 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fw_290 v0 v1 v2 v3 v4
  = coe
      du_two_304 (coe v0) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v1)) v3 v4)
-- Once.Metatheory.Trace._._._._.two
d_two_304 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_two_304 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 ~v9 v10
  = du_two_304 v2 v7 v8 v10
du_two_304 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_two_304 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    du_three_320 (coe v0) (coe v2) (coe v4) (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v1)) v4 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._._._.three
d_three_320 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_three_320 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 v10 ~v11 ~v12 v13
            v14
  = du_three_320 v2 v8 v10 v13 v14
du_three_320 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_three_320 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                       (coe
                          du_transStep_270 (coe v0) (coe v1) (coe v2) (coe v5)
                          (coe du_comp_234 (coe v1) (coe v2) (coe v5) (coe v3) (coe v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._.bw
d_bw_334 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bw_334 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_bw_334 v2 v6 v7 v8 v9
du_bw_334 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bw_334 v0 v1 v2 v3 v4
  = coe
      du_two_348 (coe v0) (coe v1) (coe v3)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v2)) v3 v4)
-- Once.Metatheory.Trace._._._._.two
d_two_348 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_two_348 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 v10
  = du_two_348 v2 v6 v8 v10
du_two_348 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_two_348 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    du_three_364 (coe v0) (coe v2) (coe v4) (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v1)) v4 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._._._.three
d_three_364 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_three_364 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 v10 ~v11 ~v12 v13
            v14
  = du_three_364 v2 v8 v10 v13 v14
du_three_364 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_three_364 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                       (coe
                          du_transStep_270 (coe v0) (coe v5) (coe v2) (coe v1)
                          (coe du_comp_234 (coe v5) (coe v2) (coe v1) (coe v8) (coe v3))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._.WB-mono
d_WB'45'mono_402 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_WB'45'mono_402 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_WB'45'mono_402 v3 v6
du_WB'45'mono_402 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_WB'45'mono_402 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Trace.C_constructor_108
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v2 v3 ->
               coe
                 du_go_432 (coe v0) (coe v2)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v1)) v2 v3)))
         (coe
            (\ v2 v3 ->
               coe
                 du_go'8242'_448 (coe v0) (coe v2)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v1)) v2 v3))))
-- Once.Metatheory.Trace._.monoStep
d_monoStep_416 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> AgdaAny
d_monoStep_416 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_monoStep_416 v3 v4 v5 v6
du_monoStep_416 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> AgdaAny
du_monoStep_416 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42 v8
                      -> case coe v4 of
                           MAlonzo.Code.Once.Spec.Trace.C_returned_12 v9
                             -> case coe v5 of
                                  MAlonzo.Code.Once.Spec.Trace.C_returned_12 v10
                                    -> coe
                                         MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42
                                         (coe v0 v9 v10 v8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Trace.C_halted'8776'_44 -> coe v3
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                           (coe du_WB'45'mono_402 (coe v0) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.go
d_go_432 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_432 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 = du_go_432 v3 v8 v9
du_go_432 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_432 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                       (coe du_monoStep_416 (coe v0) (coe v1) (coe v3) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.go′
d_go'8242'_448 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'8242'_448 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_go'8242'_448 v3 v8 v9
du_go'8242'_448 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'8242'_448 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                       (coe du_monoStep_416 (coe v0) (coe v3) (coe v1) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.bindD
d_bindD_474 ::
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8
d_bindD_474 ~v0 ~v1 v2 v3 = du_bindD_474 v2 v3
du_bindD_474 ::
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8
du_bindD_474 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Delay.C_constructor_16
      (coe
         du_bindS_480 (coe MAlonzo.Code.Once.Spec.Delay.d_step_14 (coe v0))
         (coe v1))
-- Once.Metatheory.Trace.bindS
d_bindS_480 ::
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_bindS_480 ~v0 ~v1 v2 v3 = du_bindS_480 v2 v3
du_bindS_480 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_bindS_480 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe MAlonzo.Code.Once.Spec.Delay.d_step_14 (coe v1 v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe du_bindD_474 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.nowInv
d_nowInv_500 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nowInv_500 = erased
-- Once.Metatheory.Trace.inj₁-inj
d_inj'8321''45'inj_510 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'8321''45'inj_510 = erased
-- Once.Metatheory.Trace.inj₂-inj
d_inj'8322''45'inj_518 ::
  () ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'8322''45'inj_518 = erased
-- Once.Metatheory.Trace.clash₁₂
d_clash'8321''8322'_528 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_clash'8321''8322'_528 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_clash'8321''8322'_528
du_clash'8321''8322'_528 :: AgdaAny
du_clash'8321''8322'_528 = MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.⇓-det
d_'8659''45'det_538 ::
  () ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8659''45'det_538 = erased
-- Once.Metatheory.Trace.bind⇓
d_bind'8659'_574 ::
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_bind'8659'_574 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_bind'8659'_574 v3 v6 v7
du_bind'8659'_574 ::
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_bind'8659'_574 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
               -> coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
             MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v4 v6
               -> coe MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v4 v6
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v3 v5
        -> coe
             MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42
             (coe du_bindD_474 (coe v3) (coe v0))
             (coe du_bind'8659'_574 (coe v0) (coe v5) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.bind⇓⁻
d_bind'8659''8315'_616 ::
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bind'8659''8315'_616 ~v0 ~v1 v2 v3 v4 v5
  = du_bind'8659''8315'_616 v2 v3 v4 v5
du_bind'8659''8315'_616 ::
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bind'8659''8315'_616 v0 v1 v2 v3
  = coe du_go'8315'_632 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Metatheory.Trace.go⁻
d_go'8315'_632 ::
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'8315'_632 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 v7
  = du_go'8315'_632 v2 v3 v4 v7
du_go'8315'_632 ::
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'8315'_632 v0 v1 v2 v3
  = coe
      du_at'8315'_650 (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Spec.Delay.d_step_14 (coe v0)) (coe v3)
-- Once.Metatheory.Trace.at⁻
d_at'8315'_650 ::
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at'8315'_650 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 v9
  = du_at'8315'_650 v3 v4 v6 v9
du_at'8315'_650 ::
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at'8315'_650 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38))
             MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v5 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                       (coe MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v5 v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
               -> coe du_clash'8321''8322'_528
             MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v5 v7
               -> coe
                    du_more'8315'_668 (coe v4)
                    (coe du_go'8315'_632 (coe v4) (coe v0) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.more⁻
d_more'8315'_668 ::
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_more'8315'_668 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_more'8315'_668 v3 v7
du_more'8315'_668 ::
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_more'8315'_668 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v0 v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.Obs
d_Obs_744 :: () -> ()
d_Obs_744 = erased
-- Once.Metatheory.Trace.pre
d_pre_750 ::
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8
d_pre_750 ~v0 v1 v2 = du_pre_750 v1 v2
du_pre_750 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8
du_pre_750 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Once.Spec.Delay.du_now_20
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_bindD_474 (coe MAlonzo.Code.Once.Spec.Trace.d_next_24 (coe v1))
                (coe du_preStep_754 (coe v2)))
-- Once.Metatheory.Trace.preStep
d_preStep_754 ::
  () ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8
d_preStep_754 ~v0 v1 v2 = du_preStep_754 v1 v2
du_preStep_754 ::
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8
du_preStep_754 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe
             MAlonzo.Code.Once.Spec.Delay.du_now_20
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_bindD_474 (coe du_pre_750 (coe v0) (coe v4))
                    (coe
                       (\ v5 ->
                          coe
                            MAlonzo.Code.Once.Spec.Delay.du_now_20
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
                               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.MaybeEnd
d_MaybeEnd_778 a0 a1 a2 a3 = ()
data T_MaybeEnd_778
  = C_cut'8776'_784 |
    C_end'8776'_790 MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
-- Once.Metatheory.Trace.ObsR
d_ObsR_794 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_ObsR_794 = erased
-- Once.Metatheory.Trace.Depth
d_Depth_804 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 -> ()
d_Depth_804 = erased
-- Once.Metatheory.Trace.FirstIs
d_FirstIs_816 ::
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_FirstIs_816 = erased
-- Once.Metatheory.Trace.∷-inj
d_'8759''45'inj_834 ::
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8759''45'inj_834 ~v0 ~v1 ~v2 ~v3 ~v4 = du_'8759''45'inj_834
du_'8759''45'inj_834 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8759''45'inj_834
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Metatheory.Trace.[]≢∷
d_'91''93''8802''8759'_842 ::
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'91''93''8802''8759'_842 ~v0 ~v1 ~v2 ~v3
  = du_'91''93''8802''8759'_842
du_'91''93''8802''8759'_842 :: AgdaAny
du_'91''93''8802''8759'_842 = MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.firstOf
d_firstOf_852 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_firstOf_852 ~v0 v1 v2 v3 = du_firstOf_852 v1 v2 v3
du_firstOf_852 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_firstOf_852 v0 v1 v2
  = coe
      du_go_904
      (coe
         du_bind'8659''8315'_616
         (coe MAlonzo.Code.Once.Spec.Trace.d_next_24 (coe v0))
         (coe du_preStep_754 (coe (0 :: Integer))) (coe v1) (coe v2))
-- Once.Metatheory.Trace._.lift₀
d_lift'8320'_870 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'8320'_870 = erased
-- Once.Metatheory.Trace._.at
d_at_886 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 -> AgdaAny
d_at_886 = erased
-- Once.Metatheory.Trace._.go
d_go_904 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_904 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_go_904 v5
du_go_904 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_904 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.seeFirst
d_seeFirst_920 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_seeFirst_920 ~v0 ~v1 v2 v3 = du_seeFirst_920 v2 v3
du_seeFirst_920 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_seeFirst_920 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   du_bind'8659'_574 (coe du_preStep_754 (coe (0 :: Integer)))
                   (coe v1) (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38))
                erased)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          du_bind'8659'_574 (coe du_preStep_754 (coe (0 :: Integer)))
                          (coe v1)
                          (coe
                             du_bind'8659'_574
                             (coe
                                (\ v5 ->
                                   coe
                                     MAlonzo.Code.Once.Spec.Delay.du_now_20
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
                                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))))
                             (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                             (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)))
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.deeper
d_deeper_944 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_deeper_944 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7
  = du_deeper_944 v2 v4 v6 v7
du_deeper_944 ::
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_deeper_944 v0 v1 v2 v3
  = coe
      du_bind'8659'_574 (coe du_preStep_754 (coe v1)) (coe v2)
      (coe
         du_bind'8659'_574
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.Once.Spec.Delay.du_now_20
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))))
         (coe v3) (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38))
-- Once.Metatheory.Trace.shallower
d_shallower_964 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shallower_964 ~v0 v1 v2 v3 v4 v5 ~v6 v7
  = du_shallower_964 v1 v2 v3 v4 v5 v7
du_shallower_964 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shallower_964 v0 v1 v2 v3 v4 v5
  = coe
      du_go_1014 (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         du_bind'8659''8315'_616
         (coe MAlonzo.Code.Once.Spec.Trace.d_next_24 (coe v0))
         (coe du_preStep_754 (coe v3)) (coe v4) (coe v5))
-- Once.Metatheory.Trace._.inner
d_inner_990 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inner_990 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inner_990 v9
du_inner_990 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inner_990 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._.sameS
d_sameS_1004 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sameS_1004 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 v11
  = du_sameS_1004 v2 v3 v4 v9 v11
du_sameS_1004 ::
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sameS_1004 v0 v1 v2 v3 v4
  = coe
      du_inner_990
      (coe
         du_bind'8659''8315'_616 (coe du_pre_750 (coe v2) (coe v1))
         (coe
            (\ v5 ->
               coe
                 MAlonzo.Code.Once.Spec.Delay.du_now_20
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))))
         (coe v3) (coe v4))
-- Once.Metatheory.Trace._.go
d_go_1014 ::
  () ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1014 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 v9
  = du_go_1014 v2 v3 v4 v8 v9
du_go_1014 ::
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1014 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe du_sameS_1004 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._.restDepth
d_restDepth_1040 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_restDepth_1040 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_restDepth_1040 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_restDepth_1040 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_restDepth_1040 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_fw_1068 (coe v1) (coe v2) (coe v4) (coe v5) (coe v6) (coe v8))
      (coe
         du_bw_1110 (coe v0) (coe v2) (coe v3) (coe v5) (coe v7) (coe v8))
-- Once.Metatheory.Trace._._.fw
d_fw_1068 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fw_1068 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 v8 ~v9 v10 v11 v12
  = du_fw_1068 v3 v4 v6 v7 v8 v10 v11 v12
du_fw_1068 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fw_1068 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_step'8321'_1098 (coe v0) (coe v1) (coe v2) (coe v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe v3 (addInt (coe (1 :: Integer)) (coe v5)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
         (coe du_deeper_944 (coe v1) (coe v5) (coe v4) (coe v7)))
-- Once.Metatheory.Trace._._._.fin
d_fin_1084 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fin_1084 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 v14 v15
  = du_fin_1084 v14 v15
du_fin_1084 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fin_1084 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe du_'8759''45'inj_834))
                                 (coe v3)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._.step₁
d_step'8321'_1098 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step'8321'_1098 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 v10 ~v11
                  ~v12 v13
  = du_step'8321'_1098 v3 v4 v6 v10 v13
du_step'8321'_1098 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step'8321'_1098 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    du_fin_1084 (coe v8)
                    (coe
                       du_shallower_964 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.bw
d_bw_1110 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bw_1110 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 v10 v11 v12
  = du_bw_1110 v2 v4 v5 v7 v9 v10 v11 v12
du_bw_1110 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bw_1110 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_step'8321'_1140 (coe v0) (coe v1) (coe v2) (coe v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe v3 (addInt (coe (1 :: Integer)) (coe v5)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
         (coe du_deeper_944 (coe v1) (coe v5) (coe v4) (coe v7)))
-- Once.Metatheory.Trace._._._.fin
d_fin_1126 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fin_1126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 v14 v15
  = du_fin_1126 v14 v15
du_fin_1126 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fin_1126 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe du_'8759''45'inj_834))
                                 (coe v3)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._.step₁
d_step'8321'_1140 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step'8321'_1140 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                  ~v12 v13
  = du_step'8321'_1140 v2 v4 v5 v10 v13
du_step'8321'_1140 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step'8321'_1140 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    du_fin_1126 (coe v8)
                    (coe
                       du_shallower_964 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._.endMatch
d_endMatch_1156 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_endMatch_1156 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_endMatch_1156 v3 v4 v5 v6
du_endMatch_1156 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_endMatch_1156 v0 v1 v2 v3
  = coe
      du_one_1224 (coe v0) (coe v1) (coe v2)
      (coe
         du_seeFirst_920
         (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1)) (coe v3))
-- Once.Metatheory.Trace._._.decide
d_decide_1178 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decide_1178 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11
  = du_decide_1178 v8 v9 v11
du_decide_1178 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_decide_1178 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    C_end'8776'_790 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             seq (coe v3) (coe seq (coe v2) (coe du_'91''93''8802''8759'_842))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.two
d_two_1196 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_two_1196 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 = du_two_1196 v3 v7
du_two_1196 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_two_1196 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_three_1212 (coe v5)
                    (coe du_firstOf_852 (coe v0) (coe v2) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._.three
d_three_1212 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_three_1212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_three_1212 v9 v10
du_three_1212 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_three_1212 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe du_decide_1178 (coe v2) (coe v4) (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.one
d_one_1224 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_one_1224 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 = du_one_1224 v3 v4 v5 v7
du_one_1224 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_one_1224 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    du_two_1196 (coe v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2 (1 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)))
                       v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._.emitMatch
d_emitMatch_1240 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_emitMatch_1240 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_emitMatch_1240 v2 v3 v4 v5 v6 v7
du_emitMatch_1240 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_emitMatch_1240 v0 v1 v2 v3 v4 v5
  = coe
      du_one_1322 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         du_seeFirst_920
         (coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)))
         (coe v5))
-- Once.Metatheory.Trace._._.decide
d_decide_1264 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decide_1264 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 ~v8 v9 v10 ~v11 v12
  = du_decide_1264 v2 v3 v5 v6 v7 v9 v10 v12
du_decide_1264 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_decide_1264 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
        -> coe seq (coe v7) (coe du_'91''93''8802''8759'_842)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    seq (coe v7)
                    (coe
                       du_fin_1286 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9)
                       (coe v10) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._.fin
d_fin_1286 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_MaybeEnd_778 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fin_1286 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13 v14
  = du_fin_1286 v2 v3 v5 v6 v7 v8 v9 v14
du_fin_1286 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fin_1286 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
         (coe
            du_restDepth_1040 (coe v0) (coe v1) (coe v5) (coe v2) (coe v6)
            (coe v3) (coe v4) (coe v7)))
-- Once.Metatheory.Trace._._.two
d_two_1294 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_two_1294 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_two_1294 v2 v3 v5 v6 v7 v8
du_two_1294 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_two_1294 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    du_three_1310 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9)
                    (coe du_firstOf_852 (coe v1) (coe v6) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._.three
d_three_1310 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_three_1310 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 v10 v11
  = du_three_1310 v2 v3 v5 v6 v7 v10 v11
du_three_1310 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_three_1310 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    du_decide_1264 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v7) (coe v9) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.one
d_one_1322 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_one_1322 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_one_1322 v2 v3 v4 v5 v6 v7 v8
du_one_1322 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_one_1322 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    du_two_1294 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4 (1 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                       v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.EndRel-flip
d_EndRel'45'flip_1336 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
d_EndRel'45'flip_1336 ~v0 ~v1 ~v2 ~v3 v4
  = du_EndRel'45'flip_1336 v4
du_EndRel'45'flip_1336 ::
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
du_EndRel'45'flip_1336 v0 = coe v0
-- Once.Metatheory.Trace.EndRel-unflip
d_EndRel'45'unflip_1348 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
d_EndRel'45'unflip_1348 ~v0 ~v1 ~v2 ~v3 v4
  = du_EndRel'45'unflip_1348 v4
du_EndRel'45'unflip_1348 ::
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
du_EndRel'45'unflip_1348 v0 = coe v0
-- Once.Metatheory.Trace.MaybeEnd-flip
d_MaybeEnd'45'flip_1360 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  T_MaybeEnd_778 -> T_MaybeEnd_778
d_MaybeEnd'45'flip_1360 ~v0 ~v1 ~v2 ~v3 v4
  = du_MaybeEnd'45'flip_1360 v4
du_MaybeEnd'45'flip_1360 :: T_MaybeEnd_778 -> T_MaybeEnd_778
du_MaybeEnd'45'flip_1360 v0 = coe v0
-- Once.Metatheory.Trace.ObsR-flip
d_ObsR'45'flip_1372 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ObsR'45'flip_1372 ~v0 ~v1 ~v2 ~v3 v4 = du_ObsR'45'flip_1372 v4
du_ObsR'45'flip_1372 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ObsR'45'flip_1372 v0 = coe v0
-- Once.Metatheory.Trace.Depth-sym
d_Depth'45'sym_1386 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Depth'45'sym_1386 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_Depth'45'sym_1386 v4 v5
du_Depth'45'sym_1386 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Depth'45'sym_1386 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v2 v3 ->
            coe
              du_turn'8321'_1408
              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v1) v2 v3)))
      (coe
         (\ v2 v3 ->
            coe
              du_turn'8322'_1422
              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v1) v2 v3)))
-- Once.Metatheory.Trace._.turn₁
d_turn'8321'_1408 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_turn'8321'_1408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_turn'8321'_1408 v7
du_turn'8321'_1408 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_turn'8321'_1408 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe seq (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._.turn₂
d_turn'8322'_1422 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_turn'8322'_1422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_turn'8322'_1422 v7
du_turn'8322'_1422 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_turn'8322'_1422 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe seq (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.fromDepth
d_fromDepth_1446 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_fromDepth_1446 ~v0 ~v1 v2 v3 v4 = du_fromDepth_1446 v2 v3 v4
du_fromDepth_1446 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_fromDepth_1446 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Trace.C_constructor_108
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe du_fwdD_1464 (coe v0) (coe v1) (coe v2))
         (coe du_bwdD_1482 (coe v0) (coe v1) (coe v2)))
-- Once.Metatheory.Trace.fwdD
d_fwdD_1464 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fwdD_1464 ~v0 ~v1 v2 v3 v4 v5 v6 = du_fwdD_1464 v2 v3 v4 v5 v6
du_fwdD_1464 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fwdD_1464 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_endMatch_1156 (coe v1) (coe v5) (coe v2) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe du_endMatch_1156 (coe v1) (coe v5) (coe v2) (coe v4)))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                du_emitMatch_1240 (coe v0) (coe v1) (coe v6) (coe v7) (coe v2)
                                (coe v4)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_emitMatch_1240 (coe v0) (coe v1) (coe v6) (coe v7) (coe v2)
                                (coe v4))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe
                             du_fromDepth_1446 (coe v7)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   du_emitMatch_1240 (coe v0) (coe v1) (coe v6) (coe v7) (coe v2)
                                   (coe v4)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      du_emitMatch_1240 (coe v0) (coe v1) (coe v6) (coe v7) (coe v2)
                                      (coe v4)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.bwdD
d_bwdD_1482 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bwdD_1482 ~v0 ~v1 v2 v3 v4 v5 v6 = du_bwdD_1482 v2 v3 v4 v5 v6
du_bwdD_1482 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bwdD_1482 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_endMatch_1156 (coe v0) (coe v5)
                      (coe du_Depth'45'sym_1386 (coe v2)) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_endMatch_1156 (coe v0) (coe v5)
                         (coe du_Depth'45'sym_1386 (coe v2)) (coe v4))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_endMatch_1156 (coe v0) (coe v5)
                         (coe du_Depth'45'sym_1386 (coe v2)) (coe v4)))))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                du_emitMatch_1240 (coe v1) (coe v0) (coe v6) (coe v7)
                                (coe du_Depth'45'sym_1386 (coe v2)) (coe v4)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_emitMatch_1240 (coe v1) (coe v0) (coe v6) (coe v7)
                                (coe du_Depth'45'sym_1386 (coe v2)) (coe v4))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe
                             du_fromDepth_1446
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   du_emitMatch_1240 (coe v1) (coe v0) (coe v6) (coe v7)
                                   (coe du_Depth'45'sym_1386 (coe v2)) (coe v4)))
                             (coe v7)
                             (coe
                                du_Depth'45'sym_1386
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         du_emitMatch_1240 (coe v1) (coe v0) (coe v6) (coe v7)
                                         (coe du_Depth'45'sym_1386 (coe v2)) (coe v4))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace.toDepth
d_toDepth_1530 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_toDepth_1530 ~v0 ~v1 v2 v3 v4 v5 = du_toDepth_1530 v2 v3 v4 v5
du_toDepth_1530 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_toDepth_1530 v0 v1 v2 v3
  = case coe v3 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe (\ v4 v5 -> coe du_base_1550))
             (coe (\ v4 v5 -> coe du_base'8242'_1556))
      _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe du_fw_1586 (coe v0) (coe v2) (coe v4))
                (coe du_bw_1732 (coe v1) (coe v2) (coe v4)))
-- Once.Metatheory.Trace._.base
d_base_1550 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_base_1550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_base_1550
du_base_1550 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_base_1550
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe C_cut'8776'_784)))
-- Once.Metatheory.Trace._.base′
d_base'8242'_1556 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_base'8242'_1556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_base'8242'_1556
du_base'8242'_1556 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_base'8242'_1556
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe C_cut'8776'_784)))
-- Once.Metatheory.Trace._.fw
d_fw_1586 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fw_1586 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 = du_fw_1586 v2 v4 v5 v6 v7
du_fw_1586 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fw_1586 v0 v1 v2 v3 v4
  = coe
      du_split_1720 (coe v1) (coe v2) (coe v3)
      (coe
         du_bind'8659''8315'_616
         (coe MAlonzo.Code.Once.Spec.Trace.d_next_24 (coe v0))
         (coe du_preStep_754 (coe v2)) (coe v3) (coe v4))
-- Once.Metatheory.Trace._._.endCase
d_endCase_1602 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_endCase_1602 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 v11 v12
  = du_endCase_1602 v5 v9 v11 v12
du_endCase_1602 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_endCase_1602 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            du_bind'8659'_574 (coe du_preStep_754 (coe v0)) (coe v2)
            (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe C_end'8776'_790 v3)))
-- Once.Metatheory.Trace._._.callCase
d_callCase_1618 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_callCase_1618 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9 v10 v11 v12
                v13
  = du_callCase_1618 v5 v8 v9 v10 v11 v12 v13
du_callCase_1618 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_callCase_1618 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    du_fin_1640 (coe v0) (coe v1) (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe du_toDepth_1530 (coe v2) (coe v3) (coe v5) (coe v0)) v7 v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._.fin
d_fin_1640 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fin_1640 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 v11 ~v12 ~v13
           ~v14 ~v15 ~v16 v17
  = du_fin_1640 v5 v8 v11 v17
du_fin_1640 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fin_1640 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe du_deeper_944 (coe v1) (coe v0) (coe v2) (coe v6))
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v9)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.both
d_both_1662 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_both_1662 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 v8 v9 v10 v11 v12
  = du_both_1662 v5 v6 v8 v9 v10 v11 v12
du_both_1662 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_both_1662 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe du_endCase_1602 (coe v0) (coe v8) (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> case coe v10 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                    -> coe
                                         du_callCase_1618 (coe v0) (coe v8) (coe v9) (coe v12)
                                         (coe v5) (coe v14)
                                         (coe
                                            du_bind'8659''8315'_616
                                            (coe du_pre_750 (coe v0) (coe v9))
                                            (coe
                                               (\ v15 ->
                                                  coe
                                                    MAlonzo.Code.Once.Spec.Delay.du_now_20
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe v8)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe v15)))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe v15)))))
                                            (coe v1) (coe v3))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.matched
d_matched_1704 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_matched_1704 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 v8 v9 v10
  = du_matched_1704 v5 v6 v8 v9 v10
du_matched_1704 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_matched_1704 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    du_both_1662 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v7)
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.split
d_split_1720 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_split_1720 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 v8
  = du_split_1720 v4 v5 v6 v8
du_split_1720 ::
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_split_1720 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    du_matched_1704 (coe v1) (coe v2) (coe v4) (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v0)) v4 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._.bw
d_bw_1732 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bw_1732 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 = du_bw_1732 v3 v4 v5 v6 v7
du_bw_1732 ::
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bw_1732 v0 v1 v2 v3 v4
  = coe
      du_split_1866 (coe v1) (coe v2) (coe v3)
      (coe
         du_bind'8659''8315'_616
         (coe MAlonzo.Code.Once.Spec.Trace.d_next_24 (coe v0))
         (coe du_preStep_754 (coe v2)) (coe v3) (coe v4))
-- Once.Metatheory.Trace._._.endCase
d_endCase_1748 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_endCase_1748 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
  = du_endCase_1748 v5 v8 v11 v12
du_endCase_1748 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_endCase_1748 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            du_bind'8659'_574 (coe du_preStep_754 (coe v0)) (coe v2)
            (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe C_end'8776'_790 v3)))
-- Once.Metatheory.Trace._._.callCase
d_callCase_1764 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_callCase_1764 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9 v10 v11 v12
                v13
  = du_callCase_1764 v5 v8 v9 v10 v11 v12 v13
du_callCase_1764 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_callCase_1764 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    du_fin_1786 (coe v0) (coe v1) (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_toDepth_1530 (coe v2) (coe v3) (coe v5) (coe v0)) v7 v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._._.fin
d_fin_1786 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fin_1786 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 v11 ~v12 ~v13
           ~v14 ~v15 ~v16 v17
  = du_fin_1786 v5 v8 v11 v17
du_fin_1786 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fin_1786 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe du_deeper_944 (coe v1) (coe v0) (coe v2) (coe v6))
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v9)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.both
d_both_1808 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_both_1808 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 v8 v9 v10 v11 v12
  = du_both_1808 v5 v6 v8 v9 v10 v11 v12
du_both_1808 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_both_1808 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe du_endCase_1748 (coe v0) (coe v8) (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> case coe v10 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                    -> coe
                                         du_callCase_1764 (coe v0) (coe v8) (coe v12) (coe v9)
                                         (coe v5) (coe v14)
                                         (coe
                                            du_bind'8659''8315'_616
                                            (coe du_pre_750 (coe v0) (coe v9))
                                            (coe
                                               (\ v15 ->
                                                  coe
                                                    MAlonzo.Code.Once.Spec.Delay.du_now_20
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe v8)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe v15)))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe v15)))))
                                            (coe v1) (coe v3))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.matched
d_matched_1850 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_matched_1850 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 v8 v9 v10
  = du_matched_1850 v5 v6 v8 v9 v10
du_matched_1850 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_matched_1850 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    du_both_1808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v7)
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Trace._._.split
d_split_1866 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_split_1866 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 v8
  = du_split_1866 v4 v5 v6 v8
du_split_1866 ::
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_split_1866 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    du_matched_1850 (coe v1) (coe v2) (coe v4) (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (MAlonzo.Code.Once.Spec.Trace.d_same_106 (coe v0)) v4 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
