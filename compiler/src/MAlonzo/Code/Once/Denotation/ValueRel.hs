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

module MAlonzo.Code.Once.Denotation.ValueRel where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Internal.FunctorMeaning
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.StreamInf
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value

-- Once.Denotation.ValueRel._.⟦_⟧F
d_'10214'_'10215'F_8 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_8 = erased
-- Once.Denotation.ValueRel.StreamRel
d_StreamRel_16 a0 a1 a2 = ()
data T_StreamRel_16
  = C_constructor_34 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
-- Once.Denotation.ValueRel.LayerRel
d_LayerRel_22 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> ()
d_LayerRel_22 = erased
-- Once.Denotation.ValueRel.StreamRel.forceR
d_forceR_32 ::
  T_StreamRel_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_forceR_32 v0
  = case coe v0 of
      C_constructor_34 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.RelD
d_RelD_98 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> ()
d_RelD_98 = erased
-- Once.Denotation.ValueRel.RelD-subst
d_RelD'45'subst_204 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_RelD'45'subst_204 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_RelD'45'subst_204 v5
du_RelD'45'subst_204 :: AgdaAny -> AgdaAny
du_RelD'45'subst_204 v0 = coe v0
-- Once.Denotation.ValueRel.FRel
d_FRel_216 a0 a1 a2 a3 a4 a5 = ()
data T_FRel_216
  = C_fr'45'K_228 | C_fr'45'Id_234 AgdaAny |
    C_fr'45'inl_244 T_FRel_216 | C_fr'45'inr_254 T_FRel_216 |
    C_fr'45'pair_268 T_FRel_216 T_FRel_216
-- Once.Denotation.ValueRel.SRel
d_SRel_278 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> ()
d_SRel_278 = erased
-- Once.Denotation.ValueRel.base-eq
d_base'45'eq_346 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'eq_346 = erased
-- Once.Denotation.ValueRel.base-refl
d_base'45'refl_420 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_base'45'refl_420 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Int_14
        -> erased
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Float_16
        -> erased
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_base'45'refl_420 (coe v7) (coe v5) (coe v9))
                           (coe d_base'45'refl_420 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe d_base'45'refl_420 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe d_base'45'refl_420 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.RelS-mono
d_RelS'45'mono_464 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'mono_464 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelS'45'mono_464 v4 v5 v6 v7
du_RelS'45'mono_464 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'mono_464 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'mono_482 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v3)))
-- Once.Denotation.ValueRel.RelSB-mono
d_RelSB'45'mono_482 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'mono_482 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelSB'45'mono_482 v4 v5 v6 v7
du_RelSB'45'mono_482 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'mono_482 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                         (coe v0 v8 v10 v6)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_RelS'45'mono_464 (coe v0) (coe v8) (coe v10)
                                            (coe v6))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v9 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v15 ->
                              coe
                                du_RelSB'45'mono_482 (coe v0) (coe v11 v15) (coe v14 v15)
                                (coe v8 v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.RelS-fmap
d_RelS'45'fmap_528 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'fmap_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_RelS'45'fmap_528 v6 v7 v8 v9 v10 v11
du_RelS'45'fmap_528 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'fmap_528 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe v0) (coe v1)
      (coe
         (\ v6 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe v2 v6)))
      (coe
         (\ v6 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe v3 v6)))
      (coe v4)
      (coe
         (\ v6 v7 v8 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
              (coe v5 v6 v7 v8)))
-- Once.Denotation.ValueRel.RelS-fmapˡ
d_RelS'45'fmap'737'_556 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'fmap'737'_556 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_RelS'45'fmap'737'_556 v5 v6 v7 v8 v9
du_RelS'45'fmap'737'_556 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'fmap'737'_556 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'fmap'737'_580 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v3))
         (coe v4))
-- Once.Denotation.ValueRel.RelSB-fmapˡ
d_RelSB'45'fmap'737'_580 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'fmap'737'_580 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_RelSB'45'fmap'737'_580 v5 v6 v7 v8 v9
du_RelSB'45'fmap'737'_580 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'fmap'737'_580 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                         (coe v4 v9 v11 v7)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_RelS'45'fmap'737'_556 (coe v0) (coe v9) (coe v11)
                                            (coe v7) (coe v4))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v10 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v16 ->
                              coe
                                du_RelSB'45'fmap'737'_580 (coe v0) (coe v12 v16) (coe v15 v16)
                                (coe v9 v16) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.RelS-fmapʳ
d_RelS'45'fmap'691'_622 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'fmap'691'_622 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_RelS'45'fmap'691'_622 v5 v6 v7 v8 v9
du_RelS'45'fmap'691'_622 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'fmap'691'_622 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'fmap'691'_646 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v3))
         (coe v4))
-- Once.Denotation.ValueRel.RelSB-fmapʳ
d_RelSB'45'fmap'691'_646 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'fmap'691'_646 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_RelSB'45'fmap'691'_646 v5 v6 v7 v8 v9
du_RelSB'45'fmap'691'_646 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'fmap'691'_646 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                         (coe v4 v9 v11 v7)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_RelS'45'fmap'691'_622 (coe v0) (coe v9) (coe v11)
                                            (coe v7) (coe v4))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v10 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v16 ->
                              coe
                                du_RelSB'45'fmap'691'_646 (coe v0) (coe v12 v16) (coe v15 v16)
                                (coe v9 v16) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.RelS-assocˡ
d_RelS'45'assoc'737'_696 ::
  () ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'assoc'737'_696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
                         v11 v12 v13
  = du_RelS'45'assoc'737'_696 v7 v8 v9 v10 v11 v12 v13
du_RelS'45'assoc'737'_696 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'assoc'737'_696 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'assoc'737'_726
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe v2) (coe v3) (coe v4)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v5))
         (coe v6))
-- Once.Denotation.ValueRel.RelSB-assocˡ
d_RelSB'45'assoc'737'_726 ::
  () ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'assoc'737'_726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
                          v11 v12 v13
  = du_RelSB'45'assoc'737'_726 v7 v8 v9 v10 v11 v12 v13
du_RelSB'45'assoc'737'_726 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'assoc'737'_726 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
                                         (coe v6 v11 v13 v9)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_RelS'45'assoc'737'_696 (coe v11) (coe v13) (coe v2)
                                            (coe v3) (coe v4) (coe v9) (coe v6))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v15 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v18 ->
                              coe
                                du_RelSB'45'assoc'737'_726 (coe v14 v18) (coe v17 v18) (coe v2)
                                (coe v3) (coe v4) (coe v11 v18) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.RelS-assocʳ
d_RelS'45'assoc'691'_776 ::
  () ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'assoc'691'_776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
                         v11 v12 v13
  = du_RelS'45'assoc'691'_776 v7 v8 v9 v10 v11 v12 v13
du_RelS'45'assoc'691'_776 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'assoc'691'_776 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'assoc'691'_806
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe v2) (coe v3) (coe v4)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v5))
         (coe v6))
-- Once.Denotation.ValueRel.RelSB-assocʳ
d_RelSB'45'assoc'691'_806 ::
  () ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'assoc'691'_806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
                          v11 v12 v13
  = du_RelSB'45'assoc'691'_806 v7 v8 v9 v10 v11 v12 v13
du_RelSB'45'assoc'691'_806 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'assoc'691'_806 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
                                         (coe v6 v11 v13 v9)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_RelS'45'assoc'691'_776 (coe v11) (coe v13) (coe v2)
                                            (coe v3) (coe v4) (coe v9) (coe v6))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v15 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v18 ->
                              coe
                                du_RelSB'45'assoc'691'_806 (coe v14 v18) (coe v17 v18) (coe v2)
                                (coe v3) (coe v4) (coe v11 v18) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.RelS-assoc₂
d_RelS'45'assoc'8322'_860 ::
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'assoc'8322'_860 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
                          v11 v12 v13 v14 v15
  = du_RelS'45'assoc'8322'_860 v8 v9 v10 v11 v12 v13 v14 v15
du_RelS'45'assoc'8322'_860 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'assoc'8322'_860 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'assoc'8322'_894
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe v2) (coe v3) (coe v4) (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v6))
         (coe v7))
-- Once.Denotation.ValueRel.RelSB-assoc₂
d_RelSB'45'assoc'8322'_894 ::
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'assoc'8322'_894 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                           v10 v11 v12 v13 v14 v15
  = du_RelSB'45'assoc'8322'_894 v8 v9 v10 v11 v12 v13 v14 v15
du_RelSB'45'assoc'8322'_894 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'assoc'8322'_894 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
               -> case coe v11 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v13
                             -> case coe v13 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
                                         (coe v7 v12 v14 v10)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
               -> case coe v11 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v13
                             -> case coe v13 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_RelS'45'assoc'8322'_860 (coe v12) (coe v14) (coe v2)
                                            (coe v3) (coe v4) (coe v5) (coe v10) (coe v7))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v16 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v19 ->
                              coe
                                du_RelSB'45'assoc'8322'_894 (coe v15 v19) (coe v18 v19) (coe v2)
                                (coe v3) (coe v4) (coe v5) (coe v12 v19) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.RelS-unfmapʳ
d_RelS'45'unfmap'691'_934 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'unfmap'691'_934 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelS'45'unfmap'691'_934 v4 v5 v6 v7
du_RelS'45'unfmap'691'_934 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'unfmap'691'_934 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'unfmap'691'_956 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v3)))
-- Once.Denotation.ValueRel.RelSB-unfmapʳ
d_RelSB'45'unfmap'691'_956 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'unfmap'691'_956 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelSB'45'unfmap'691'_956 v4 v5 v6 v7
du_RelSB'45'unfmap'691'_956 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'unfmap'691'_956 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> case coe v3 of
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v8
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> case coe v3 of
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_RelS'45'unfmap'691'_934 (coe v0) (coe v10) (coe v5)
                                            (coe v8))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v4 v5 v6
        -> case coe v3 of
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v15 ->
                              coe
                                du_RelSB'45'unfmap'691'_956 (coe v0) (coe v14 v15) (coe v6 v15)
                                (coe v11 v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v4 v5
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.retargetˡ
d_retarget'737'_996 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_retarget'737'_996 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_retarget'737'_996 v7
du_retarget'737'_996 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_retarget'737'_996 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
         (coe v0))
-- Once.Denotation.ValueRel.retargetʳ
d_retarget'691'_1016 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_retarget'691'_1016 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_retarget'691'_1016 v7
du_retarget'691'_1016 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_retarget'691'_1016 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
         (coe v0))
-- Once.Denotation.ValueRel.RelS-substˡ
d_RelS'45'subst'737'_1042 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'subst'737'_1042 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_RelS'45'subst'737'_1042 v7
du_RelS'45'subst'737'_1042 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'subst'737'_1042 v0 = coe v0
-- Once.Denotation.ValueRel.seqF∞-rel
d_seqF'8734''45'rel_1058 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  T_FRel_216 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_seqF'8734''45'rel_1058 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_seqF'8734''45'rel_1058 v3 v4 v5 v6
du_seqF'8734''45'rel_1058 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  T_FRel_216 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_seqF'8734''45'rel_1058 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v4
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                (coe C_fr'45'K_228))
      MAlonzo.Code.Once.Internal.Type.C_Id_14
        -> case coe v3 of
             C_fr'45'Id_234 v6
               -> coe
                    du_RelS'45'mono_464 (\ v7 v8 v9 -> coe C_fr'45'Id_234 v9)
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
                       (coe v1))
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
                       (coe v2))
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v4 v5
        -> case coe v3 of
             C_fr'45'inl_244 v10
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v2 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_RelS'45'fmap_528
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                                     (coe v11))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                                     (coe v12))
                                  (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                                  (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                                  (coe
                                     du_seqF'8734''45'rel_1058 (coe v4) (coe v11) (coe v12)
                                     (coe v10))
                                  (\ v13 v14 v15 -> coe C_fr'45'inl_244 v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_fr'45'inr_254 v10
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v2 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_RelS'45'fmap_528
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v5)
                                     (coe v11))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v5)
                                     (coe v12))
                                  (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                                  (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                                  (coe
                                     du_seqF'8734''45'rel_1058 (coe v5) (coe v11) (coe v12)
                                     (coe v10))
                                  (\ v13 v14 v15 -> coe C_fr'45'inr_254 v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v4 v5
        -> case coe v3 of
             C_fr'45'pair_268 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                                     (coe v14))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                                     (coe v16))
                                  (coe
                                     (\ v18 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v5) (coe v15))
                                          (coe
                                             (\ v19 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v18) (coe v19))))))
                                  (coe
                                     (\ v18 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v5) (coe v17))
                                          (coe
                                             (\ v19 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v18) (coe v19))))))
                                  (coe
                                     du_seqF'8734''45'rel_1058 (coe v4) (coe v14) (coe v16)
                                     (coe v12))
                                  (coe
                                     (\ v18 v19 v20 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v5) (coe v15))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v5) (coe v17))
                                          (coe
                                             (\ v21 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v18) (coe v21))))
                                          (coe
                                             (\ v21 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v19) (coe v21))))
                                          (coe
                                             du_seqF'8734''45'rel_1058 (coe v5) (coe v15) (coe v17)
                                             (coe v13))
                                          (coe
                                             (\ v21 v22 v23 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                  (coe C_fr'45'pair_268 v20 v23)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.fr-K≡
d_fr'45'K'8801'_1100 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FRel_216
d_fr'45'K'8801'_1100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_fr'45'K'8801'_1100
du_fr'45'K'8801'_1100 :: T_FRel_216
du_fr'45'K'8801'_1100 = coe C_fr'45'K_228
-- Once.Denotation.ValueRel.cfD-rel
d_cfD'45'rel_1112 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_FRel_216
d_cfD'45'rel_1112 v0 v1 ~v2 v3 v4 v5
  = du_cfD'45'rel_1112 v0 v1 v3 v4 v5
du_cfD'45'rel_1112 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_FRel_216
du_cfD'45'rel_1112 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v6
        -> coe du_fr'45'K'8801'_1100
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54
        -> coe C_fr'45'Id_234 v4
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  C_fr'45'inl_244
                                  (coe
                                     du_cfD'45'rel_1112 (coe v9) (coe v7) (coe v11) (coe v12)
                                     (coe v4))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  C_fr'45'inr_254
                                  (coe
                                     du_cfD'45'rel_1112 (coe v10) (coe v8) (coe v11) (coe v12)
                                     (coe v4))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         C_fr'45'pair_268
                                         (coe
                                            du_cfD'45'rel_1112 (coe v9) (coe v7) (coe v11) (coe v13)
                                            (coe v15))
                                         (coe
                                            du_cfD'45'rel_1112 (coe v10) (coe v8) (coe v12)
                                            (coe v14) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.cfD⁻¹-rel
d_cfD'8315''185''45'rel_1188 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> T_FRel_216 -> AgdaAny
d_cfD'8315''185''45'rel_1188 v0 v1 ~v2 v3 v4 v5
  = du_cfD'8315''185''45'rel_1188 v0 v1 v3 v4 v5
du_cfD'8315''185''45'rel_1188 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> T_FRel_216 -> AgdaAny
du_cfD'8315''185''45'rel_1188 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C_K_12 v7
               -> coe
                    seq (coe v4)
                    (coe
                       d_base'45'refl_420 (coe v7) (coe v6)
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                          (coe v7) (coe v6) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54
        -> case coe v4 of
             C_fr'45'Id_234 v7 -> coe v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v9 v10
               -> case coe v4 of
                    C_fr'45'inl_244 v15
                      -> case coe v2 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                                    -> coe
                                         du_cfD'8315''185''45'rel_1188 (coe v9) (coe v7) (coe v16)
                                         (coe v17) (coe v15)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_fr'45'inr_254 v15
                      -> case coe v2 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                                    -> coe
                                         du_cfD'8315''185''45'rel_1188 (coe v10) (coe v8) (coe v16)
                                         (coe v17) (coe v15)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v9 v10
               -> case coe v4 of
                    C_fr'45'pair_268 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_cfD'8315''185''45'rel_1188 (coe v9) (coe v7)
                                            (coe v19) (coe v21) (coe v17))
                                         (coe
                                            du_cfD'8315''185''45'rel_1188 (coe v10) (coe v8)
                                            (coe v20) (coe v22) (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel._.coerce-base-to-full
d_coerce'45'base'45'to'45'full_1228 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_1228
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Denotation.ValueRel._.coerce-full-to-base
d_coerce'45'full'45'to'45'base_1230 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_1230
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Denotation.ValueRel._.coerce-μ-in
d_coerce'45'μ'45'in_1232 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_1232 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Denotation.ValueRel._.coerce-μ-out
d_coerce'45'μ'45'out_1234 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_1234 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Denotation.ValueRel.cμin-rel
d_cμin'45'rel_1246 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_FRel_216 -> AgdaAny
d_cμin'45'rel_1246 v0 ~v1 ~v2 v3 v4 v5
  = du_cμin'45'rel_1246 v0 v3 v4 v5
du_cμin'45'rel_1246 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> AgdaAny -> T_FRel_216 -> AgdaAny
du_cμin'45'rel_1246 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v4 -> erased
      MAlonzo.Code.Once.Internal.Type.C_Id_14
        -> case coe v3 of
             C_fr'45'Id_234 v6 -> coe v6
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v4 v5
        -> case coe v3 of
             C_fr'45'inl_244 v10
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v2 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe du_cμin'45'rel_1246 (coe v4) (coe v11) (coe v12) (coe v10)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_fr'45'inr_254 v10
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v2 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe du_cμin'45'rel_1246 (coe v5) (coe v11) (coe v12) (coe v10)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v4 v5
        -> case coe v3 of
             C_fr'45'pair_268 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe du_cμin'45'rel_1246 (coe v4) (coe v14) (coe v16) (coe v12))
                                  (coe du_cμin'45'rel_1246 (coe v5) (coe v15) (coe v17) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.cμout-rel
d_cμout'45'rel_1284 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_FRel_216
d_cμout'45'rel_1284 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_cμout'45'rel_1284 v0 v1 v4 v5 v6
du_cμout'45'rel_1284 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_FRel_216
du_cμout'45'rel_1284 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v6
        -> coe du_fr'45'K'8801'_1100
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54
        -> coe C_fr'45'Id_234 v4
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  C_fr'45'inl_244
                                  (coe
                                     du_cμout'45'rel_1284 (coe v9) (coe v7) (coe v11) (coe v12)
                                     (coe v4))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  C_fr'45'inr_254
                                  (coe
                                     du_cμout'45'rel_1284 (coe v10) (coe v8) (coe v11) (coe v12)
                                     (coe v4))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         C_fr'45'pair_268
                                         (coe
                                            du_cμout'45'rel_1284 (coe v9) (coe v7) (coe v11)
                                            (coe v13) (coe v15))
                                         (coe
                                            du_cμout'45'rel_1284 (coe v10) (coe v8) (coe v12)
                                            (coe v14) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel._.cataS-rel
d_cataS'45'rel_1360 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_cataS'45'rel_1360 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cataS'45'rel_1360 v0 v4 v5 v6 v7
du_cataS'45'rel_1360 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
du_cataS'45'rel_1360 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Polynomial.C_'10216'_'10217'_86 v5
        -> coe
             v3
             (coe
                MAlonzo.Code.Once.Internal.Polynomial.du_sfmapCata_120 (coe v0)
                (coe v0) (coe v1) (coe v5))
             (coe
                MAlonzo.Code.Once.Internal.Polynomial.du_sfmapCata_120 (coe v0)
                (coe v0) (coe v2) (coe v5))
             (coe
                du_sfmapCata'45'rel_1366 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v0) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel._.sfmapCata-rel
d_sfmapCata'45'rel_1366 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_sfmapCata'45'rel_1366 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_sfmapCata'45'rel_1366 v0 v4 v5 v6 v7 v8
du_sfmapCata'45'rel_1366 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
du_sfmapCata'45'rel_1366 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> erased
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe
             du_cataS'45'rel_1360 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe
                    du_sfmapCata'45'rel_1366 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v6) (coe v8)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> coe
                    du_sfmapCata'45'rel_1366 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_sfmapCata'45'rel_1366 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v6) (coe v8))
                    (coe
                       du_sfmapCata'45'rel_1366 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel._.anaᴵ-rel
d_ana'7477''45'rel_1422 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_StreamRel_16
d_ana'7477''45'rel_1422 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_ana'7477''45'rel_1422 v0 v4 v5 v6 v7 v8 v9
du_ana'7477''45'rel_1422 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_StreamRel_16
du_ana'7477''45'rel_1422 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_constructor_34
      (coe
         du_anaRun'45'rel_1428 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v1 v4) (coe v2 v5) (coe v3 v4 v5 v6))
-- Once.Denotation.ValueRel._.anaRun-rel
d_anaRun'45'rel_1428 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_anaRun'45'rel_1428 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_anaRun'45'rel_1428 v0 v4 v5 v6 v7 v8 v9
du_anaRun'45'rel_1428 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_anaRun'45'rel_1428 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_anaBlock'45'rel_1434 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v4))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v5))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v6)))
-- Once.Denotation.ValueRel._.anaBlock-rel
d_anaBlock'45'rel_1434 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_anaBlock'45'rel_1434 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_anaBlock'45'rel_1434 v0 v4 v5 v6 v7 v8 v9
du_anaBlock'45'rel_1434 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_anaBlock'45'rel_1434 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v9
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v5 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                         (coe
                                            du_mapAna'45'rel_1442 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v0) (coe v11) (coe v13) (coe v9))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v9
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v5 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_anaRun'45'rel_1428 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v11) (coe v13) (coe v9))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v15 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v18 ->
                              coe
                                du_anaBlock'45'rel_1434 (coe v0) (coe v1) (coe v2) (coe v3)
                                (coe v14 v18) (coe v17 v18) (coe v11 v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel._.mapAna-rel
d_mapAna'45'rel_1442 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapAna'45'rel_1442 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_mapAna'45'rel_1442 v0 v4 v5 v6 v7 v8 v9 v10
du_mapAna'45'rel_1442 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mapAna'45'rel_1442 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> coe v7
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe
             du_ana'7477''45'rel_1422 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v5) (coe v6) (coe v7)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v8 v9
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> coe
                           du_mapAna'45'rel_1442 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                           (coe v10) (coe v11) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> coe
                           du_mapAna'45'rel_1442 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
                           (coe v10) (coe v11) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v8 v9
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_mapAna'45'rel_1442 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v8) (coe v10) (coe v12) (coe v14))
                                  (coe
                                     du_mapAna'45'rel_1442 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v9) (coe v11) (coe v13) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel._.sem-cata
d_sem'45'cata_1492 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_1492 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Denotation.ValueRel.sem-cata-rel
d_sem'45'cata'45'rel_1512 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> T_FRel_216 -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata'45'rel_1512 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_sem'45'cata'45'rel_1512 v0 v1 v4 v5 v6 v7
du_sem'45'cata'45'rel_1512 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> T_FRel_216 -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'cata'45'rel_1512 v0 v1 v2 v3 v4 v5
  = coe
      du_cataS'45'rel_1360
      (coe
         MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
         (coe v0))
      (coe
         (\ v6 ->
            coe
              v2
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
                 (coe v1) (coe v6))))
      (coe
         (\ v6 ->
            coe
              v3
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
                 (coe v1) (coe v6))))
      (coe
         (\ v6 v7 v8 ->
            coe
              v4
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
                 (coe v1) (coe v6))
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
                 (coe v1) (coe v7))
              (coe
                 du_cμout'45'rel_1284 (coe v0) (coe v1) (coe v6) (coe v7)
                 (coe v8))))
      (coe v5)
-- Once.Denotation.ValueRel.layer→srel
d_layer'8594'srel_1530 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_layer'8594'srel_1530 ~v0 v1 v2 v3 v4
  = du_layer'8594'srel_1530 v1 v2 v3 v4
du_layer'8594'srel_1530 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_layer'8594'srel_1530 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10 -> coe v3
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe du_layer'8594'srel_1530 (coe v4) (coe v6) (coe v7) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe du_layer'8594'srel_1530 (coe v5) (coe v6) (coe v7) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe du_layer'8594'srel_1530 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe du_layer'8594'srel_1530 (coe v5) (coe v7) (coe v9) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.srel→layer
d_srel'8594'layer_1574 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_srel'8594'layer_1574 ~v0 v1 v2 v3 v4
  = du_srel'8594'layer_1574 v1 v2 v3 v4
du_srel'8594'layer_1574 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_srel'8594'layer_1574 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10 -> coe v3
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe du_srel'8594'layer_1574 (coe v4) (coe v6) (coe v7) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe du_srel'8594'layer_1574 (coe v5) (coe v6) (coe v7) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe du_srel'8594'layer_1574 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe du_srel'8594'layer_1574 (coe v5) (coe v7) (coe v9) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRel.in-rel
d_in'45'rel_1616 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_StreamRel_16
d_in'45'rel_1616 v0 v1 v2 v3
  = coe
      C_constructor_34
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
            (coe du_srel'8594'layer_1574 (coe v0) (coe v1) (coe v2) (coe v3))))
