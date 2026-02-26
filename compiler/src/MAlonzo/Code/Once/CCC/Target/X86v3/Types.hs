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

module MAlonzo.Code.Once.CCC.Target.X86v3.Types where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Target.X86v3.Types._⊕_
d__'8853'__10 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32
d__'8853'__10 = coe MAlonzo.Code.Once.Type.C__'43'__40
-- Once.CCC.Target.X86v3.Types.stack-type-slots
d_stack'45'type'45'slots_12 ::
  MAlonzo.Code.Once.Type.T_Type_32 -> Integer
d_stack'45'type'45'slots_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_34 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Type.C_Void_36 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Type.C__'42'__38 v1 v2 -> coe (2 :: Integer)
      MAlonzo.Code.Once.Type.C__'43'__40 v1 v2 -> coe (2 :: Integer)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v1 v2 v3
        -> coe (2 :: Integer)
      MAlonzo.Code.Once.Type.C_Eff_44 v1 v2
        -> coe d_stack'45'type'45'slots_12 (coe v2)
      MAlonzo.Code.Once.Type.C_Fix_46 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Int_48 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Float_50 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Str_52 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Buffer_54 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_TVar_56 v1 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86v3.Types.heap-type-slots
d_heap'45'type'45'slots_24 ::
  MAlonzo.Code.Once.Type.T_Type_32 -> Integer
d_heap'45'type'45'slots_24 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_34 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Type.C_Void_36 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Type.C__'42'__38 v1 v2 -> coe (2 :: Integer)
      MAlonzo.Code.Once.Type.C__'43'__40 v1 v2 -> coe (2 :: Integer)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v1 v2 v3
        -> coe (2 :: Integer)
      MAlonzo.Code.Once.Type.C_Eff_44 v1 v2
        -> coe d_heap'45'type'45'slots_24 (coe v2)
      MAlonzo.Code.Once.Type.C_Fix_46 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Int_48 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Float_50 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Str_52 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Buffer_54 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_TVar_56 v1 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86v3.Types.type-slots
d_type'45'slots_36 :: MAlonzo.Code.Once.Type.T_Type_32 -> Integer
d_type'45'slots_36 = coe d_stack'45'type'45'slots_12
-- Once.CCC.Target.X86v3.Types.⟦Fix⟧
d_'10214'Fix'10215'_40 a0 = ()
newtype T_'10214'Fix'10215'_40 = C_wrap_48 AgdaAny
-- Once.CCC.Target.X86v3.Types.⟦Fix⟧.unwrap
d_unwrap_46 :: T_'10214'Fix'10215'_40 -> AgdaAny
d_unwrap_46 v0
  = case coe v0 of
      C_wrap_48 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86v3.Types.⟦_⟧
d_'10214'_'10215'_50 :: MAlonzo.Code.Once.Type.T_Type_32 -> ()
d_'10214'_'10215'_50 = erased
-- Once.CCC.Target.X86v3.Types.fst
d_fst_74 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_74 ~v0 ~v1 v2 = du_fst_74 v2
du_fst_74 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_fst_74 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Target.X86v3.Types.snd
d_snd_80 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_80 ~v0 ~v1 v2 = du_snd_80 v2
du_snd_80 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_snd_80 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Target.X86v3.Types.pair
d_pair_86 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair_86 ~v0 ~v1 v2 v3 = du_pair_86 v2 v3
du_pair_86 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair_86 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.CCC.Target.X86v3.Types.inl
d_inl_96 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inl_96 ~v0 ~v1 = du_inl_96
du_inl_96 :: AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_inl_96 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
-- Once.CCC.Target.X86v3.Types.inr
d_inr_102 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inr_102 ~v0 ~v1 = du_inr_102
du_inr_102 :: AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_inr_102 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
-- Once.CCC.Target.X86v3.Types.case
d_case_110 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_case_110 ~v0 ~v1 ~v2 v3 v4 v5 = du_case_110 v3 v4 v5
du_case_110 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_case_110 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v0 v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86v3.Types.fold
d_fold_126 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny -> T_'10214'Fix'10215'_40
d_fold_126 ~v0 v1 = du_fold_126 v1
du_fold_126 :: AgdaAny -> T_'10214'Fix'10215'_40
du_fold_126 v0 = coe C_wrap_48 (coe v0)
-- Once.CCC.Target.X86v3.Types.unfold
d_unfold_132 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_'10214'Fix'10215'_40 -> AgdaAny
d_unfold_132 ~v0 v1 = du_unfold_132 v1
du_unfold_132 :: T_'10214'Fix'10215'_40 -> AgdaAny
du_unfold_132 v0
  = case coe v0 of
      C_wrap_48 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86v3.Types.fst-pair
d_fst'45'pair_144 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'pair_144 = erased
-- Once.CCC.Target.X86v3.Types.snd-pair
d_snd'45'pair_158 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'pair_158 = erased
-- Once.CCC.Target.X86v3.Types.case-inl
d_case'45'inl_176 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'inl_176 = erased
-- Once.CCC.Target.X86v3.Types.case-inr
d_case'45'inr_196 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'inr_196 = erased
-- Once.CCC.Target.X86v3.Types.unfold-fold
d_unfold'45'fold_208 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unfold'45'fold_208 = erased
-- Once.CCC.Target.X86v3.Types.fold-unfold
d_fold'45'unfold_216 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_'10214'Fix'10215'_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'unfold_216 = erased
