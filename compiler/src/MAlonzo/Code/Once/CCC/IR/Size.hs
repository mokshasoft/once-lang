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

module MAlonzo.Code.Once.CCC.IR.Size where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.IR.Size.ir-size
d_ir'45'size_12 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 -> Integer
d_ir'45'size_12 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_28 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C__'8728'__36 v4 v6 v7
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer))
                (coe d_ir'45'size_12 (coe v0) (coe v4) (coe v7)))
             (coe d_ir'45'size_12 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_44 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size_12 (coe v0) (coe v9) (coe v6)))
                    (coe d_ir'45'size_12 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_50 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_snd_56 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_inl_62 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_inr_68 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_case_76 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size_12 (coe v8) (coe v1) (coe v6)))
                    (coe d_ir'45'size_12 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_80 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_initial_84 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_curry_94 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       d_ir'45'size_12
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v9))
                       (coe v11) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_102 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_arr_110 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_In_114 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_118 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Cata_124 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       d_ir'45'size_12
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v1))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_130 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       d_ir'45'size_12
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_134 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_138 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Ana_144 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       d_ir'45'size_12 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_152 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    addInt
                    (coe
                       addInt (coe (2 :: Integer))
                       (coe d_ir'45'size'45'nt_18 (coe v10) (coe v3) (coe v9)))
                    (coe
                       d_ir'45'size_12
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Fuse_160 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    addInt
                    (coe
                       addInt (coe (2 :: Integer))
                       (coe d_ir'45'size'45'nt_18 (coe v10) (coe v3) (coe v9)))
                    (coe
                       d_ir'45'size_12
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_162 v3
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_const_166 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_SigOp_172 v5 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Size.ir-size-nt
d_ir'45'size'45'nt_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_24 -> Integer
d_ir'45'size'45'nt_18 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_174 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_ntK_180 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v7
                      -> coe
                           addInt (coe (1 :: Integer))
                           (coe d_ir'45'size_12 (coe v6) (coe v7) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntFst_188 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_18 (coe v7) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_196 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_18 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntCase_204 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size'45'nt_18 (coe v8) (coe v1) (coe v6)))
                    (coe d_ir'45'size'45'nt_18 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInl_212 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_18 (coe v0) (coe v7) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInr_220 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_18 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntPair_228 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size'45'nt_18 (coe v0) (coe v8) (coe v6)))
                    (coe d_ir'45'size'45'nt_18 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Size.∘-f-smaller
d_'8728''45'f'45'smaller_76 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8728''45'f'45'smaller_76 v0 v1 ~v2 v3 ~v4
  = du_'8728''45'f'45'smaller_76 v0 v1 v3
du_'8728''45'f'45'smaller_76 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8728''45'f'45'smaller_76 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'n'43'm_3748
      (coe d_ir'45'size_12 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.CCC.IR.Size.∘-g-smaller
d_'8728''45'g'45'smaller_92 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8728''45'g'45'smaller_92 ~v0 v1 v2 ~v3 v4
  = du_'8728''45'g'45'smaller_92 v1 v2 v4
du_'8728''45'g'45'smaller_92 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8728''45'g'45'smaller_92 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_12 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.IR.Size.⟨,⟩-f-smaller
d_'10216''44''10217''45'f'45'smaller_110 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'f'45'smaller_110 v0 v1 ~v2 v3 ~v4 ~v5
  = du_'10216''44''10217''45'f'45'smaller_110 v0 v1 v3
du_'10216''44''10217''45'f'45'smaller_110 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'f'45'smaller_110 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_12 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.IR.Size.⟨,⟩-g-smaller
d_'10216''44''10217''45'g'45'smaller_130 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'g'45'smaller_130 v0 ~v1 v2 ~v3 v4 ~v5
  = du_'10216''44''10217''45'g'45'smaller_130 v0 v2 v4
du_'10216''44''10217''45'g'45'smaller_130 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'g'45'smaller_130 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe d_ir'45'size_12 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.IR.Size.curry-smaller
d_curry'45'smaller_150 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_curry'45'smaller_150 v0 v1 v2 ~v3 v4 ~v5
  = du_curry'45'smaller_150 v0 v1 v2 v4
du_curry'45'smaller_150 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_curry'45'smaller_150 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
      (coe
         d_ir'45'size_12
         (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1))
         (coe v2) (coe v3))
-- Once.CCC.IR.Size.case-f-smaller
d_case'45'f'45'smaller_166 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_case'45'f'45'smaller_166 v0 ~v1 v2 v3 ~v4
  = du_case'45'f'45'smaller_166 v0 v2 v3
du_case'45'f'45'smaller_166 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_case'45'f'45'smaller_166 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_12 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.IR.Size.case-g-smaller
d_case'45'g'45'smaller_182 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_case'45'g'45'smaller_182 ~v0 v1 v2 ~v3 v4
  = du_case'45'g'45'smaller_182 v1 v2 v4
du_case'45'g'45'smaller_182 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_case'45'g'45'smaller_182 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe d_ir'45'size_12 (coe v0) (coe v1) (coe v2)))
