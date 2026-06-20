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

module MAlonzo.Code.Once.IR.Size where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.IR.Size.ir-size
d_ir'45'size_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'size_10 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C__'8728'__30 v4 v6 v7
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer))
                (coe d_ir'45'size_10 (coe v0) (coe v4) (coe v7)))
             (coe d_ir'45'size_10 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size_10 (coe v0) (coe v9) (coe v6)))
                    (coe d_ir'45'size_10 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_snd_50 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_inl_56 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_inr_62 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_case_70 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size_10 (coe v8) (coe v1) (coe v6)))
                    (coe d_ir'45'size_10 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_initial_78 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_curry_88 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       d_ir'45'size_10
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v9))
                       (coe v11) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_96 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_arr_104 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_In_108 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_out'45'μ_112 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_Cata_118 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       d_ir'45'size_10
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v1))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_124 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       d_ir'45'size_10
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_128 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_in'45'ν_132 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_Ana_138 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       d_ir'45'size_10 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Hylo_146 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    addInt
                    (coe
                       addInt (coe (2 :: Integer))
                       (coe d_ir'45'size'45'nt_16 (coe v10) (coe v3) (coe v9)))
                    (coe
                       d_ir'45'size_10
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Fuse_154 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    addInt
                    (coe
                       addInt (coe (2 :: Integer))
                       (coe d_ir'45'size'45'nt_16 (coe v10) (coe v3) (coe v9)))
                    (coe
                       d_ir'45'size_10
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_free'45'heap_156 v3 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_const_160 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_SigOp_166 v5 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Size.ir-size-nt
d_ir'45'size'45'nt_16 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> Integer
d_ir'45'size'45'nt_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_168 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_ntK_174 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v7
                      -> coe
                           addInt (coe (1 :: Integer))
                           (coe d_ir'45'size_10 (coe v6) (coe v7) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_182 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_16 (coe v7) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_190 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_16 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_198 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size'45'nt_16 (coe v8) (coe v1) (coe v6)))
                    (coe d_ir'45'size'45'nt_16 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_206 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_16 (coe v0) (coe v7) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_214 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_16 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_222 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size'45'nt_16 (coe v0) (coe v8) (coe v6)))
                    (coe d_ir'45'size'45'nt_16 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Size.∘-f-smaller
d_'8728''45'f'45'smaller_74 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8728''45'f'45'smaller_74 v0 v1 ~v2 v3 ~v4
  = du_'8728''45'f'45'smaller_74 v0 v1 v3
du_'8728''45'f'45'smaller_74 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8728''45'f'45'smaller_74 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'n'43'm_3748
      (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.IR.Size.∘-g-smaller
d_'8728''45'g'45'smaller_90 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8728''45'g'45'smaller_90 ~v0 v1 v2 ~v3 v4
  = du_'8728''45'g'45'smaller_90 v1 v2 v4
du_'8728''45'g'45'smaller_90 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8728''45'g'45'smaller_90 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2)))
-- Once.IR.Size.⟨,⟩-f-smaller
d_'10216''44''10217''45'f'45'smaller_108 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'f'45'smaller_108 v0 v1 ~v2 v3 ~v4 ~v5
  = du_'10216''44''10217''45'f'45'smaller_108 v0 v1 v3
du_'10216''44''10217''45'f'45'smaller_108 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'f'45'smaller_108 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2)))
-- Once.IR.Size.⟨,⟩-g-smaller
d_'10216''44''10217''45'g'45'smaller_128 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'g'45'smaller_128 v0 ~v1 v2 ~v3 v4 ~v5
  = du_'10216''44''10217''45'g'45'smaller_128 v0 v2 v4
du_'10216''44''10217''45'g'45'smaller_128 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'g'45'smaller_128 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2)))
-- Once.IR.Size.curry-smaller
d_curry'45'smaller_148 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_curry'45'smaller_148 v0 v1 v2 ~v3 v4 ~v5
  = du_curry'45'smaller_148 v0 v1 v2 v4
du_curry'45'smaller_148 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_curry'45'smaller_148 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
      (coe
         d_ir'45'size_10
         (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1))
         (coe v2) (coe v3))
-- Once.IR.Size.case-f-smaller
d_case'45'f'45'smaller_164 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_case'45'f'45'smaller_164 v0 ~v1 v2 v3 ~v4
  = du_case'45'f'45'smaller_164 v0 v2 v3
du_case'45'f'45'smaller_164 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_case'45'f'45'smaller_164 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2)))
-- Once.IR.Size.case-g-smaller
d_case'45'g'45'smaller_180 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_case'45'g'45'smaller_180 ~v0 v1 v2 ~v3 v4
  = du_case'45'g'45'smaller_180 v1 v2 v4
du_case'45'g'45'smaller_180 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_case'45'g'45'smaller_180 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2)))
