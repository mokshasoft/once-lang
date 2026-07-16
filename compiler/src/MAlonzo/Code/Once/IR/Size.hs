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
import qualified MAlonzo.Code.Once.IRTy

-- Once.IR.Size.ir-size
d_ir'45'size_10 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'size_10 v0 v1 v2
  = let v3 = 1 :: Integer in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.IR.C_id_22 -> coe (1 :: Integer)
         MAlonzo.Code.Once.IR.C__'8728'__30 v5 v7 v8
           -> coe
                addInt
                (coe
                   addInt (coe (1 :: Integer))
                   (coe d_ir'45'size_10 (coe v0) (coe v5) (coe v8)))
                (coe d_ir'45'size_10 (coe v5) (coe v1) (coe v7))
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v7 v8 v9
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
                  -> coe
                       addInt
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe d_ir'45'size_10 (coe v0) (coe v10) (coe v7)))
                       (coe d_ir'45'size_10 (coe v0) (coe v11) (coe v8))
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_fst_44
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7 -> coe (1 :: Integer)
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_snd_50
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7 -> coe (1 :: Integer)
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_inl_56 v6
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v7 v8 -> coe (1 :: Integer)
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_inr_62 v6
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v7 v8 -> coe (1 :: Integer)
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_case_70 v7 v8
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
                  -> coe
                       addInt
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe d_ir'45'size_10 (coe v9) (coe v1) (coe v7)))
                       (coe d_ir'45'size_10 (coe v10) (coe v1) (coe v8))
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_terminal_74 -> coe (1 :: Integer)
         MAlonzo.Code.Once.IR.C_initial_78 -> coe (1 :: Integer)
         MAlonzo.Code.Once.IR.C_curry_86 v7 v8
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
                  -> coe
                       addInt (coe (2 :: Integer))
                       (coe
                          d_ir'45'size_10
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v9))
                          (coe v10) (coe v7))
                _ -> coe v3
         MAlonzo.Code.Once.IR.C_apply_92
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9 -> coe (1 :: Integer)
                       _ -> coe v3
                _ -> coe v3
         _ -> coe v3)
-- Once.IR.Size.ir-size-nt
d_ir'45'size'45'nt_16 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> Integer
d_ir'45'size'45'nt_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_156 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_ntK_162 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_K_8 v7
                      -> coe
                           addInt (coe (1 :: Integer))
                           (coe d_ir'45'size_10 (coe v6) (coe v7) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_170 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_16 (coe v7) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_178 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_16 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_186 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size'45'nt_16 (coe v8) (coe v1) (coe v6)))
                    (coe d_ir'45'size'45'nt_16 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_194 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_16 (coe v0) (coe v7) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_202 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe d_ir'45'size'45'nt_16 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_210 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size'45'nt_16 (coe v0) (coe v8) (coe v6)))
                    (coe d_ir'45'size'45'nt_16 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Size.∘-f-smaller
d_'8728''45'f'45'smaller_76 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8728''45'f'45'smaller_76 v0 v1 ~v2 v3 ~v4
  = du_'8728''45'f'45'smaller_76 v0 v1 v3
du_'8728''45'f'45'smaller_76 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8728''45'f'45'smaller_76 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'n'43'm_3748
      (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.IR.Size.∘-g-smaller
d_'8728''45'g'45'smaller_92 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8728''45'g'45'smaller_92 ~v0 v1 v2 ~v3 v4
  = du_'8728''45'g'45'smaller_92 v1 v2 v4
du_'8728''45'g'45'smaller_92 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8728''45'g'45'smaller_92 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2)))
-- Once.IR.Size.⟨,⟩-f-smaller
d_'10216''44''10217''45'f'45'smaller_110 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'f'45'smaller_110 v0 v1 ~v2 v3 ~v4 ~v5
  = du_'10216''44''10217''45'f'45'smaller_110 v0 v1 v3
du_'10216''44''10217''45'f'45'smaller_110 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'f'45'smaller_110 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2)))
-- Once.IR.Size.⟨,⟩-g-smaller
d_'10216''44''10217''45'g'45'smaller_130 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'g'45'smaller_130 v0 ~v1 v2 ~v3 v4 ~v5
  = du_'10216''44''10217''45'g'45'smaller_130 v0 v2 v4
du_'10216''44''10217''45'g'45'smaller_130 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'g'45'smaller_130 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2)))
-- Once.IR.Size.curry-smaller
d_curry'45'smaller_148 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_curry'45'smaller_148 v0 v1 v2 v3 ~v4
  = du_curry'45'smaller_148 v0 v1 v2 v3
du_curry'45'smaller_148 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_curry'45'smaller_148 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
      (coe
         d_ir'45'size_10
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) (coe v2)
         (coe v3))
-- Once.IR.Size.case-f-smaller
d_case'45'f'45'smaller_164 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_case'45'f'45'smaller_164 v0 ~v1 v2 v3 ~v4
  = du_case'45'f'45'smaller_164 v0 v2 v3
du_case'45'f'45'smaller_164 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_case'45'g'45'smaller_180 ~v0 v1 v2 ~v3 v4
  = du_case'45'g'45'smaller_180 v1 v2 v4
du_case'45'g'45'smaller_180 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_case'45'g'45'smaller_180 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe d_ir'45'size_10 (coe v0) (coe v1) (coe v2)))
