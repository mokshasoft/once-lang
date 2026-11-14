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

module MAlonzo.Code.Once.Denotation.Admissible where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Denotation.Admissible.rawIntLits
d_rawIntLits_6 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 -> [Integer]
d_rawIntLits_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_46 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_48 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v1)) (coe d_rawIntLits_6 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_54 v1 v2
        -> coe d_rawIntLits_6 (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_56 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v2)) (coe d_rawIntLits_6 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_58 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v1)) (coe d_rawIntLits_6 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_60 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v1))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_rawIntLits_6 (coe v3)) (coe d_rawIntLits_6 (coe v5)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_62
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_64 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_66 v1 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_68 v1 v2
        -> coe d_rawIntLits_6 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_70 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v2)) (coe d_rawIntLits_6 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_72 v1
        -> coe d_rawIntLits_6 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible.declIntLits
d_declIntLits_38 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_104 -> [Integer]
d_declIntLits_38 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_106 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_108 v1 v2
        -> coe d_rawIntLits_6 (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_110 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeAlias_112 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_114 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible.moduleIntLits
d_moduleIntLits_42 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_116 -> [Integer]
d_moduleIntLits_42 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_122 v1
        -> coe du_go_50 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible._.go
d_go_50 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_104] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_104] -> [Integer]
d_go_50 ~v0 v1 = du_go_50 v1
du_go_50 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_104] -> [Integer]
du_go_50 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_declIntLits_38 (coe v1)) (coe du_go_50 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible.AdmissibleM
d_AdmissibleM_56 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_116 -> ()
d_AdmissibleM_56 = erased
-- Once.Denotation.Admissible.admissibleM?
d_admissibleM'63'_66 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_116 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_admissibleM'63'_66 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_all'63'_510
      (coe
         MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66
         (coe
            MAlonzo.Code.Once.Target.Arch.d_arch'45'int'45'bits_64 (coe v0)))
      (coe d_moduleIntLits_42 (coe v1))
-- Once.Denotation.Admissible.outOfRange
d_outOfRange_72 :: Integer -> [Integer] -> Maybe Integer
d_outOfRange_72 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                     (coe
                        MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d_'45'__260
                           (coe MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0)))
                        (coe v2))
                     (coe
                        MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880 (coe v2)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                           (MAlonzo.Code.Once.Spec.Word.d_half_50 (coe v0))
                           (1 :: Integer))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe d_outOfRange_72 (coe v0) (coe v3))
                       else coe
                              seq (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible.firstBadLit
d_firstBadLit_98 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_116 -> Maybe Integer
d_firstBadLit_98 v0 v1
  = coe
      d_outOfRange_72
      (coe
         MAlonzo.Code.Once.Target.Arch.d_arch'45'int'45'bits_64 (coe v0))
      (coe d_moduleIntLits_42 (coe v1))
