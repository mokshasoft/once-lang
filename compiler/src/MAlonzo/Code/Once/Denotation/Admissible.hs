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
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Denotation.Admissible.rawIntLits
d_rawIntLits_6 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> [Integer]
d_rawIntLits_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v1)) (coe d_rawIntLits_6 (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v1 v2
        -> coe d_rawIntLits_6 (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v2)) (coe d_rawIntLits_6 (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v1)) (coe d_rawIntLits_6 (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v1))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_rawIntLits_6 (coe v3)) (coe d_rawIntLits_6 (coe v5)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v1 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v1 v2
        -> coe d_rawIntLits_6 (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawIntLits_6 (coe v2)) (coe d_rawIntLits_6 (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v2
        -> coe d_negLits_8 (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v1 v2
        -> coe d_rawIntLits_6 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible.negLits
d_negLits_8 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> [Integer]
d_negLits_8 v0
  = let v1 = d_rawIntLits_6 (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         _ -> coe v1)
-- Once.Denotation.Admissible.declIntLits
d_declIntLits_46 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 -> [Integer]
d_declIntLits_46 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 v1 v2 v3
        -> coe d_rawIntLits_6 (coe v3)
      MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v1 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible.moduleIntLits
d_moduleIntLits_50 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> [Integer]
d_moduleIntLits_50 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v1
        -> coe du_go_58 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible._.go
d_go_58 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] -> [Integer]
d_go_58 ~v0 v1 = du_go_58 v1
du_go_58 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] -> [Integer]
du_go_58 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_declIntLits_46 (coe v1)) (coe du_go_58 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible.AdmissibleM
d_AdmissibleM_64 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> ()
d_AdmissibleM_64 = erased
-- Once.Denotation.Admissible.admissibleM?
d_admissibleM'63'_74 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_admissibleM'63'_74 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_all'63'_510
      (coe
         MAlonzo.Code.Once.Word.d_inRange'63'_62
         (coe
            MAlonzo.Code.Once.Target.Arch.d_arch'45'int'45'bits_80 (coe v0)))
      (coe d_moduleIntLits_50 (coe v1))
-- Once.Denotation.Admissible.outOfRange
d_outOfRange_80 :: Integer -> [Integer] -> Maybe Integer
d_outOfRange_80 v0 v1
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
                           (coe MAlonzo.Code.Once.Word.d_half_48 (coe v0)))
                        (coe v2))
                     (coe
                        MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880 (coe v2)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                           (MAlonzo.Code.Once.Word.d_half_48 (coe v0)) (1 :: Integer))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe d_outOfRange_80 (coe v0) (coe v3))
                       else coe
                              seq (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Admissible.firstBadLit
d_firstBadLit_106 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> Maybe Integer
d_firstBadLit_106 v0 v1
  = coe
      d_outOfRange_80
      (coe
         MAlonzo.Code.Once.Target.Arch.d_arch'45'int'45'bits_80 (coe v0))
      (coe d_moduleIntLits_50 (coe v1))
