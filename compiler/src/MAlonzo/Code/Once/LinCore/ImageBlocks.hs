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

module MAlonzo.Code.Once.LinCore.ImageBlocks where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.LinCore.Keys
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.LinCore.ImageBlocks._.Sig
d_Sig_12 a0 a1 = ()
-- Once.LinCore.ImageBlocks._.Sig.info
d_info_18 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_18 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)
-- Once.LinCore.ImageBlocks._.Sig.sA
d_sA_20 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_20 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_688 (coe v0)
-- Once.LinCore.ImageBlocks._.Sig.sB
d_sB_22 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_22 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_690 (coe v0)
-- Once.LinCore.ImageBlocks._.Univ
d_Univ_30 a0 a1 = ()
-- Once.LinCore.ImageBlocks._.Univ.cts
d_cts_36 ::
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_cts_36 v0
  = coe MAlonzo.Code.Once.LinCore.Keys.d_cts_1894 (coe v0)
-- Once.LinCore.ImageBlocks._.Univ.cts⊆
d_cts'8838'_38 ::
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_cts'8838'_38 v0
  = coe MAlonzo.Code.Once.LinCore.Keys.d_cts'8838'_1898 (coe v0)
-- Once.LinCore.ImageBlocks._.Univ.keys
d_keys_40 ::
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_keys_40 v0
  = coe MAlonzo.Code.Once.LinCore.Keys.d_keys_1884 (coe v0)
-- Once.LinCore.ImageBlocks._.Univ.nus
d_nus_42 ::
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_nus_42 v0
  = coe MAlonzo.Code.Once.LinCore.Keys.d_nus_1888 (coe v0)
-- Once.LinCore.ImageBlocks._.Univ.obs
d_obs_44 ::
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_obs_44 v0
  = coe MAlonzo.Code.Once.LinCore.Keys.d_obs_1890 (coe v0)
-- Once.LinCore.ImageBlocks._.Univ.ops
d_ops_46 ::
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  [MAlonzo.Code.Once.LinCore.Core.T_Sig_680]
d_ops_46 v0
  = coe MAlonzo.Code.Once.LinCore.Keys.d_ops_1892 (coe v0)
-- Once.LinCore.ImageBlocks._.Univ.tys
d_tys_48 ::
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_tys_48 v0
  = coe MAlonzo.Code.Once.LinCore.Keys.d_tys_1886 (coe v0)
-- Once.LinCore.ImageBlocks._.Univ.tys-cl
d_tys'45'cl_50 ::
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_tys'45'cl_50 v0
  = coe MAlonzo.Code.Once.LinCore.Keys.d_tys'45'cl_1902 (coe v0)
-- Once.LinCore.ImageBlocks.own
d_own_56 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
d_own_56 ~v0 ~v1 ~v2 ~v3 v4 = du_own_56 v4
du_own_56 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
du_own_56 v0
  = case coe v0 of
      MAlonzo.Code.Once.SigOp.Info.C_blockV_86 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_72 (coe v1)
                (coe v2) (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.SigOp.Info.C_ffiV_88
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_callsV_90
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_emitsV_92
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_haltsV_94
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_primV_96 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ImageBlocks.opBlks
d_opBlks_64 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
d_opBlks_64 ~v0 ~v1 v2 = du_opBlks_64 v2
du_opBlks_64 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
du_opBlks_64 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         du_own_56
         (coe
            MAlonzo.Code.Once.SigOp.Info.d_sem_118
            (coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0))))
      (coe
         MAlonzo.Code.Once.Arith.Machine.Rewrite.du_sigop'45'blocks_200
         (coe
            MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_18
            (coe
               MAlonzo.Code.Once.SigOp.Info.d_sem_118
               (coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)))))
-- Once.LinCore.ImageBlocks.imageBlocks
d_imageBlocks_68 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
d_imageBlocks_68 ~v0 ~v1 v2 = du_imageBlocks_68 v2
du_imageBlocks_68 ::
  MAlonzo.Code.Once.LinCore.Keys.T_Univ_1862 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
du_imageBlocks_68 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_concatMap_246 (coe du_opBlks_64)
      (coe MAlonzo.Code.Once.LinCore.Keys.d_ops_1892 (coe v0))
-- Once.LinCore.ImageBlocks.op-blocks
d_op'45'blocks_78 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [MAlonzo.Code.Once.LinCore.Core.T_Sig_680] ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_op'45'blocks_78 ~v0 ~v1 v2 ~v3 v4 ~v5 v6
  = du_op'45'blocks_78 v2 v4 v6
du_op'45'blocks_78 ::
  [MAlonzo.Code.Once.LinCore.Core.T_Sig_680] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_op'45'blocks_78 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v7
               -> coe
                    MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                    (coe du_opBlks_64 (coe v3)) v2
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
               -> coe
                    MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                    (coe du_opBlks_64 (coe v3))
                    (coe
                       MAlonzo.Code.Data.List.Base.du_concatMap_246 (coe du_opBlks_64)
                       (coe v4))
                    (coe du_op'45'blocks_78 (coe v4) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
