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

module MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.Codegen.AllocExpand
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd

-- Once.CCC.Codegen.AllocExpandClasses.size-of
d_size'45'of_8 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404 ->
  [Integer]
d_size'45'of_8 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2464 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'free'45'heap_2470 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         _ -> coe v1)
-- Once.CCC.Codegen.AllocExpandClasses.sizes
d_sizes_14 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [Integer]
d_sizes_14 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_size'45'of_8 (coe v1)) (coe d_sizes_14 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpandClasses.Sz
d_Sz_20 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer -> ()
d_Sz_20 = erased
-- Once.CCC.Codegen.AllocExpandClasses.Fetch._.fetch
d_fetch_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404
d_fetch_32 ~v0 = du_fetch_32
du_fetch_32 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404
du_fetch_32 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_258
-- Once.CCC.Codegen.AllocExpandClasses.Fetch.sz-at
d_sz'45'at_42 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_sz'45'at_42 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_sz'45'at_42 v1 v2
du_sz'45'at_42 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_sz'45'at_42 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v1 of
             0 -> coe
                    (\ v4 ->
                       coe
                         MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                         (d_size'45'of_8 (coe v2))
                         (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (coe
                       (\ v5 ->
                          coe
                            MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                            (d_size'45'of_8 (coe v2)) (d_sizes_14 (coe v3))
                            (coe du_sz'45'at_42 v3 v4 erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpandClasses.Fetch.sz-alloc
d_sz'45'alloc_82 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_sz'45'alloc_82 ~v0 v1 v2 ~v3 ~v4 = du_sz'45'alloc_82 v1 v2
du_sz'45'alloc_82 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_sz'45'alloc_82 v0 v1 = coe du_sz'45'at_42 v0 v1 erased
-- Once.CCC.Codegen.AllocExpandClasses.Fetch.sz-free
d_sz'45'free_98 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_sz'45'free_98 ~v0 v1 v2 ~v3 ~v4 = du_sz'45'free_98 v1 v2
du_sz'45'free_98 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_sz'45'free_98 v0 v1 = coe du_sz'45'at_42 v0 v1 erased
-- Once.CCC.Codegen.AllocExpandClasses.largest
d_largest_108 :: [Integer] -> Integer
d_largest_108
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208)
      (coe (0 :: Integer))
-- Once.CCC.Codegen.AllocExpandClasses.≤-largest
d_'8804''45'largest_114 ::
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'largest_114 ~v0 v1 v2 = du_'8804''45'largest_114 v1 v2
du_'8804''45'largest_114 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'largest_114 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v6
               -> coe
                    MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
                    (coe
                       MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962))
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                       (coe MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4582))
                    (coe v2) (coe d_largest_108 v3)
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe du_'8804''45'largest_114 (coe v3) (coe v6))
                    (coe
                       MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
                       (coe
                          MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962))
                       (coe
                          MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                          (coe MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4582))
                       (coe v2) (coe d_largest_108 v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpandClasses.pool
d_pool_126 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpand.T_Classes_8
d_pool_126 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.AllocExpand.C_constructor_22
      (coe (1 :: Integer)) (coe (\ v1 -> 0 :: Integer))
      (coe
         (\ v1 ->
            MAlonzo.Code.Data.Nat.Base.d__'8852'__208
              (coe v1) (coe d_largest_108 (d_sizes_14 (coe v0)))))
-- Once.CCC.Codegen.AllocExpandClasses.Pool.C
d_C_138 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpand.T_Classes_8
d_C_138 v0 = coe d_pool_126 (coe v0)
-- Once.CCC.Codegen.AllocExpandClasses.Pool.small
d_small_140 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_small_140 ~v0 = du_small_140
du_small_140 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_small_140
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Once.CCC.Codegen.AllocExpandClasses.Pool.in-range
d_in'45'range_144 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_in'45'range_144 ~v0 ~v1 = du_in'45'range_144
du_in'45'range_144 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_in'45'range_144
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.CCC.Codegen.AllocExpandClasses.Pool.fits
d_fits_148 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_148 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4582))
      (coe v1) (coe d_largest_108 (d_sizes_14 (coe v0)))
-- Once.CCC.Codegen.AllocExpandClasses.Pool.uniform
d_uniform_156 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uniform_156 = erased
