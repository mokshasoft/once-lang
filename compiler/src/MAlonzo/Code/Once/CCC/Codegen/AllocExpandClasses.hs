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
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
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
-- Once.CCC.Codegen.AllocExpandClasses.idx-of
d_idx'45'of_166 :: Integer -> [Integer] -> Integer
d_idx'45'of_166 v0 v1
  = case coe v1 of
      [] -> coe (0 :: Integer)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe eqInt (coe v0) (coe v2)) (coe (0 :: Integer))
             (coe
                addInt (coe (1 :: Integer))
                (coe d_idx'45'of_166 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpandClasses.idx-≤
d_idx'45''8804'_180 ::
  Integer -> [Integer] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_idx'45''8804'_180 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      (:) v2 v3
        -> coe du_by_196 (coe v0) (coe v3) (coe eqInt (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpandClasses._.by
d_by_196 ::
  Integer ->
  Integer ->
  [Integer] -> Bool -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_by_196 v0 ~v1 v2 v3 = du_by_196 v0 v2 v3
du_by_196 ::
  Integer ->
  [Integer] -> Bool -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_by_196 v0 v1 v2
  = if coe v2
      then coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      else coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (d_idx'45''8804'_180 (coe v0) (coe v1))
-- Once.CCC.Codegen.AllocExpandClasses.idx-inj
d_idx'45'inj_204 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idx'45'inj_204 = erased
-- Once.CCC.Codegen.AllocExpandClasses._.by
d_by_228 ::
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_by_228 = erased
-- Once.CCC.Codegen.AllocExpandClasses._._.tl
d_tl_250 ::
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_tl_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13 v14
  = du_tl_250 v14
du_tl_250 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_tl_250 v0
  = case coe v0 of
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v3
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpandClasses._._._.no
d_no_262 ::
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no_262 = erased
-- Once.CCC.Codegen.AllocExpandClasses.dsizes
d_dsizes_268 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [Integer]
d_dsizes_268 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_deduplicate_882
      (coe MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796)
      (coe d_sizes_14 (coe v0))
-- Once.CCC.Codegen.AllocExpandClasses.slab-of
d_slab'45'of_272 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Bool -> MAlonzo.Code.Once.CCC.Codegen.AllocExpand.T_Classes_8
d_slab'45'of_272 v0 v1
  = if coe v1
      then coe
             MAlonzo.Code.Once.CCC.Codegen.AllocExpand.C_constructor_22
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.List.Base.du_length_268 (d_dsizes_268 (coe v0))))
             (coe
                (\ v2 -> d_idx'45'of_166 (coe v2) (coe d_dsizes_268 (coe v0))))
             (coe (\ v2 -> v2))
      else coe d_pool_126 (coe v0)
-- Once.CCC.Codegen.AllocExpandClasses.slab
d_slab_282 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpand.T_Classes_8
d_slab_282 v0
  = coe
      d_slab'45'of_272 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268 (d_dsizes_268 (coe v0)))
         (coe (60 :: Integer)))
-- Once.CCC.Codegen.AllocExpandClasses.Slab.∈-dd
d_'8712''45'dd_294 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [Integer] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8712''45'dd_294 ~v0 v1 v2 = du_'8712''45'dd_294 v1 v2
du_'8712''45'dd_294 ::
  [Integer] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'8712''45'dd_294 v0 v1
  = coe
      MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'deduplicate'8314'_614
      (coe MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796) (coe v0)
      (coe v1)
-- Once.CCC.Codegen.AllocExpandClasses.Slab.b
d_b_296 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] -> Bool
d_b_296 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
      (coe
         MAlonzo.Code.Data.List.Base.du_length_268 (d_dsizes_268 (coe v0)))
      (coe (60 :: Integer))
-- Once.CCC.Codegen.AllocExpandClasses.Slab.C
d_C_298 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpand.T_Classes_8
d_C_298 v0 = coe d_slab_282 (coe v0)
-- Once.CCC.Codegen.AllocExpandClasses.Slab.Asks
d_Asks_302 a0 a1 = ()
data T_Asks_302
  = C_constructor_338 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                      (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.CCC.Codegen.AllocExpandClasses.Slab.Asks.small
d_small_322 ::
  T_Asks_302 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_small_322 v0
  = case coe v0 of
      C_constructor_338 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpandClasses.Slab.Asks.in-range
d_in'45'range_326 ::
  T_Asks_302 -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_in'45'range_326 v0
  = case coe v0 of
      C_constructor_338 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpandClasses.Slab.Asks.fits
d_fits_330 ::
  T_Asks_302 -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_330 v0
  = case coe v0 of
      C_constructor_338 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.AllocExpandClasses.Slab.Asks.uniform
d_uniform_336 ::
  T_Asks_302 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uniform_336 = erased
-- Once.CCC.Codegen.AllocExpandClasses.Slab.asks
d_asks_342 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Asks_302
d_asks_342 v0 v1
  = if coe v1
      then coe
             (\ v2 ->
                coe
                  C_constructor_338
                  (coe
                     MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                     (coe
                        MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                        (coe
                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                       (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                                        coe (coe (\ v4 -> v3)))
                                       (coe (0 :: Integer))
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_deduplicate_882
                                          (coe MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796)
                                          (coe d_sizes_14 (coe v0))))))
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
                                 (coe (61 :: Integer)))))))
                  (\ v3 ->
                     coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (d_idx'45''8804'_180 (coe v3) (coe d_dsizes_268 (coe v0))))
                  (\ v3 ->
                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3)))
      else coe
             (\ v2 ->
                coe
                  C_constructor_338 (coe du_small_140)
                  (\ v3 -> coe du_in'45'range_144) (d_fits_148 (coe v0)))
-- Once.CCC.Codegen.AllocExpandClasses.Slab.A
d_A_360 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  T_Asks_302
d_A_360 v0 = coe d_asks_342 v0 (d_b_296 (coe v0)) erased
-- Once.CCC.Codegen.AllocExpandClasses.Slab.small
d_small_362 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_small_362 v0 = coe d_small_322 (coe d_A_360 (coe v0))
-- Once.CCC.Codegen.AllocExpandClasses.Slab.in-range
d_in'45'range_366 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_in'45'range_366 v0 = coe d_in'45'range_326 (coe d_A_360 (coe v0))
-- Once.CCC.Codegen.AllocExpandClasses.Slab.fits
d_fits_370 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_370 v0 = coe d_fits_330 (coe d_A_360 (coe v0))
-- Once.CCC.Codegen.AllocExpandClasses.Slab.uniform
d_uniform_376 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uniform_376 = erased
