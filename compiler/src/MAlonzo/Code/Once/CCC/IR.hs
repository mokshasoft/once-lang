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

module MAlonzo.Code.Once.CCC.IR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.SlotMachine
import qualified MAlonzo.Code.Once.CCC.Target.X86v3.Types
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.IR.AllocMode
d_AllocMode_6 = ()
data T_AllocMode_6 = C_Stack_8 | C_Heap_10
-- Once.CCC.IR.IR
d_IR_12 a0 a1 = ()
data T_IR_12
  = C_id_16 |
    C__'8728'__24 MAlonzo.Code.Once.Type.T_Type_32 T_IR_12 T_IR_12 |
    C_'10216'_'44'_'10217'__32 T_IR_12 T_IR_12 T_AllocMode_6 |
    C_fst'45'ir_38 | C_snd'45'ir_44 | C_inl'45'ir_50 T_AllocMode_6 |
    C_inr'45'ir_56 T_AllocMode_6 | C_case'45'ir_64 T_IR_12 T_IR_12 |
    C_terminal_68 | C_initial_72 | C_curry_82 T_IR_12 T_AllocMode_6 |
    C_apply_90 | C_arr_98 | C_fold'45'ir_102 T_AllocMode_6 |
    C_unfold'45'ir_106 |
    C_free'45'heap_108 MAlonzo.Code.Once.CCC.SlotMachine.T_HeapRef_10 |
    C_Prim_114 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.CCC.IR.IsPrimitive
d_IsPrimitive_116 a0 = ()
data T_IsPrimitive_116
  = C_is'45'unit_118 | C_is'45'int_120 | C_is'45'float_122 |
    C_is'45'str_124 | C_is'45'buffer_126
-- Once.CCC.IR.PrimContractV3
d_PrimContractV3_132 a0 a1 = ()
data T_PrimContractV3_132
  = C_constructor_150 Integer T_AllocMode_6
                      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.IR.PrimContractV3.stack-requirement
d_stack'45'requirement_144 :: T_PrimContractV3_132 -> Integer
d_stack'45'requirement_144 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.PrimContractV3.output-mode
d_output'45'mode_146 :: T_PrimContractV3_132 -> T_AllocMode_6
d_output'45'mode_146 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.PrimContractV3.stack-req-bounded
d_stack'45'req'45'bounded_148 ::
  T_PrimContractV3_132 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'45'req'45'bounded_148 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.PrimSem
d_PrimSem_152 = ()
newtype T_PrimSem_152
  = C_constructor_166 (MAlonzo.Code.Once.Type.T_Type_32 ->
                       MAlonzo.Code.Once.Type.T_Type_32 ->
                       MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny)
-- Once.CCC.IR.PrimSem.evalPrim
d_evalPrim_164 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_evalPrim_164 v0
  = case coe v0 of
      C_constructor_166 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.eval
d_eval_172 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T_IR_12 -> AgdaAny -> AgdaAny
d_eval_172 v0 v1 v2 v3 v4
  = case coe v3 of
      C_id_16 -> coe v4
      C__'8728'__24 v6 v8 v9
        -> coe
             d_eval_172 (coe v0) (coe v6) (coe v2) (coe v8)
             (coe d_eval_172 (coe v0) (coe v1) (coe v6) (coe v9) (coe v4))
      C_'10216'_'44'_'10217'__32 v8 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__38 v11 v12
               -> coe
                    MAlonzo.Code.Once.CCC.Target.X86v3.Types.du_pair_86
                    (coe d_eval_172 (coe v0) (coe v1) (coe v11) (coe v8) (coe v4))
                    (coe d_eval_172 (coe v0) (coe v1) (coe v12) (coe v9) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fst'45'ir_38
        -> coe MAlonzo.Code.Once.CCC.Target.X86v3.Types.du_fst_74 (coe v4)
      C_snd'45'ir_44
        -> coe MAlonzo.Code.Once.CCC.Target.X86v3.Types.du_snd_80 (coe v4)
      C_inl'45'ir_50 v7
        -> coe MAlonzo.Code.Once.CCC.Target.X86v3.Types.du_inl_96 v4
      C_inr'45'ir_56 v7
        -> coe MAlonzo.Code.Once.CCC.Target.X86v3.Types.du_inr_102 v4
      C_case'45'ir_64 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__40 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.Target.X86v3.Types.du_case_110
                    (coe d_eval_172 (coe v0) (coe v10) (coe v2) (coe v8))
                    (coe d_eval_172 (coe v0) (coe v11) (coe v2) (coe v9)) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_terminal_68 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      C_curry_82 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v11 v12 v13
               -> coe
                    (\ v14 ->
                       d_eval_172
                         (coe v0)
                         (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v1) (coe v11))
                         (coe v13) (coe v9)
                         (coe
                            MAlonzo.Code.Once.CCC.Target.X86v3.Types.du_pair_86 (coe v4)
                            (coe v14)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apply_90
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9 -> coe v8 v9
             _ -> MAlonzo.RTE.mazUnreachableError
      C_arr_98 -> coe v4
      C_fold'45'ir_102 v6
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86v3.Types.du_fold_126 (coe v4)
      C_unfold'45'ir_106
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86v3.Types.du_unfold_132 (coe v4)
      C_free'45'heap_108 v5 -> coe v4
      C_Prim_114 v7 -> coe d_evalPrim_164 v0 v1 v2 v7 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.eval-id
d_eval'45'id_266 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'id_266 = erased
-- Once.CCC.IR.eval-fst
d_eval'45'fst_280 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'fst_280 = erased
-- Once.CCC.IR.eval-snd
d_eval'45'snd_294 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'snd_294 = erased
-- Once.CCC.IR.eval-compose
d_eval'45'compose_314 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 ->
  T_IR_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'compose_314 = erased
-- Once.CCC.IR.eval-pair
d_eval'45'pair_340 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 ->
  T_IR_12 ->
  T_AllocMode_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'pair_340 = erased
-- Once.CCC.IR.eval-terminal
d_eval'45'terminal_358 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'terminal_358 = erased
-- Once.CCC.IR.alloc-mode-independent-pair
d_alloc'45'mode'45'independent'45'pair_382 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 ->
  T_IR_12 ->
  T_AllocMode_6 ->
  T_AllocMode_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'mode'45'independent'45'pair_382 = erased
-- Once.CCC.IR.alloc-mode-independent-inl
d_alloc'45'mode'45'independent'45'inl_408 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_AllocMode_6 ->
  T_AllocMode_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'mode'45'independent'45'inl_408 = erased
-- Once.CCC.IR.alloc-mode-independent-inr
d_alloc'45'mode'45'independent'45'inr_430 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_AllocMode_6 ->
  T_AllocMode_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'mode'45'independent'45'inr_430 = erased
-- Once.CCC.IR.alloc-mode-independent-curry
d_alloc'45'mode'45'independent'45'curry_458 ::
  T_PrimSem_152 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  T_IR_12 ->
  T_AllocMode_6 ->
  T_AllocMode_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'mode'45'independent'45'curry_458 = erased
-- Once.CCC.IR.pair-slots
d_pair'45'slots_470 :: Integer
d_pair'45'slots_470 = coe (2 :: Integer)
-- Once.CCC.IR.closure-slots
d_closure'45'slots_472 :: Integer
d_closure'45'slots_472 = coe (2 :: Integer)
-- Once.CCC.IR.ir-size
d_ir'45'size_478 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T_IR_12 -> Integer
d_ir'45'size_478 v0 v1 v2
  = case coe v2 of
      C_id_16 -> coe (1 :: Integer)
      C__'8728'__24 v4 v6 v7
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer))
                (coe d_ir'45'size_478 (coe v0) (coe v4) (coe v7)))
             (coe d_ir'45'size_478 (coe v4) (coe v1) (coe v6))
      C_'10216'_'44'_'10217'__32 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size_478 (coe v0) (coe v9) (coe v6)))
                    (coe d_ir'45'size_478 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fst'45'ir_38 -> coe (1 :: Integer)
      C_snd'45'ir_44 -> coe (1 :: Integer)
      C_inl'45'ir_50 v5 -> coe (1 :: Integer)
      C_inr'45'ir_56 v5 -> coe (1 :: Integer)
      C_case'45'ir_64 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe d_ir'45'size_478 (coe v8) (coe v1) (coe v6)))
                    (coe d_ir'45'size_478 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_terminal_68 -> coe (1 :: Integer)
      C_initial_72 -> coe (1 :: Integer)
      C_curry_82 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       d_ir'45'size_478
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                       (coe v11) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apply_90 -> coe (1 :: Integer)
      C_arr_98 -> coe (1 :: Integer)
      C_fold'45'ir_102 v4 -> coe (1 :: Integer)
      C_unfold'45'ir_106 -> coe (1 :: Integer)
      C_free'45'heap_108 v3 -> coe (1 :: Integer)
      C_Prim_114 v5 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.∘-f-smaller
d_'8728''45'f'45'smaller_504 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8728''45'f'45'smaller_504 v0 v1 ~v2 v3 ~v4
  = du_'8728''45'f'45'smaller_504 v0 v1 v3
du_'8728''45'f'45'smaller_504 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8728''45'f'45'smaller_504 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'n'43'm_3748
      (coe d_ir'45'size_478 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.CCC.IR.∘-g-smaller
d_'8728''45'g'45'smaller_520 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8728''45'g'45'smaller_520 ~v0 v1 v2 ~v3 v4
  = du_'8728''45'g'45'smaller_520 v1 v2 v4
du_'8728''45'g'45'smaller_520 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8728''45'g'45'smaller_520 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_478 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.IR.⟨,⟩-f-smaller
d_'10216''44''10217''45'f'45'smaller_542 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 ->
  T_IR_12 ->
  T_AllocMode_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'f'45'smaller_542 v0 v1 ~v2 v3 ~v4 ~v5
  = du_'10216''44''10217''45'f'45'smaller_542 v0 v1 v3
du_'10216''44''10217''45'f'45'smaller_542 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'f'45'smaller_542 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_478 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.IR.⟨,⟩-g-smaller
d_'10216''44''10217''45'g'45'smaller_566 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 ->
  T_IR_12 ->
  T_AllocMode_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'g'45'smaller_566 v0 ~v1 v2 ~v3 v4 ~v5
  = du_'10216''44''10217''45'g'45'smaller_566 v0 v2 v4
du_'10216''44''10217''45'g'45'smaller_566 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'g'45'smaller_566 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe d_ir'45'size_478 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.IR.curry-smaller
d_curry'45'smaller_590 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  T_IR_12 ->
  T_AllocMode_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_curry'45'smaller_590 v0 v1 v2 ~v3 v4 ~v5
  = du_curry'45'smaller_590 v0 v1 v2 v4
du_curry'45'smaller_590 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_curry'45'smaller_590 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
      (coe
         d_ir'45'size_478
         (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v1)) (coe v2)
         (coe v3))
-- Once.CCC.IR.case-f-smaller
d_case'45'f'45'smaller_610 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_case'45'f'45'smaller_610 v0 ~v1 v2 v3 ~v4
  = du_case'45'f'45'smaller_610 v0 v2 v3
du_case'45'f'45'smaller_610 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_case'45'f'45'smaller_610 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe d_ir'45'size_478 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.IR.case-g-smaller
d_case'45'g'45'smaller_630 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_case'45'g'45'smaller_630 ~v0 v1 v2 ~v3 v4
  = du_case'45'g'45'smaller_630 v1 v2 v4
du_case'45'g'45'smaller_630 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_case'45'g'45'smaller_630 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe d_ir'45'size_478 (coe v0) (coe v1) (coe v2)))
-- Once.CCC.IR.ir-stack-requirement
d_ir'45'stack'45'requirement_644 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T_IR_12 -> Integer
d_ir'45'stack'45'requirement_644 v0 v1 v2
  = case coe v2 of
      C_id_16 -> coe (0 :: Integer)
      C__'8728'__24 v4 v6 v7
        -> coe
             addInt
             (coe d_ir'45'stack'45'requirement_644 (coe v0) (coe v4) (coe v7))
             (coe d_ir'45'stack'45'requirement_644 (coe v4) (coe v1) (coe v6))
      C_'10216'_'44'_'10217'__32 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe d_ir'45'stack'45'requirement_644 (coe v0) (coe v9) (coe v6))
                       (coe d_ir'45'stack'45'requirement_644 (coe v0) (coe v10) (coe v7)))
                    (coe d_pair'45'slots_470)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fst'45'ir_38 -> coe (0 :: Integer)
      C_snd'45'ir_44 -> coe (0 :: Integer)
      C_inl'45'ir_50 v5 -> coe d_pair'45'slots_470
      C_inr'45'ir_56 v5 -> coe d_pair'45'slots_470
      C_case'45'ir_64 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    addInt
                    (coe d_ir'45'stack'45'requirement_644 (coe v8) (coe v1) (coe v6))
                    (coe d_ir'45'stack'45'requirement_644 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_terminal_68 -> coe (0 :: Integer)
      C_initial_72 -> coe (0 :: Integer)
      C_curry_82 v7 v8 -> coe d_pair'45'slots_470
      C_apply_90 -> coe d_pair'45'slots_470
      C_arr_98 -> coe (0 :: Integer)
      C_fold'45'ir_102 v4 -> coe (1 :: Integer)
      C_unfold'45'ir_106 -> coe (0 :: Integer)
      C_free'45'heap_108 v3 -> coe (0 :: Integer)
      C_Prim_114 v5 -> coe d_pair'45'slots_470
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.∘-stack-req
d_'8728''45'stack'45'req_668 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 ->
  T_IR_12 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8728''45'stack'45'req_668 = erased
-- Once.CCC.IR.⟨,⟩-stack-req
d_'10216''44''10217''45'stack'45'req_686 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 ->
  T_IR_12 ->
  T_AllocMode_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10216''44''10217''45'stack'45'req_686 = erased
-- Once.CCC.IR.⟨,⟩-capacity-for-pair
d_'10216''44''10217''45'capacity'45'for'45'pair_710 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 ->
  T_IR_12 ->
  T_AllocMode_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'capacity'45'for'45'pair_710 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 ~v5 ~v6 ~v7 v8
  = du_'10216''44''10217''45'capacity'45'for'45'pair_710 v8
du_'10216''44''10217''45'capacity'45'for'45'pair_710 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'capacity'45'for'45'pair_710 v0 = coe v0
-- Once.CCC.IR.ir-req-≤-pair-slots*size
d_ir'45'req'45''8804''45'pair'45'slots'42'size_748 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  T_IR_12 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ir'45'req'45''8804''45'pair'45'slots'42'size_748 v0 v1 v2
  = case coe v2 of
      C_id_16 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      C__'8728'__24 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
                (coe
                   mulInt (coe d_pair'45'slots_470)
                   (coe d_ir'45'size_478 (coe v4) (coe v1) (coe v6)))
                (coe
                   d_ir'45'req'45''8804''45'pair'45'slots'42'size_748 (coe v0)
                   (coe v4) (coe v7))
                (coe
                   d_ir'45'req'45''8804''45'pair'45'slots'42'size_748 (coe v4)
                   (coe v1) (coe v6)))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                d_pair'45'slots_470
                (addInt
                   (coe d_ir'45'size_478 (coe v0) (coe v4) (coe v7))
                   (coe d_ir'45'size_478 (coe v4) (coe v1) (coe v6)))
                (addInt
                   (coe
                      addInt (coe (1 :: Integer))
                      (coe d_ir'45'size_478 (coe v0) (coe v4) (coe v7)))
                   (coe d_ir'45'size_478 (coe v4) (coe v1) (coe v6)))
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                   (coe
                      addInt (coe d_ir'45'size_478 (coe v0) (coe v4) (coe v7))
                      (coe d_ir'45'size_478 (coe v4) (coe v1) (coe v6)))))
      C_'10216'_'44'_'10217'__32 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'737''45''8804'_3682
                    d_pair'45'slots_470
                    (addInt
                       (coe d_ir'45'stack'45'requirement_644 (coe v0) (coe v9) (coe v6))
                       (coe d_ir'45'stack'45'requirement_644 (coe v0) (coe v10) (coe v7)))
                    (mulInt
                       (coe d_pair'45'slots_470)
                       (coe
                          addInt (coe d_ir'45'size_478 (coe v0) (coe v9) (coe v6))
                          (coe d_ir'45'size_478 (coe v0) (coe v10) (coe v7))))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
                       (coe
                          mulInt (coe d_pair'45'slots_470)
                          (coe d_ir'45'size_478 (coe v0) (coe v10) (coe v7)))
                       (coe
                          d_ir'45'req'45''8804''45'pair'45'slots'42'size_748 (coe v0)
                          (coe v9) (coe v6))
                       (coe
                          d_ir'45'req'45''8804''45'pair'45'slots'42'size_748 (coe v0)
                          (coe v10) (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fst'45'ir_38 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      C_snd'45'ir_44 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      C_inl'45'ir_50 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__40 v6 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe
                       d_ir'45'stack'45'requirement_644 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v0) (coe v7))
                       (coe C_inl'45'ir_50 v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_inr'45'ir_56 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__40 v6 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe
                       d_ir'45'stack'45'requirement_644 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v6) (coe v0))
                       (coe C_inr'45'ir_56 v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_case'45'ir_64 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
                       (coe
                          mulInt (coe d_pair'45'slots_470)
                          (coe d_ir'45'size_478 (coe v9) (coe v1) (coe v7)))
                       (coe
                          d_ir'45'req'45''8804''45'pair'45'slots'42'size_748 (coe v8)
                          (coe v1) (coe v6))
                       (coe
                          d_ir'45'req'45''8804''45'pair'45'slots'42'size_748 (coe v9)
                          (coe v1) (coe v7)))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                       d_pair'45'slots_470
                       (addInt
                          (coe d_ir'45'size_478 (coe v8) (coe v1) (coe v6))
                          (coe d_ir'45'size_478 (coe v9) (coe v1) (coe v7)))
                       (addInt
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe d_ir'45'size_478 (coe v8) (coe v1) (coe v6)))
                          (coe d_ir'45'size_478 (coe v9) (coe v1) (coe v7)))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                          (coe
                             addInt (coe d_ir'45'size_478 (coe v8) (coe v1) (coe v6))
                             (coe d_ir'45'size_478 (coe v9) (coe v1) (coe v7)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_terminal_68 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      C_initial_72 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      C_curry_82 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      C_apply_90
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__38 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v8 v9 v10
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                           (coe
                              d_ir'45'stack'45'requirement_644
                              (coe
                                 MAlonzo.Code.Once.Type.C__'42'__38
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 (coe v8) (coe v9)
                                    (coe v1))
                                 (coe v8))
                              (coe v1) (coe C_apply_90))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_arr_98 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      C_fold'45'ir_102 v4
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      C_unfold'45'ir_106 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      C_free'45'heap_108 v3
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      C_Prim_114 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe
                d_ir'45'stack'45'requirement_644 (coe v0) (coe v1)
                (coe C_Prim_114 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.adaptAllocMode
d_adaptAllocMode_834 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> T_AllocMode_6
d_adaptAllocMode_834 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_Stack_6 -> coe C_Stack_8
      MAlonzo.Code.Once.IR.C_Heap_8 -> coe C_Heap_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.fromOnceIR
d_fromOnceIR_840 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> T_IR_12
d_fromOnceIR_840 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_14 -> coe C_id_16
      MAlonzo.Code.Once.IR.C__'8728'__22 v4 v6 v7
        -> coe
             C__'8728'__24 v4 (d_fromOnceIR_840 (coe v4) (coe v1) (coe v6))
             (d_fromOnceIR_840 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_fst_28 -> coe C_fst'45'ir_38
      MAlonzo.Code.Once.IR.C_snd_34 -> coe C_snd'45'ir_44
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    C_'10216'_'44'_'10217'__32
                    (d_fromOnceIR_840 (coe v0) (coe v9) (coe v6))
                    (d_fromOnceIR_840 (coe v0) (coe v10) (coe v7))
                    (d_adaptAllocMode_834 (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v5
        -> coe C_inl'45'ir_50 (d_adaptAllocMode_834 (coe v5))
      MAlonzo.Code.Once.IR.C_inr_54 v5
        -> coe C_inr'45'ir_56 (d_adaptAllocMode_834 (coe v5))
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    C_case'45'ir_64 (d_fromOnceIR_840 (coe v8) (coe v1) (coe v6))
                    (d_fromOnceIR_840 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66 -> coe C_terminal_68
      MAlonzo.Code.Once.IR.C_initial_70 -> coe C_initial_72
      MAlonzo.Code.Once.IR.C_curry_80 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> coe
                    C_curry_82
                    (d_fromOnceIR_840
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                       (coe v11) (coe v7))
                    (d_adaptAllocMode_834 (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_88 -> coe C_apply_90
      MAlonzo.Code.Once.IR.C_fold_92
        -> coe C_fold'45'ir_102 (coe C_Heap_10)
      MAlonzo.Code.Once.IR.C_unfold_96 -> coe C_unfold'45'ir_106
      MAlonzo.Code.Once.IR.C_arr_102 -> coe C_arr_98
      MAlonzo.Code.Once.IR.C_Prim_108 v5 -> coe C_Prim_114 v5
      _ -> MAlonzo.RTE.mazUnreachableError
