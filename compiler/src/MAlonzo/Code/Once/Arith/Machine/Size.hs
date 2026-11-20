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

module MAlonzo.Code.Once.Arith.Machine.Size where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Arith.Machine.Size.sz
d_sz_12 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_sz_12 ~v0 v1 v2 = du_sz_12 v1 v2
du_sz_12 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_sz_12 v0 v1
  = let v2 = 1 :: Integer in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
           -> coe
                addInt
                (coe
                   addInt
                   (coe addInt (coe (1 :: Integer)) (coe du_sz_12 (coe v0) (coe v6)))
                   (coe du_sz_12 (coe v0) (coe v6)))
                (coe du_sz_12 (coe v4) (coe v7))
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
                  -> coe
                       addInt
                       (coe addInt (coe (1 :: Integer)) (coe du_sz_12 (coe v8) (coe v6)))
                       (coe du_sz_12 (coe v9) (coe v7))
                _ -> coe v2
         _ -> coe v2)
-- Once.Arith.Machine.Size.reassoc-<
d_reassoc'45''60'_36 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reassoc'45''60'_36 ~v0 v1 v2 v3 v4 v5 v6
  = du_reassoc'45''60'_36 v1 v2 v3 v4 v5 v6
du_reassoc'45''60'_36 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_reassoc'45''60'_36 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            du_bound_54 (coe du_sz_12 (coe v2) (coe v3))
            (coe du_sz_12 (coe v1) (coe v4)) (coe du_sz_12 (coe v0) (coe v5))))
-- Once.Arith.Machine.Size._.bound
d_bound_54 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_bound_54 v7 v8 v9
du_bound_54 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound_54 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt
               (coe
                  addInt
                  (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v0))
                  (coe v1))
               (coe v1))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe du_step_88 (coe v0) (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               addInt
               (coe
                  addInt
                  (coe
                     addInt
                     (coe
                        addInt
                        (coe
                           addInt
                           (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v0))
                           (coe v0))
                        (coe v0))
                     (coe v1))
                  (coe v1))
               (coe v2))))
-- Once.Arith.Machine.Size._._.lhs≡
d_lhs'8801'_72 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lhs'8801'_72 = erased
-- Once.Arith.Machine.Size._._.rhs≡
d_rhs'8801'_80 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rhs'8801'_80 = erased
-- Once.Arith.Machine.Size._._.step
d_step_88 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_step_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_step_88 v10 v11 v12
du_step_88 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_step_88 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               addInt
               (coe
                  addInt (coe addInt (coe addInt (coe v0) (coe v0)) (coe v1))
                  (coe v1))
               (coe v2)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               addInt
               (coe
                  addInt
                  (coe
                     addInt
                     (coe
                        addInt (coe addInt (coe addInt (coe v0) (coe v0)) (coe v0))
                        (coe v0))
                     (coe v1))
                  (coe v1))
               (coe v2))))
-- Once.Arith.Machine.Size.sz-sigop
d_sz'45'sigop_106 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'sigop_106 v0 ~v1 ~v2 ~v3 v4 = du_sz'45'sigop_106 v0 v4
du_sz'45'sigop_106 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'sigop_106 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               du_sz_12
               (coe
                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe (0 :: Integer))
                  (coe v0))
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               addInt (coe (1 :: Integer))
               (coe
                  du_sz_12
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe (0 :: Integer))
                     (coe v0))
                  (coe v1)))))
-- Once.Arith.Machine.Size.sz-pairˡ
d_sz'45'pair'737'_122 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'pair'737'_122 ~v0 v1 ~v2 v3 ~v4
  = du_sz'45'pair'737'_122 v1 v3
du_sz'45'pair'737'_122 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'pair'737'_122 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe du_sz_12 (coe v0) (coe v1)))
-- Once.Arith.Machine.Size.sz-pairʳ
d_sz'45'pair'691'_138 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'pair'691'_138 ~v0 ~v1 v2 ~v3 v4
  = du_sz'45'pair'691'_138 v2 v4
du_sz'45'pair'691'_138 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'pair'691'_138 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe du_sz_12 (coe v0) (coe v1)))
-- Once.Arith.Machine.Size.sz-distˡ
d_sz'45'dist'737'_158 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'dist'737'_158 v0 v1 v2 ~v3 v4 v5 v6
  = du_sz'45'dist'737'_158 v0 v1 v2 v4 v5 v6
du_sz'45'dist'737'_158 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'dist'737'_158 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            du_go_184 (coe du_sz_12 (coe v1) (coe v3))
            (coe du_sz_12 (coe v2) (coe v4)) (coe du_sz_12 (coe v0) (coe v5))))
-- Once.Arith.Machine.Size._.e
d_e_176 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e_176 = erased
-- Once.Arith.Machine.Size._.go
d_go_184 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_go_184 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 = du_go_184 v7 v8 v9
du_go_184 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_go_184 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe addInt (coe addInt (coe v0) (coe v0)) (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt
               (coe
                  addInt
                  (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v0))
                  (coe v1))
               (coe v1))
            (coe v2)))
-- Once.Arith.Machine.Size.sz-distʳ
d_sz'45'dist'691'_206 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'dist'691'_206 v0 v1 v2 ~v3 v4 v5 v6
  = du_sz'45'dist'691'_206 v0 v1 v2 v4 v5 v6
du_sz'45'dist'691'_206 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'dist'691'_206 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            du_go_232 (coe du_sz_12 (coe v1) (coe v3))
            (coe du_sz_12 (coe v2) (coe v4)) (coe du_sz_12 (coe v0) (coe v5))))
-- Once.Arith.Machine.Size._.e
d_e_224 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e_224 = erased
-- Once.Arith.Machine.Size._.go
d_go_232 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_go_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 = du_go_232 v7 v8 v9
du_go_232 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_go_232 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe addInt (coe addInt (coe v1) (coe v1)) (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt
               (coe
                  addInt
                  (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v0))
                  (coe v1))
               (coe v1))
            (coe v2)))
