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

module MAlonzo.Code.Once.Arith.Backend.MemEffectCore where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax

-- Once.Arith.Backend.MemEffectCore.mem-effect
d_mem'45'effect_60 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Integer -> AgdaAny) ->
  (Integer -> AgdaAny -> AgdaAny -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   Integer ->
   Integer ->
   Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   ()) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny -> AgdaAny
d_mem'45'effect_60 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 v12
                   ~v13 ~v14 ~v15 v16 v17
  = du_mem'45'effect_60 v4 v5 v6 v7 v11 v12 v16 v17
du_mem'45'effect_60 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny -> AgdaAny
du_mem'45'effect_60 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8 = coe v0 v7 in
    coe
      (case coe v6 of
         MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v9 v10
           -> coe
                v3 (coe v0 v7) (coe v5 v7 v9) (coe v2 (coe v1 v7) (coe v4 v10))
         _ -> coe v8)
-- Once.Arith.Backend.MemEffectCore.mem-preserves
d_mem'45'preserves_76 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Integer -> AgdaAny) ->
  (Integer -> AgdaAny -> AgdaAny -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   Integer ->
   Integer ->
   Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny -> Integer) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   ()) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_mem'45'preserves_76 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 v10 v11
                      v12 ~v13 ~v14 v15 v16 v17 v18 v19 v20 v21
  = du_mem'45'preserves_76
      v4 v5 v6 v9 v10 v11 v12 v15 v16 v17 v18 v19 v20 v21
du_mem'45'preserves_76 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (Integer -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   Integer ->
   Integer ->
   Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   Integer) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
   MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_mem'45'preserves_76 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13
  = case coe v8 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v14 v15
        -> coe
             v4 (coe v0 v9) v10 (coe v6 v9 v14)
             (coe v2 (coe v1 v9) (coe v5 v15))
             (coe v7 v9 v14 v15 v10 v11 v12 v13)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v14
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v14 v15 v16
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v14 v15 v16
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v14 v15 v16
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v14 v15 v16
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v14 v15 v16
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v14 v15 v16
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_56 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_58 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_60 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_62 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_64 v14
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_66 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_68 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_70 v14 v15
        -> coe v3 v10 (coe v0 v9)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_72 v14
        -> coe v3 v10 (coe v0 v9)
      _ -> MAlonzo.RTE.mazUnreachableError
