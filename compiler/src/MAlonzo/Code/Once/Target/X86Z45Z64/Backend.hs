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

module MAlonzo.Code.Once.Target.X86Z45Z64.Backend where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File
import qualified MAlonzo.Code.Once.Target.Backend

-- Once.Target.X86-64.Backend.backend
d_backend_8 :: MAlonzo.Code.Once.Target.Backend.T_Backend_6
d_backend_8
  = coe
      MAlonzo.Code.Once.Target.Backend.C_constructor_36
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_print_84
      MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_block'45'payload_300
      (\ v0 v1 v2 ->
         coe
           MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.C_mkImage_30
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe
                 MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.du_compile'45'trace'45'cnt_82
                 (coe (0 :: Integer)) (coe v0)))
           (coe
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
           (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.C_mkImage_30
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
