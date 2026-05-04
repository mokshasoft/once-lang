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

module MAlonzo.Code.Once.Compiler where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Verified
import qualified MAlonzo.Code.Once.Verified.Behavior
import qualified MAlonzo.Code.Once.Verified.CPU
import qualified MAlonzo.Code.Once.Verified.Compile

-- Once.Compiler.once-compiler
d_once'45'compiler_4 ::
  MAlonzo.Code.Once.Verified.T_CorrectCompiler_4
d_once'45'compiler_4
  = coe
      MAlonzo.Code.Once.Verified.C_constructor_50
      MAlonzo.Code.Once.Verified.Behavior.d_'10214'_'10215'_10
      MAlonzo.Code.Once.Verified.CPU.d_exec_8
      MAlonzo.Code.Once.Verified.Compile.d_compile_12
