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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Memory.Memory

-- Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.plg
d_plg_26 ::
  (Integer -> ()) ->
  (Integer -> ()) ->
  ((Integer -> Maybe Integer) ->
   Integer ->
   Integer ->
   Integer ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Maybe Integer -> Integer) ->
  (MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 -> Integer) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
d_plg_26 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 = du_plg_26 v3 v4 v5 v6 v7
du_plg_26 ::
  (Maybe Integer -> Integer) ->
  (MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 -> Integer) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] -> Integer
du_plg_26 v0 v1 v2 v3 v4
  = case coe v4 of
      []
        -> coe
             v0 (MAlonzo.Code.Once.Memory.Memory.d_readMem_88 (coe v2) (coe v3))
      (:) v5 v6
        -> coe
             du_plg_26 (coe v0) (coe v1) (coe v2)
             (coe
                v0
                (MAlonzo.Code.Once.Memory.Memory.d_readMem_88
                   (coe v2) (coe addInt (coe v1 v5) (coe v3))))
             (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.HeapChase
d_HeapChase_42 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_HeapChase_42
  = C_hc'45''91''93'_48 AgdaAny |
    C_hc'45''8759'_56 AgdaAny T_HeapChase_42
-- Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.plg-stack-write-invisible
d_plg'45'stack'45'write'45'invisible_68 ::
  (Integer -> ()) ->
  (Integer -> ()) ->
  ((Integer -> Maybe Integer) ->
   Integer ->
   Integer ->
   Integer ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Maybe Integer -> Integer) ->
  (MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 -> Integer) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  AgdaAny ->
  T_HeapChase_42 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'stack'45'write'45'invisible_68 = erased
-- Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion.heapchase-agree
d_heapchase'45'agree_112 ::
  (Integer -> ()) ->
  (Integer -> ()) ->
  ((Integer -> Maybe Integer) ->
   Integer ->
   Integer ->
   Integer ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Maybe Integer -> Integer) ->
  (MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22 -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_HeapChase_42 -> T_HeapChase_42
d_heapchase'45'agree_112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 v10
  = du_heapchase'45'agree_112 v8 v10
du_heapchase'45'agree_112 ::
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  T_HeapChase_42 -> T_HeapChase_42
du_heapchase'45'agree_112 v0 v1
  = case coe v0 of
      []
        -> case coe v1 of
             C_hc'45''91''93'_48 v3 -> coe C_hc'45''91''93'_48 v3
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v2 v3
        -> case coe v1 of
             C_hc'45''8759'_56 v7 v8
               -> coe
                    C_hc'45''8759'_56 v7
                    (coe du_heapchase'45'agree_112 (coe v3) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
