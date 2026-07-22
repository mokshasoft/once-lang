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

module MAlonzo.Code.Once.Arith.Backend.PreserveCore where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax

-- Once.Arith.Backend.PreserveCore.PreservesCCC-rf
d_PreservesCCC'45'rf_46 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [AgdaAny]) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  (AgdaAny -> AgdaAny) -> ()
d_PreservesCCC'45'rf_46 = erased
-- Once.Arith.Backend.PreserveCore.runFns
d_runFns_52 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [AgdaAny]) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  [AgdaAny -> AgdaAny] -> AgdaAny -> AgdaAny
d_runFns_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
  = du_runFns_52 v11 v12
du_runFns_52 :: [AgdaAny -> AgdaAny] -> AgdaAny -> AgdaAny
du_runFns_52 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3 -> coe du_runFns_52 (coe v3) (coe v2 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.PreserveCore.preserves-runFns
d_preserves'45'runFns_64 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [AgdaAny]) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  [AgdaAny -> AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_preserves'45'runFns_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10
                         v11 v12 v13
  = du_preserves'45'runFns_64 v6 v7 v11 v12 v13
du_preserves'45'runFns_64 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny -> AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_preserves'45'runFns_64 v0 v1 v2 v3 v4
  = case coe v2 of
      [] -> coe v0 v4
      (:) v5 v6
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v9 v10
               -> coe
                    v1 v4 (coe v5 v4) (coe du_runFns_52 (coe v6) (coe v5 v4))
                    (coe v9 v4)
                    (coe
                       du_preserves'45'runFns_64 (coe v0) (coe v1) (coe v6) (coe v10)
                       (coe v5 v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.PreserveCore.write-regs
d_write'45'regs_78 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [AgdaAny]) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
d_write'45'regs_78 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                   v12
  = du_write'45'regs_78 v3 v11 v12
du_write'45'regs_78 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_write'45'regs_78 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe du_write'45'regs_78 (coe v0) (coe v4) (coe v0 v2 v5 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.PreserveCore.write-regs-preserves
d_write'45'regs'45'preserves_94 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [AgdaAny]) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_write'45'regs'45'preserves_94 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 ~v9
                                ~v10 v11 v12 v13
  = du_write'45'regs'45'preserves_94 v3 v6 v7 v8 v11 v12 v13
du_write'45'regs'45'preserves_94 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_write'45'regs'45'preserves_94 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      [] -> coe v1 v6
      (:) v7 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> case coe v5 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v13 v14
                      -> coe
                           v2 v6 (coe v0 v6 v9 v10)
                           (coe du_write'45'regs_78 (coe v0) (coe v8) (coe v0 v6 v9 v10))
                           (coe v3 v6 v9 v10 v13)
                           (coe
                              du_write'45'regs'45'preserves_94 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v8) (coe v14) (coe v0 v6 v9 v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.PreserveCore.step-of
d_step'45'of_110 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [AgdaAny]) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_step'45'of_110 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 v11 v12
  = du_step'45'of_110 v3 v9 v11 v12
du_step'45'of_110 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [AgdaAny]) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_step'45'of_110 v0 v1 v2 v3
  = coe
      du_write'45'regs_78 (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v3 v4)))
         (coe v1 v2))
-- Once.Arith.Backend.PreserveCore.step-of-preserves
d_step'45'of'45'preserves_122 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [AgdaAny]) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_step'45'of'45'preserves_122 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9
                              v10 v11 v12
  = du_step'45'of'45'preserves_122 v3 v6 v7 v8 v9 v10 v11 v12
du_step'45'of'45'preserves_122 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   [AgdaAny]) ->
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_step'45'of'45'preserves_122 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_write'45'regs'45'preserves_94 (coe v0) (coe v1) (coe v2)
      (coe v3)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v8 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) (coe v7 v8)))
         (coe v4 v6))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_map'8314'_496
         (coe v4 v6) (coe v5 v6))
