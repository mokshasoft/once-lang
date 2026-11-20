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

module MAlonzo.Code.Once.Measure where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.RoomChecks
import qualified MAlonzo.Code.Once.CompileSrc
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.LinCore.ExprBuild
import qualified MAlonzo.Code.Once.LinCore.ExprImage
import qualified MAlonzo.Code.Once.Measure.Image
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Measure.at
d_at_6 ::
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_at_6 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Once.Measure.Image.d_show'45'stats_106
                       (coe
                          MAlonzo.Code.Once.Measure.Image.d_image'45'stats_104
                          (MAlonzo.Code.Once.CCC.Codegen.RoomChecks.d_room'45'checks_84
                             (coe
                                MAlonzo.Code.Once.LinCore.ExprImage.d_imageAt_10
                                (coe
                                   MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62
                                   (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8))
                                (coe
                                   MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1482 (coe v0)
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe v3) (coe v4)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Once.Measure.Image.d_show'45'stats_106
                (coe
                   MAlonzo.Code.Once.Measure.Image.d_image'45'stats_104
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.stats-src
d_stats'45'src_16 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stats'45'src_16 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             d_at_6 (coe v1)
             (coe MAlonzo.Code.Once.CompileSrc.d_mainOf_1810 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.statsOf
d_statsOf_22 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_statsOf_22 ~v0 v1 = du_statsOf_22 v1
du_statsOf_22 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_statsOf_22 v0
  = coe
      d_stats'45'src_16
      (coe
         MAlonzo.Code.Once.CompileSrc.d_srcModule_1760
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
