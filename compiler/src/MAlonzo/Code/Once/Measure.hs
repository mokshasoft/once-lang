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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Measure.Image
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax

-- Once.Measure.statsOf
d_statsOf_4 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_statsOf_4 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_1038
              (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v0)
              (coe
                 MAlonzo.Code.Once.Parser.d_guardDistinct_488
                 (coe
                    MAlonzo.Code.Once.Parser.d_thenExtract_578
                    (coe
                       MAlonzo.Code.Once.Parser.d_sigsAdjacent_500
                       (coe
                          MAlonzo.Code.Once.Spec.Surface.Syntax.d_decls_126
                          (coe MAlonzo.Code.Once.Parser.Module.Core.d_rmodule_14 (coe v1)))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                    (coe
                       MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_196
                       (coe
                          MAlonzo.Code.Once.Parser.d_sigsFirst_572
                          (coe
                             MAlonzo.Code.Once.Spec.Surface.Syntax.d_decls_126
                             (coe MAlonzo.Code.Once.Parser.Module.Core.d_rmodule_14 (coe v1)))
                          (coe MAlonzo.Code.Once.Parser.Module.Core.d_imported_16 (coe v1)))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> let v4 = MAlonzo.Code.Once.Compile.d_findMain_1250 (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                          (coe
                             MAlonzo.Code.Once.Measure.Image.d_show'45'stats_106
                             (coe
                                MAlonzo.Code.Once.Measure.Image.d_image'45'stats_104
                                (MAlonzo.Code.Once.Compile.d_image'45'of_1390
                                   (coe
                                      MAlonzo.Code.Once.Denotation.Program.C_irProgram_662
                                      (coe MAlonzo.Code.Once.Compile.d_tableOf_1284 (coe v3))
                                      (coe v5)))))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                          (coe
                             MAlonzo.Code.Once.Measure.Image.d_show'45'stats_106
                             (coe
                                MAlonzo.Code.Once.Measure.Image.d_image'45'stats_104
                                (MAlonzo.Code.Once.Compile.d_lib'45'image_1434
                                   (coe MAlonzo.Code.Once.Compile.d_tableOf_1284 (coe v3)))))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
