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

module MAlonzo.Code.Once.Compile.Dump where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Show
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Name
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type

-- Once.Compile.Dump.showCompiledFun
d_showCompiledFun_6 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_538 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCompiledFun_6 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Name.d_showCanonical_4
         (coe MAlonzo.Code.Once.Compile.d_cfName_546 (coe v0)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (MAlonzo.Code.Once.Type.d_showType_36
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.Compile.d_cfType_548 (coe v0)))
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("\n  = " :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (MAlonzo.Code.Once.IR.Show.d_showIR_14
                     (coe
                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe (0 :: Integer))
                        (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                     (coe
                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe (0 :: Integer))
                        (coe MAlonzo.Code.Once.Compile.d_cfType_548 (coe v0)))
                     (coe MAlonzo.Code.Once.Compile.d_cfIR_550 (coe v0)))
                  ("\n" :: Data.Text.Text)))))
-- Once.Compile.Dump.showAll
d_showAll_10 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_538] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showAll_10 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showCompiledFun_6 (coe v1)) (d_showAll_10 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.Dump.dumpIR
d_dumpIR_16 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dumpIR_16 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_1016
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
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe d_showAll_10 (coe v3))
         _ -> MAlonzo.RTE.mazUnreachableError)
