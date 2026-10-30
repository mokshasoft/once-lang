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

module MAlonzo.Code.Once.Inspect where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Show
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Name
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type

-- Once.Inspect.showFunInfo
d_showFunInfo_4 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfo_4 v0
  = let v1 = MAlonzo.Code.Once.Parser.d_funType_90 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_88 (coe v0))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" : " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Type.d_showType_36
                         (coe (0 :: Integer)) (coe v2))
                      ("\n" :: Data.Text.Text)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_88 (coe v0))
                (" : <inferred>\n" :: Data.Text.Text)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Inspect.showPolyFunInfo
d_showPolyFunInfo_18 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_98 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfo_18 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_pfunName_106 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (MAlonzo.Code.Once.Type.d_showPolyType_134
               (coe MAlonzo.Code.Once.Parser.d_pfunType_108 (coe v0)))
            ("\n" :: Data.Text.Text)))
-- Once.Inspect.showFuns
d_showFuns_22 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_78] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFuns_22 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showFunInfo_4 (coe v1)) (d_showFuns_22 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Inspect.showPolys
d_showPolys_28 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_98] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolys_28 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showPolyFunInfo_18 (coe v1)) (d_showPolys_28 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Inspect.showEntries
d_showEntries_34 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_showEntries_34 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFuns_22
                   (coe MAlonzo.Code.Once.Parser.d_funsOf_120 (coe v1)))
                (d_showPolys_28
                   (coe MAlonzo.Code.Once.Parser.d_polysOf_128 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Inspect.signatures
d_signatures_40 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_signatures_40 v0
  = coe
      d_showEntries_34
      (coe MAlonzo.Code.Once.Parser.d_extractFunctions_584 (coe v0))
-- Once.Inspect.accepted
d_accepted_44 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_accepted_44 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Inspect.check
d_check_48 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_check_48 v0
  = coe
      d_accepted_44
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_1034
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Inspect.showCompiledFun
d_showCompiledFun_52 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_538 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCompiledFun_52 v0
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
-- Once.Inspect.showCompiledFuns
d_showCompiledFuns_56 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_538] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCompiledFuns_56 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showCompiledFun_52 (coe v1)) (d_showCompiledFuns_56 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Inspect.showCompiled
d_showCompiled_62 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_showCompiled_62 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe d_showCompiledFuns_56 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Inspect.dumpIR
d_dumpIR_68 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dumpIR_68 v0 v1
  = coe
      d_showCompiled_62
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_1034
         (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v0) (coe v1))
