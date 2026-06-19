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

module MAlonzo.Code.Once.CCC.Machine.IR.MuValidity where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.IR.MuValidity._.sem-CoIn
d_sem'45'CoIn_12 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_12
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoIn_1000
-- Once.CCC.Machine.IR.MuValidity._.sem-CoOut
d_sem'45'CoOut_14 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_14
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_990
-- Once.CCC.Machine.IR.MuValidity._.sem-In
d_sem'45'In_16 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_16
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_920
-- Once.CCC.Machine.IR.MuValidity._.sem-Out
d_sem'45'Out_18 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_18
  = coe MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_928
-- Once.CCC.Machine.IR.MuValidity._.⟦_⟧F
d_'10214'_'10215'F_20 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_20 = erased
-- Once.CCC.Machine.IR.MuValidity._.⟦μ⟧
d_'10214'μ'10215'_22 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_22 = erased
-- Once.CCC.Machine.IR.MuValidity._.⟦ν⟧
d_'10214'ν'10215'_24 :: MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_24 = erased
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl._.BeforeFrontier
d_BeforeFrontier_38 a0 a1 a2 a3 = ()
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl._.readLoc
d_readLoc_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_106 ~v0 ~v1 = du_readLoc_106
du_readLoc_106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_106
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_618
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μLayerValid
d_μLayerValid_172 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_μLayerValid_172
  = C_μlayer'45'K_196 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 |
    C_μlayer'45'Id_208 T_μValid_178 |
    C_μlayer'45'inl_230 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                        T_μLayerValid_172 |
    C_μlayer'45'inr_252 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                        T_μLayerValid_172 |
    C_μlayer'45'prod_278 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                         MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                         MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                         MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                         MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                         T_μLayerValid_172 T_μLayerValid_172
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μValid
d_μValid_178 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_μValid_178
  = C_μ'45'valid_292 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                     T_μLayerValid_172
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νLayerValid
d_νLayerValid_300 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_νLayerValid_300
  = C_νlayer'45'K_324 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 |
    C_νlayer'45'Id_336 T_νValid_306 |
    C_νlayer'45'inl_358 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                        T_νLayerValid_300 |
    C_νlayer'45'inr_380 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                        T_νLayerValid_300 |
    C_νlayer'45'prod_406 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                         MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                         MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                         MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                         MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                         T_νLayerValid_300 T_νLayerValid_300
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νValid
d_νValid_306 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_νValid_306
  = C_ν'45'valid_420 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
                     T_νLayerValid_300
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μLayerValid-mem-only
d_μLayerValid'45'mem'45'only_440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_μLayerValid_172 -> T_μLayerValid_172
d_μLayerValid'45'mem'45'only_440 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 ~v11 ~v12 v13
  = du_μLayerValid'45'mem'45'only_440
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v13
du_μLayerValid'45'mem'45'only_440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  T_μLayerValid_172 -> T_μLayerValid_172
du_μLayerValid'45'mem'45'only_440 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11
  = case coe v5 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v13
        -> case coe v11 of
             C_μlayer'45'K_196 v21 -> coe C_μlayer'45'K_196 v21
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> case coe v11 of
             C_μlayer'45'Id_208 v17
               -> coe
                    C_μlayer'45'Id_208
                    (coe
                       du_μValid'45'mem'45'only_456 (coe v0) (coe v1) (coe v4) (coe v3)
                       (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v16 v17
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                      -> case coe v11 of
                           C_μlayer'45'inl_230 v27 v30 v31 v32
                             -> coe
                                  C_μlayer'45'inl_230 v27 v30 v31
                                  (coe
                                     du_μLayerValid'45'mem'45'only_440 (coe v0) (coe v1) (coe v16)
                                     (coe v3) (coe v4) (coe v14) (coe v6) (coe v18) (coe v27)
                                     (coe v9) (coe v10) (coe v32))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                      -> case coe v11 of
                           C_μlayer'45'inr_252 v27 v30 v31 v32
                             -> coe
                                  C_μlayer'45'inr_252 v27 v30 v31
                                  (coe
                                     du_μLayerValid'45'mem'45'only_440 (coe v0) (coe v1) (coe v17)
                                     (coe v3) (coe v4) (coe v15) (coe v6) (coe v18) (coe v27)
                                     (coe v9) (coe v10) (coe v32))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v16 v17
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                      -> case coe v11 of
                           C_μlayer'45'prod_278 v29 v30 v34 v35 v36 v37 v38
                             -> coe
                                  C_μlayer'45'prod_278 v29 v30 v34 v35 v36
                                  (coe
                                     du_μLayerValid'45'mem'45'only_440 (coe v0) (coe v1) (coe v16)
                                     (coe v3) (coe v4) (coe v14) (coe v6) (coe v18) (coe v29)
                                     (coe v9) (coe v10) (coe v37))
                                  (coe
                                     du_μLayerValid'45'mem'45'only_440 (coe v0) (coe v1) (coe v17)
                                     (coe v3) (coe v4) (coe v15) (coe v6) (coe v19) (coe v30)
                                     (coe v9) (coe v10) (coe v38))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μValid-mem-only
d_μValid'45'mem'45'only_456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_μValid_178 -> T_μValid_178
d_μValid'45'mem'45'only_456 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10 v11
  = du_μValid'45'mem'45'only_456 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11
du_μValid'45'mem'45'only_456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  T_μValid_178 -> T_μValid_178
du_μValid'45'mem'45'only_456 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_μ'45'valid_292 v15 v16
        -> coe
             C_μ'45'valid_292 v15
             (coe
                du_μLayerValid'45'mem'45'only_440 (coe v0) (coe v1) (coe v3)
                (coe v3) (coe v2) (coe v4) (coe v4)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_928 (coe v3)
                   (coe v4) (coe v5))
                (coe v6) (coe v7) (coe v8) (coe v16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νLayerValid-mem-only
d_νLayerValid'45'mem'45'only_624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_νLayerValid_300 -> T_νLayerValid_300
d_νLayerValid'45'mem'45'only_624 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 ~v11 ~v12 v13
  = du_νLayerValid'45'mem'45'only_624
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v13
du_νLayerValid'45'mem'45'only_624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  T_νLayerValid_300 -> T_νLayerValid_300
du_νLayerValid'45'mem'45'only_624 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11
  = case coe v5 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v13
        -> case coe v11 of
             C_νlayer'45'K_324 v21 -> coe C_νlayer'45'K_324 v21
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> case coe v11 of
             C_νlayer'45'Id_336 v17
               -> coe
                    C_νlayer'45'Id_336
                    (coe
                       du_νValid'45'mem'45'only_640 (coe v0) (coe v1) (coe v4) (coe v3)
                       (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v16 v17
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                      -> case coe v11 of
                           C_νlayer'45'inl_358 v27 v30 v31 v32
                             -> coe
                                  C_νlayer'45'inl_358 v27 v30 v31
                                  (coe
                                     du_νLayerValid'45'mem'45'only_624 (coe v0) (coe v1) (coe v16)
                                     (coe v3) (coe v4) (coe v14) (coe v6) (coe v18) (coe v27)
                                     (coe v9) (coe v10) (coe v32))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                      -> case coe v11 of
                           C_νlayer'45'inr_380 v27 v30 v31 v32
                             -> coe
                                  C_νlayer'45'inr_380 v27 v30 v31
                                  (coe
                                     du_νLayerValid'45'mem'45'only_624 (coe v0) (coe v1) (coe v17)
                                     (coe v3) (coe v4) (coe v15) (coe v6) (coe v18) (coe v27)
                                     (coe v9) (coe v10) (coe v32))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v16 v17
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                      -> case coe v11 of
                           C_νlayer'45'prod_406 v29 v30 v34 v35 v36 v37 v38
                             -> coe
                                  C_νlayer'45'prod_406 v29 v30 v34 v35 v36
                                  (coe
                                     du_νLayerValid'45'mem'45'only_624 (coe v0) (coe v1) (coe v16)
                                     (coe v3) (coe v4) (coe v14) (coe v6) (coe v18) (coe v29)
                                     (coe v9) (coe v10) (coe v37))
                                  (coe
                                     du_νLayerValid'45'mem'45'only_624 (coe v0) (coe v1) (coe v17)
                                     (coe v3) (coe v4) (coe v15) (coe v6) (coe v19) (coe v30)
                                     (coe v9) (coe v10) (coe v38))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νValid-mem-only
d_νValid'45'mem'45'only_640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_νValid_306 -> T_νValid_306
d_νValid'45'mem'45'only_640 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10 v11
  = du_νValid'45'mem'45'only_640 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11
du_νValid'45'mem'45'only_640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  T_νValid_306 -> T_νValid_306
du_νValid'45'mem'45'only_640 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_ν'45'valid_420 v15 v16
        -> coe
             C_ν'45'valid_420 v15
             (coe
                du_νLayerValid'45'mem'45'only_624 (coe v0) (coe v1) (coe v3)
                (coe v3) (coe v2) (coe v4) (coe v4)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_990 (coe v3)
                   (coe v4) (coe v5))
                (coe v6) (coe v7) (coe v8) (coe v16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μLayerValid-frontier-advance
d_μLayerValid'45'frontier'45'advance_808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_μLayerValid_172 -> T_μLayerValid_172
d_μLayerValid'45'frontier'45'advance_808 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 ~v11 v12 v13 v14
  = du_μLayerValid'45'frontier'45'advance_808
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_μLayerValid'45'frontier'45'advance_808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_μLayerValid_172 -> T_μLayerValid_172
du_μLayerValid'45'frontier'45'advance_808 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10 v11 v12 v13
  = case coe v6 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v15
        -> case coe v13 of
             C_μlayer'45'K_196 v23
               -> coe
                    C_μlayer'45'K_196
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                       (coe v11) (coe v12) (coe v9) (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> case coe v13 of
             C_μlayer'45'Id_208 v19
               -> coe
                    C_μlayer'45'Id_208
                    (coe
                       du_μValid'45'frontier'45'advance_824 (coe v0) (coe v1) (coe v4)
                       (coe v5) (coe v3) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                       (coe v12) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v18 v19
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                      -> case coe v13 of
                           C_μlayer'45'inl_230 v29 v32 v33 v34
                             -> coe
                                  C_μlayer'45'inl_230 v29
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12) (coe v29) (coe v32))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     (coe v33))
                                  (coe
                                     du_μLayerValid'45'frontier'45'advance_808 (coe v0) (coe v1)
                                     (coe v18) (coe v3) (coe v4) (coe v5) (coe v16) (coe v7)
                                     (coe v20) (coe v29) (coe v10) (coe v11) (coe v12) (coe v34))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                      -> case coe v13 of
                           C_μlayer'45'inr_252 v29 v32 v33 v34
                             -> coe
                                  C_μlayer'45'inr_252 v29
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12) (coe v29) (coe v32))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     (coe v33))
                                  (coe
                                     du_μLayerValid'45'frontier'45'advance_808 (coe v0) (coe v1)
                                     (coe v19) (coe v3) (coe v4) (coe v5) (coe v17) (coe v7)
                                     (coe v20) (coe v29) (coe v10) (coe v11) (coe v12) (coe v34))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v18 v19
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                      -> case coe v13 of
                           C_μlayer'45'prod_278 v31 v32 v36 v37 v38 v39 v40
                             -> coe
                                  C_μlayer'45'prod_278 v31 v32
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12) (coe v31) (coe v36))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12) (coe v32) (coe v37))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     (coe v38))
                                  (coe
                                     du_μLayerValid'45'frontier'45'advance_808 (coe v0) (coe v1)
                                     (coe v18) (coe v3) (coe v4) (coe v5) (coe v16) (coe v7)
                                     (coe v20) (coe v31) (coe v10) (coe v11) (coe v12) (coe v39))
                                  (coe
                                     du_μLayerValid'45'frontier'45'advance_808 (coe v0) (coe v1)
                                     (coe v19) (coe v3) (coe v4) (coe v5) (coe v17) (coe v7)
                                     (coe v21) (coe v32) (coe v10) (coe v11) (coe v12) (coe v40))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μValid-frontier-advance
d_μValid'45'frontier'45'advance_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_μValid_178 -> T_μValid_178
d_μValid'45'frontier'45'advance_824 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
                                    v10 v11 v12
  = du_μValid'45'frontier'45'advance_824
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11 v12
du_μValid'45'frontier'45'advance_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_μValid_178 -> T_μValid_178
du_μValid'45'frontier'45'advance_824 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11
  = case coe v11 of
      C_μ'45'valid_292 v17 v18
        -> coe
             C_μ'45'valid_292
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                (coe v9) (coe v10) (coe v7) (coe v17))
             (coe
                du_μLayerValid'45'frontier'45'advance_808 (coe v0) (coe v1)
                (coe v4) (coe v4) (coe v2) (coe v3) (coe v5) (coe v5)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_928 (coe v4)
                   (coe v5) (coe v6))
                (coe v7) (coe v8) (coe v9) (coe v10) (coe v18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νLayerValid-frontier-advance
d_νLayerValid'45'frontier'45'advance_1004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_νLayerValid_300 -> T_νLayerValid_300
d_νLayerValid'45'frontier'45'advance_1004 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10 ~v11 v12 v13 v14
  = du_νLayerValid'45'frontier'45'advance_1004
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_νLayerValid'45'frontier'45'advance_1004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_νLayerValid_300 -> T_νLayerValid_300
du_νLayerValid'45'frontier'45'advance_1004 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10 v11 v12 v13
  = case coe v6 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v15
        -> case coe v13 of
             C_νlayer'45'K_324 v23
               -> coe
                    C_νlayer'45'K_324
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                       (coe v11) (coe v12) (coe v9) (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> case coe v13 of
             C_νlayer'45'Id_336 v19
               -> coe
                    C_νlayer'45'Id_336
                    (coe
                       du_νValid'45'frontier'45'advance_1020 (coe v0) (coe v1) (coe v4)
                       (coe v5) (coe v3) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                       (coe v12) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v18 v19
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                      -> case coe v13 of
                           C_νlayer'45'inl_358 v29 v32 v33 v34
                             -> coe
                                  C_νlayer'45'inl_358 v29
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12) (coe v29) (coe v32))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     (coe v33))
                                  (coe
                                     du_νLayerValid'45'frontier'45'advance_1004 (coe v0) (coe v1)
                                     (coe v18) (coe v3) (coe v4) (coe v5) (coe v16) (coe v7)
                                     (coe v20) (coe v29) (coe v10) (coe v11) (coe v12) (coe v34))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                      -> case coe v13 of
                           C_νlayer'45'inr_380 v29 v32 v33 v34
                             -> coe
                                  C_νlayer'45'inr_380 v29
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12) (coe v29) (coe v32))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     (coe v33))
                                  (coe
                                     du_νLayerValid'45'frontier'45'advance_1004 (coe v0) (coe v1)
                                     (coe v19) (coe v3) (coe v4) (coe v5) (coe v17) (coe v7)
                                     (coe v20) (coe v29) (coe v10) (coe v11) (coe v12) (coe v34))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v18 v19
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                      -> case coe v13 of
                           C_νlayer'45'prod_406 v31 v32 v36 v37 v38 v39 v40
                             -> coe
                                  C_νlayer'45'prod_406 v31 v32
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12) (coe v31) (coe v36))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12) (coe v32) (coe v37))
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                                     (coe v11) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     (coe v38))
                                  (coe
                                     du_νLayerValid'45'frontier'45'advance_1004 (coe v0) (coe v1)
                                     (coe v18) (coe v3) (coe v4) (coe v5) (coe v16) (coe v7)
                                     (coe v20) (coe v31) (coe v10) (coe v11) (coe v12) (coe v39))
                                  (coe
                                     du_νLayerValid'45'frontier'45'advance_1004 (coe v0) (coe v1)
                                     (coe v19) (coe v3) (coe v4) (coe v5) (coe v17) (coe v7)
                                     (coe v21) (coe v32) (coe v10) (coe v11) (coe v12) (coe v40))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νValid-frontier-advance
d_νValid'45'frontier'45'advance_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_νValid_306 -> T_νValid_306
d_νValid'45'frontier'45'advance_1020 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
                                     v10 v11 v12
  = du_νValid'45'frontier'45'advance_1020
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11 v12
du_νValid'45'frontier'45'advance_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_νValid_306 -> T_νValid_306
du_νValid'45'frontier'45'advance_1020 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                      v10 v11
  = case coe v11 of
      C_ν'45'valid_420 v17 v18
        -> coe
             C_ν'45'valid_420
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_814
                (coe v9) (coe v10) (coe v7) (coe v17))
             (coe
                du_νLayerValid'45'frontier'45'advance_1004 (coe v0) (coe v1)
                (coe v4) (coe v4) (coe v2) (coe v3) (coe v5) (coe v5)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_990 (coe v4)
                   (coe v5) (coe v6))
                (coe v7) (coe v8) (coe v9) (coe v10) (coe v18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μLayerValid-bf-transfer
d_μLayerValid'45'bf'45'transfer_1204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610) ->
  T_μLayerValid_172 -> T_μLayerValid_172
d_μLayerValid'45'bf'45'transfer_1204 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11 v12
  = case coe v6 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v14
        -> case coe v12 of
             C_μlayer'45'K_196 v22 -> coe C_μlayer'45'K_196 (coe v11 v9 v22)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> case coe v12 of
             C_μlayer'45'Id_208 v18
               -> coe
                    C_μlayer'45'Id_208
                    (d_μValid'45'bf'45'transfer_1224
                       (coe v0) (coe v1) (coe v4) (coe v5) (coe v3) (coe v7) (coe v8)
                       (coe v9) (coe v10) (coe v11) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v17 v18
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v19
                      -> case coe v12 of
                           C_μlayer'45'inl_230 v28 v31 v32 v33
                             -> coe
                                  C_μlayer'45'inl_230 v28 (coe v11 v28 v31)
                                  (coe
                                     v11
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     v32)
                                  (d_μLayerValid'45'bf'45'transfer_1204
                                     (coe v0) (coe v1) (coe v17) (coe v3) (coe v4) (coe v5)
                                     (coe v15) (coe v7) (coe v19) (coe v28) (coe v10) (coe v11)
                                     (coe v33))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v19
                      -> case coe v12 of
                           C_μlayer'45'inr_252 v28 v31 v32 v33
                             -> coe
                                  C_μlayer'45'inr_252 v28 (coe v11 v28 v31)
                                  (coe
                                     v11
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     v32)
                                  (d_μLayerValid'45'bf'45'transfer_1204
                                     (coe v0) (coe v1) (coe v18) (coe v3) (coe v4) (coe v5)
                                     (coe v16) (coe v7) (coe v19) (coe v28) (coe v10) (coe v11)
                                     (coe v33))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v17 v18
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                      -> case coe v12 of
                           C_μlayer'45'prod_278 v30 v31 v35 v36 v37 v38 v39
                             -> coe
                                  C_μlayer'45'prod_278 v30 v31 (coe v11 v30 v35) (coe v11 v31 v36)
                                  (coe
                                     v11
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     v37)
                                  (d_μLayerValid'45'bf'45'transfer_1204
                                     (coe v0) (coe v1) (coe v17) (coe v3) (coe v4) (coe v5)
                                     (coe v15) (coe v7) (coe v19) (coe v30) (coe v10) (coe v11)
                                     (coe v38))
                                  (d_μLayerValid'45'bf'45'transfer_1204
                                     (coe v0) (coe v1) (coe v18) (coe v3) (coe v4) (coe v5)
                                     (coe v16) (coe v7) (coe v20) (coe v31) (coe v10) (coe v11)
                                     (coe v39))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μValid-bf-transfer
d_μValid'45'bf'45'transfer_1224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610) ->
  T_μValid_178 -> T_μValid_178
d_μValid'45'bf'45'transfer_1224 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_μ'45'valid_292 v16 v17
        -> coe
             C_μ'45'valid_292 (coe v9 v7 v16)
             (d_μLayerValid'45'bf'45'transfer_1204
                (coe v0) (coe v1) (coe v4) (coe v4) (coe v2) (coe v3) (coe v5)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_928 (coe v4)
                   (coe v5) (coe v6))
                (coe v7) (coe v8) (coe v9) (coe v17))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νLayerValid-bf-transfer
d_νLayerValid'45'bf'45'transfer_1384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610) ->
  T_νLayerValid_300 -> T_νLayerValid_300
d_νLayerValid'45'bf'45'transfer_1384 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11 v12
  = case coe v6 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v14
        -> case coe v12 of
             C_νlayer'45'K_324 v22 -> coe C_νlayer'45'K_324 (coe v11 v9 v22)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> case coe v12 of
             C_νlayer'45'Id_336 v18
               -> coe
                    C_νlayer'45'Id_336
                    (d_νValid'45'bf'45'transfer_1404
                       (coe v0) (coe v1) (coe v4) (coe v5) (coe v3) (coe v7) (coe v8)
                       (coe v9) (coe v10) (coe v11) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v17 v18
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v19
                      -> case coe v12 of
                           C_νlayer'45'inl_358 v28 v31 v32 v33
                             -> coe
                                  C_νlayer'45'inl_358 v28 (coe v11 v28 v31)
                                  (coe
                                     v11
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     v32)
                                  (d_νLayerValid'45'bf'45'transfer_1384
                                     (coe v0) (coe v1) (coe v17) (coe v3) (coe v4) (coe v5)
                                     (coe v15) (coe v7) (coe v19) (coe v28) (coe v10) (coe v11)
                                     (coe v33))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v19
                      -> case coe v12 of
                           C_νlayer'45'inr_380 v28 v31 v32 v33
                             -> coe
                                  C_νlayer'45'inr_380 v28 (coe v11 v28 v31)
                                  (coe
                                     v11
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     v32)
                                  (d_νLayerValid'45'bf'45'transfer_1384
                                     (coe v0) (coe v1) (coe v18) (coe v3) (coe v4) (coe v5)
                                     (coe v16) (coe v7) (coe v19) (coe v28) (coe v10) (coe v11)
                                     (coe v33))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v17 v18
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                      -> case coe v12 of
                           C_νlayer'45'prod_406 v30 v31 v35 v36 v37 v38 v39
                             -> coe
                                  C_νlayer'45'prod_406 v30 v31 (coe v11 v30 v35) (coe v11 v31 v36)
                                  (coe
                                     v11
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v9))
                                     v37)
                                  (d_νLayerValid'45'bf'45'transfer_1384
                                     (coe v0) (coe v1) (coe v17) (coe v3) (coe v4) (coe v5)
                                     (coe v15) (coe v7) (coe v19) (coe v30) (coe v10) (coe v11)
                                     (coe v38))
                                  (d_νLayerValid'45'bf'45'transfer_1384
                                     (coe v0) (coe v1) (coe v18) (coe v3) (coe v4) (coe v5)
                                     (coe v16) (coe v7) (coe v20) (coe v31) (coe v10) (coe v11)
                                     (coe v39))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νValid-bf-transfer
d_νValid'45'bf'45'transfer_1404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610) ->
  T_νValid_306 -> T_νValid_306
d_νValid'45'bf'45'transfer_1404 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_ν'45'valid_420 v16 v17
        -> coe
             C_ν'45'valid_420 (coe v9 v7 v16)
             (d_νLayerValid'45'bf'45'transfer_1384
                (coe v0) (coe v1) (coe v4) (coe v4) (coe v2) (coe v3) (coe v5)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_990 (coe v4)
                   (coe v5) (coe v6))
                (coe v7) (coe v8) (coe v9) (coe v17))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μLayerValid-mem-preserved
d_μLayerValid'45'mem'45'preserved_1562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_μLayerValid_172 -> T_μLayerValid_172
d_μLayerValid'45'mem'45'preserved_1562 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 ~v12 v13
  = du_μLayerValid'45'mem'45'preserved_1562
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13
du_μLayerValid'45'mem'45'preserved_1562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  T_μLayerValid_172 -> T_μLayerValid_172
du_μLayerValid'45'mem'45'preserved_1562 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12
  = case coe v5 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v14
        -> case coe v12 of
             C_μlayer'45'K_196 v22 -> coe C_μlayer'45'K_196 v22
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> case coe v12 of
             C_μlayer'45'Id_208 v18
               -> coe
                    C_μlayer'45'Id_208
                    (coe
                       du_μValid'45'mem'45'preserved_1580 (coe v0) (coe v1) (coe v4)
                       (coe v3) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                       (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v17 v18
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v19
                      -> case coe v12 of
                           C_μlayer'45'inl_230 v28 v31 v32 v33
                             -> coe
                                  C_μlayer'45'inl_230 v28 v31 v32
                                  (coe
                                     du_μLayerValid'45'mem'45'preserved_1562 (coe v0) (coe v1)
                                     (coe v17) (coe v3) (coe v4) (coe v15) (coe v6) (coe v19)
                                     (coe v28) (coe v9) (coe v10) (coe v31) (coe v33))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v19
                      -> case coe v12 of
                           C_μlayer'45'inr_252 v28 v31 v32 v33
                             -> coe
                                  C_μlayer'45'inr_252 v28 v31 v32
                                  (coe
                                     du_μLayerValid'45'mem'45'preserved_1562 (coe v0) (coe v1)
                                     (coe v18) (coe v3) (coe v4) (coe v16) (coe v6) (coe v19)
                                     (coe v28) (coe v9) (coe v10) (coe v31) (coe v33))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v17 v18
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                      -> case coe v12 of
                           C_μlayer'45'prod_278 v30 v31 v35 v36 v37 v38 v39
                             -> coe
                                  C_μlayer'45'prod_278 v30 v31 v35 v36 v37
                                  (coe
                                     du_μLayerValid'45'mem'45'preserved_1562 (coe v0) (coe v1)
                                     (coe v17) (coe v3) (coe v4) (coe v15) (coe v6) (coe v19)
                                     (coe v30) (coe v9) (coe v10) (coe v35) (coe v38))
                                  (coe
                                     du_μLayerValid'45'mem'45'preserved_1562 (coe v0) (coe v1)
                                     (coe v18) (coe v3) (coe v4) (coe v16) (coe v6) (coe v20)
                                     (coe v31) (coe v9) (coe v10) (coe v36) (coe v39))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.μValid-mem-preserved
d_μValid'45'mem'45'preserved_1580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_μValid_178 -> T_μValid_178
d_μValid'45'mem'45'preserved_1580 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                  ~v10 v11
  = du_μValid'45'mem'45'preserved_1580
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11
du_μValid'45'mem'45'preserved_1580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  T_μValid_178 -> T_μValid_178
du_μValid'45'mem'45'preserved_1580 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10
  = case coe v10 of
      C_μ'45'valid_292 v16 v17
        -> coe
             C_μ'45'valid_292 v16
             (coe
                du_μLayerValid'45'mem'45'preserved_1562 (coe v0) (coe v1) (coe v3)
                (coe v3) (coe v2) (coe v4) (coe v4)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_sem'45'Out_928 (coe v3)
                   (coe v4) (coe v5))
                (coe v6) (coe v7) (coe v8) (coe v9) (coe v17))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νLayerValid-mem-preserved
d_νLayerValid'45'mem'45'preserved_1750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_νLayerValid_300 -> T_νLayerValid_300
d_νLayerValid'45'mem'45'preserved_1750 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 v10 v11 ~v12 v13
  = du_νLayerValid'45'mem'45'preserved_1750
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13
du_νLayerValid'45'mem'45'preserved_1750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  T_νLayerValid_300 -> T_νLayerValid_300
du_νLayerValid'45'mem'45'preserved_1750 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12
  = case coe v5 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v14
        -> case coe v12 of
             C_νlayer'45'K_324 v22 -> coe C_νlayer'45'K_324 v22
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> case coe v12 of
             C_νlayer'45'Id_336 v18
               -> coe
                    C_νlayer'45'Id_336
                    (coe
                       du_νValid'45'mem'45'preserved_1768 (coe v0) (coe v1) (coe v4)
                       (coe v3) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                       (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v17 v18
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v19
                      -> case coe v12 of
                           C_νlayer'45'inl_358 v28 v31 v32 v33
                             -> coe
                                  C_νlayer'45'inl_358 v28 v31 v32
                                  (coe
                                     du_νLayerValid'45'mem'45'preserved_1750 (coe v0) (coe v1)
                                     (coe v17) (coe v3) (coe v4) (coe v15) (coe v6) (coe v19)
                                     (coe v28) (coe v9) (coe v10) (coe v31) (coe v33))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v19
                      -> case coe v12 of
                           C_νlayer'45'inr_380 v28 v31 v32 v33
                             -> coe
                                  C_νlayer'45'inr_380 v28 v31 v32
                                  (coe
                                     du_νLayerValid'45'mem'45'preserved_1750 (coe v0) (coe v1)
                                     (coe v18) (coe v3) (coe v4) (coe v16) (coe v6) (coe v19)
                                     (coe v28) (coe v9) (coe v10) (coe v31) (coe v33))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v17 v18
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                      -> case coe v12 of
                           C_νlayer'45'prod_406 v30 v31 v35 v36 v37 v38 v39
                             -> coe
                                  C_νlayer'45'prod_406 v30 v31 v35 v36 v37
                                  (coe
                                     du_νLayerValid'45'mem'45'preserved_1750 (coe v0) (coe v1)
                                     (coe v17) (coe v3) (coe v4) (coe v15) (coe v6) (coe v19)
                                     (coe v30) (coe v9) (coe v10) (coe v35) (coe v38))
                                  (coe
                                     du_νLayerValid'45'mem'45'preserved_1750 (coe v0) (coe v1)
                                     (coe v18) (coe v3) (coe v4) (coe v16) (coe v6) (coe v20)
                                     (coe v31) (coe v9) (coe v10) (coe v36) (coe v39))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.IR.MuValidity.MuValidityImpl.νValid-mem-preserved
d_νValid'45'mem'45'preserved_1768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_νValid_306 -> T_νValid_306
d_νValid'45'mem'45'preserved_1768 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                  ~v10 v11
  = du_νValid'45'mem'45'preserved_1768
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11
du_νValid'45'mem'45'preserved_1768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  T_νValid_306 -> T_νValid_306
du_νValid'45'mem'45'preserved_1768 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10
  = case coe v10 of
      C_ν'45'valid_420 v16 v17
        -> coe
             C_ν'45'valid_420 v16
             (coe
                du_νLayerValid'45'mem'45'preserved_1750 (coe v0) (coe v1) (coe v3)
                (coe v3) (coe v2) (coe v4) (coe v4)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_sem'45'CoOut_990 (coe v3)
                   (coe v4) (coe v5))
                (coe v6) (coe v7) (coe v8) (coe v9) (coe v17))
      _ -> MAlonzo.RTE.mazUnreachableError
