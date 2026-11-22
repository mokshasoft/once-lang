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

module MAlonzo.Code.Once.LinCore.Layout where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.LinCore.Code
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.LinCore.Image
import qualified MAlonzo.Code.Once.LinCore.Values
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.LinCore.Layout._.LTy
d_LTy_74 a0 a1 = ()
-- Once.LinCore.Layout._.Sh
d_Sh_616 a0 a1 = ()
-- Once.LinCore.Layout._.Sh.env
d_env_622 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_env_622 v0
  = coe MAlonzo.Code.Once.LinCore.Code.d_env_766 (coe v0)
-- Once.LinCore.Layout._.Sh.ops
d_ops_624 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_ops_624 v0
  = coe MAlonzo.Code.Once.LinCore.Code.d_ops_768 (coe v0)
-- Once.LinCore.Layout._.Codeᴵ
d_Code'7477'_638 a0 a1 a2 a3 = ()
-- Once.LinCore.Layout._.Insᴵ
d_Ins'7477'_640 a0 a1 a2 a3 = ()
-- Once.LinCore.Layout.ws
d_ws_884 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
d_ws_884 ~v0 ~v1 v2 = du_ws_884 v2
du_ws_884 :: [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
du_ws_884 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2
        -> coe
             addInt (coe du_ws_884 (coe v2))
             (coe MAlonzo.Code.Once.LinCore.Values.du_wsz_662 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.envW
d_envW_890 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 -> Integer
d_envW_890 ~v0 ~v1 v2 = du_envW_890 v2
du_envW_890 :: MAlonzo.Code.Once.LinCore.Code.T_Sh_760 -> Integer
du_envW_890 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v1 v2
        -> coe du_ws_884 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.opW
d_opW_896 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 -> Integer
d_opW_896 ~v0 ~v1 v2 = du_opW_896 v2
du_opW_896 :: MAlonzo.Code.Once.LinCore.Code.T_Sh_760 -> Integer
du_opW_896 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v1 v2
        -> coe du_ws_884 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout._⊔²_
d__'8852''178'__902 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8852''178'__902 ~v0 ~v1 v2 v3 = du__'8852''178'__902 v2 v3
du__'8852''178'__902 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'8852''178'__902 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v2) (coe v4))
                    (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.at
d_at_912 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_912 ~v0 ~v1 v2 = du_at_912 v2
du_at_912 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_912 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_envW_890 (coe v0)) (coe du_opW_896 (coe v0))
-- Once.LinCore.Layout.peakI
d_peakI_920 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Once.LinCore.Image.T_Ins'7477'_1000 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peakI_920 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
              (coe (0 :: Integer)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.LinCore.Image.C_swap_1030
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v10 v11
                  -> case coe v11 of
                       (:) v12 v13
                         -> case coe v13 of
                              (:) v14 v15
                                -> case coe v3 of
                                     MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v16 v17
                                       -> case coe v17 of
                                            (:) v18 v19
                                              -> case coe v19 of
                                                   (:) v20 v21
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe (0 :: Integer))
                                                          (coe
                                                             addInt (coe du_ws_884 (coe v11))
                                                             (coe
                                                                MAlonzo.Code.Once.LinCore.Values.du_wsz_662
                                                                (coe v12)))
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.LinCore.Image.C_prim_1050 v6 v7 v12
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v13 v14
                  -> case coe v14 of
                       (:) v15 v16
                         -> case coe v3 of
                              MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v17 v18
                                -> case coe v18 of
                                     (:) v19 v20
                                       -> case coe v12 of
                                            MAlonzo.Code.Once.LinCore.Core.C_lswap_860
                                              -> case coe v15 of
                                                   MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v24 v25
                                                     -> case coe v19 of
                                                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v26 v27
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe (0 :: Integer))
                                                                 (coe
                                                                    addInt (coe du_ws_884 (coe v14))
                                                                    (coe
                                                                       MAlonzo.Code.Once.LinCore.Values.du_wsz_662
                                                                       (coe v24)))
                                                          _ -> coe v5
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.LinCore.Image.C_loop_1342 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v12 v13
                  -> case coe v12 of
                       (:) v14 v15
                         -> case coe v13 of
                              (:) v16 v17
                                -> case coe v3 of
                                     MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v18 v19
                                       -> case coe v18 of
                                            (:) v20 v21
                                              -> case coe v19 of
                                                   (:) v22 v23
                                                     -> coe
                                                          du_peakC_926 (coe v0) (coe v1) (coe v2)
                                                          (coe v11)
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v5)
-- Once.LinCore.Layout.peakC
d_peakC_926 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peakC_926 v0 v1 v2 ~v3 v4 = du_peakC_926 v0 v1 v2 v4
du_peakC_926 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_peakC_926 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.LinCore.Image.C_end_1352
        -> coe du_at_912 (coe v2)
      MAlonzo.Code.Once.LinCore.Image.C__'10814'__1360 v5 v7 v8
        -> coe
             du__'8852''178'__902 (coe du_at_912 (coe v2))
             (coe
                du__'8852''178'__902
                (coe d_peakI_920 (coe v0) (coe v1) (coe v2) (coe v5) (coe v7))
                (coe du_peakC_926 (coe v0) (coe v1) (coe v5) (coe v8)))
      MAlonzo.Code.Once.LinCore.Image.C_case_1372 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v11 v12
               -> case coe v12 of
                    (:) v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v15 v16
                             -> coe
                                  du__'8852''178'__902 (coe du_at_912 (coe v2))
                                  (coe
                                     du__'8852''178'__902
                                     (coe
                                        du_peakC_926 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v15)
                                              (coe v14)))
                                        (coe v9))
                                     (coe
                                        du_peakC_926 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v16)
                                              (coe v14)))
                                        (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Image.C_ecase_1384 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Code.C__'8739'__770 v11 v12
               -> case coe v11 of
                    (:) v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v15 v16
                             -> coe
                                  du__'8852''178'__902 (coe du_at_912 (coe v2))
                                  (coe
                                     du__'8852''178'__902
                                     (coe
                                        du_peakC_926 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__770
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v15)
                                              (coe v11))
                                           (coe v12))
                                        (coe v9))
                                     (coe
                                        du_peakC_926 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__770
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v16)
                                              (coe v11))
                                           (coe v12))
                                        (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Image.C_halted_1390
        -> coe du_at_912 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.Frame
d_Frame_966 a0 a1 = ()
data T_Frame_966 = C_frame_976 Integer Integer
-- Once.LinCore.Layout.Frame.EP
d_EP_972 :: T_Frame_966 -> Integer
d_EP_972 v0
  = case coe v0 of
      C_frame_976 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.Frame.OP
d_OP_974 :: T_Frame_966 -> Integer
d_OP_974 v0
  = case coe v0 of
      C_frame_976 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.budget
d_budget_978 :: T_Frame_966 -> Integer
d_budget_978 v0
  = coe addInt (coe d_OP_974 (coe v0)) (coe d_EP_972 (coe v0))
-- Once.LinCore.Layout.frameOf
d_frameOf_986 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_998 -> T_Frame_966
d_frameOf_986 v0 v1 v2 ~v3 v4 = du_frameOf_986 v0 v1 v2 v4
du_frameOf_986 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_760 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_998 -> T_Frame_966
du_frameOf_986 v0 v1 v2 v3
  = coe
      C_frame_976
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_peakC_926 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_peakC_926 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.LinCore.Layout.envAt
d_envAt_990 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
d_envAt_990 ~v0 ~v1 v2 = du_envAt_990 v2
du_envAt_990 ::
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
du_envAt_990 v0 = coe du_ws_884 (coe v0)
-- Once.LinCore.Layout.opAt
d_opAt_994 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  T_Frame_966 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
d_opAt_994 ~v0 ~v1 v2 v3 = du_opAt_994 v2 v3
du_opAt_994 ::
  T_Frame_966 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
du_opAt_994 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (addInt (coe d_OP_974 (coe v0)) (coe d_EP_972 (coe v0)))
      (coe du_ws_884 (coe v1))
