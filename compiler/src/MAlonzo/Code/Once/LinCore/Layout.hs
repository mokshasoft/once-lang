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
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.LinCore.Layout._.LTy
d_LTy_74 a0 a1 = ()
-- Once.LinCore.Layout._.Sh
d_Sh_616 a0 a1 = ()
-- Once.LinCore.Layout._.Sh.env
d_env_622 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_env_622 v0
  = coe MAlonzo.Code.Once.LinCore.Code.d_env_758 (coe v0)
-- Once.LinCore.Layout._.Sh.ops
d_ops_624 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_ops_624 v0
  = coe MAlonzo.Code.Once.LinCore.Code.d_ops_760 (coe v0)
-- Once.LinCore.Layout._.Codeᴵ
d_Code'7477'_638 a0 a1 a2 a3 = ()
-- Once.LinCore.Layout._.Insᴵ
d_Ins'7477'_640 a0 a1 a2 a3 = ()
-- Once.LinCore.Layout.wsz
d_wsz_880 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
d_wsz_880 ~v0 ~v1 v2 = du_wsz_880 v2
du_wsz_880 :: MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
du_wsz_880 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_One_180 -> coe (0 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Zero_182 -> coe (0 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v1 v2
        -> coe addInt (coe du_wsz_880 (coe v1)) (coe du_wsz_880 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v1 v2
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe du_wsz_880 (coe v1))
                (coe du_wsz_880 (coe v2)))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v1 v2
        -> coe du_wsz_880 (coe v2)
      MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v1 v2 v3 v4
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_μt_194 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Bt_196 v1 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.ws
d_ws_908 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
d_ws_908 ~v0 ~v1 v2 = du_ws_908 v2
du_ws_908 :: [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
du_ws_908 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2
        -> coe addInt (coe du_ws_908 (coe v2)) (coe du_wsz_880 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.envW
d_envW_914 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 -> Integer
d_envW_914 ~v0 ~v1 v2 = du_envW_914 v2
du_envW_914 :: MAlonzo.Code.Once.LinCore.Code.T_Sh_752 -> Integer
du_envW_914 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v1 v2
        -> coe du_ws_908 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.opW
d_opW_920 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 -> Integer
d_opW_920 ~v0 ~v1 v2 = du_opW_920 v2
du_opW_920 :: MAlonzo.Code.Once.LinCore.Code.T_Sh_752 -> Integer
du_opW_920 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v1 v2
        -> coe du_ws_908 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout._⊔²_
d__'8852''178'__926 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8852''178'__926 ~v0 ~v1 v2 v3 = du__'8852''178'__926 v2 v3
du__'8852''178'__926 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'8852''178'__926 v0 v1
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
d_at_936 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_936 ~v0 ~v1 v2 = du_at_936 v2
du_at_936 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_936 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_envW_914 (coe v0)) (coe du_opW_920 (coe v0))
-- Once.LinCore.Layout.peakI
d_peakI_944 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Once.LinCore.Image.T_Ins'7477'_992 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peakI_944 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
              (coe (0 :: Integer)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.LinCore.Image.C_swap_1022
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v10 v11
                  -> case coe v11 of
                       (:) v12 v13
                         -> case coe v13 of
                              (:) v14 v15
                                -> case coe v3 of
                                     MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v16 v17
                                       -> case coe v17 of
                                            (:) v18 v19
                                              -> case coe v19 of
                                                   (:) v20 v21
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe (0 :: Integer))
                                                          (coe
                                                             addInt (coe du_ws_908 (coe v11))
                                                             (coe du_wsz_880 (coe v12)))
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.LinCore.Image.C_prim_1042 v6 v7 v12
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v13 v14
                  -> case coe v14 of
                       (:) v15 v16
                         -> case coe v3 of
                              MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v17 v18
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
                                                                    addInt (coe du_ws_908 (coe v14))
                                                                    (coe du_wsz_880 (coe v24)))
                                                          _ -> coe v5
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.LinCore.Image.C_loop_1334 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v12 v13
                  -> case coe v12 of
                       (:) v14 v15
                         -> case coe v13 of
                              (:) v16 v17
                                -> case coe v3 of
                                     MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v18 v19
                                       -> case coe v18 of
                                            (:) v20 v21
                                              -> case coe v19 of
                                                   (:) v22 v23
                                                     -> coe
                                                          du_peakC_950 (coe v0) (coe v1) (coe v2)
                                                          (coe v11)
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v5)
-- Once.LinCore.Layout.peakC
d_peakC_950 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_990 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peakC_950 v0 v1 v2 ~v3 v4 = du_peakC_950 v0 v1 v2 v4
du_peakC_950 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_990 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_peakC_950 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.LinCore.Image.C_end_1344
        -> coe du_at_936 (coe v2)
      MAlonzo.Code.Once.LinCore.Image.C__'10814'__1352 v5 v7 v8
        -> coe
             du__'8852''178'__926 (coe du_at_936 (coe v2))
             (coe
                du__'8852''178'__926
                (coe d_peakI_944 (coe v0) (coe v1) (coe v2) (coe v5) (coe v7))
                (coe du_peakC_950 (coe v0) (coe v1) (coe v5) (coe v8)))
      MAlonzo.Code.Once.LinCore.Image.C_case_1364 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v11 v12
               -> case coe v12 of
                    (:) v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v15 v16
                             -> coe
                                  du__'8852''178'__926 (coe du_at_936 (coe v2))
                                  (coe
                                     du__'8852''178'__926
                                     (coe
                                        du_peakC_950 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v15)
                                              (coe v14)))
                                        (coe v9))
                                     (coe
                                        du_peakC_950 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v16)
                                              (coe v14)))
                                        (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Image.C_ecase_1376 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Code.C__'8739'__762 v11 v12
               -> case coe v11 of
                    (:) v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v15 v16
                             -> coe
                                  du__'8852''178'__926 (coe du_at_936 (coe v2))
                                  (coe
                                     du__'8852''178'__926
                                     (coe
                                        du_peakC_950 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__762
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v15)
                                              (coe v11))
                                           (coe v12))
                                        (coe v9))
                                     (coe
                                        du_peakC_950 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__762
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v16)
                                              (coe v11))
                                           (coe v12))
                                        (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Image.C_halted_1382
        -> coe du_at_936 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.Frame
d_Frame_990 a0 a1 = ()
data T_Frame_990 = C_frame_1000 Integer Integer
-- Once.LinCore.Layout.Frame.EP
d_EP_996 :: T_Frame_990 -> Integer
d_EP_996 v0
  = case coe v0 of
      C_frame_1000 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.Frame.OP
d_OP_998 :: T_Frame_990 -> Integer
d_OP_998 v0
  = case coe v0 of
      C_frame_1000 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.budget
d_budget_1002 :: T_Frame_990 -> Integer
d_budget_1002 v0
  = coe addInt (coe d_OP_998 (coe v0)) (coe d_EP_996 (coe v0))
-- Once.LinCore.Layout.frameOf
d_frameOf_1010 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_990 -> T_Frame_990
d_frameOf_1010 v0 v1 v2 ~v3 v4 = du_frameOf_1010 v0 v1 v2 v4
du_frameOf_1010 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_752 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_990 -> T_Frame_990
du_frameOf_1010 v0 v1 v2 v3
  = coe
      C_frame_1000
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_peakC_950 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_peakC_950 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.LinCore.Layout.envAt
d_envAt_1014 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
d_envAt_1014 ~v0 ~v1 v2 = du_envAt_1014 v2
du_envAt_1014 ::
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
du_envAt_1014 v0 = coe du_ws_908 (coe v0)
-- Once.LinCore.Layout.opAt
d_opAt_1018 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  T_Frame_990 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
d_opAt_1018 ~v0 ~v1 v2 v3 = du_opAt_1018 v2 v3
du_opAt_1018 ::
  T_Frame_990 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
du_opAt_1018 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (addInt (coe d_OP_998 (coe v0)) (coe d_EP_996 (coe v0)))
      (coe du_ws_908 (coe v1))
