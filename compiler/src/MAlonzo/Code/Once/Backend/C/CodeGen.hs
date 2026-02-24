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

module MAlonzo.Code.Once.Backend.C.CodeGen where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Backend.C.Emit
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Backend.C.CodeGen.compile-c-expr
d_compile'45'c'45'expr_12 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compile'45'c'45'expr_12 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_14 -> coe v3
      MAlonzo.Code.Once.IR.C__'8728'__22 v5 v7 v8
        -> coe
             d_compile'45'c'45'expr_12 (coe v5) (coe v1) (coe v7)
             (coe d_compile'45'c'45'expr_12 (coe v0) (coe v5) (coe v8) (coe v3))
      MAlonzo.Code.Once.IR.C_fst_28
        -> coe
             MAlonzo.Code.Once.Backend.C.Emit.d_pairAccess_68 (coe v3)
             (coe ("fst" :: Data.Text.Text))
      MAlonzo.Code.Once.IR.C_snd_34
        -> coe
             MAlonzo.Code.Once.Backend.C.Emit.d_pairAccess_68 (coe v3)
             (coe ("snd" :: Data.Text.Text))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v10 v11
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("(OncePair){ .fst = " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_compile'45'c'45'expr_12 (coe v0) (coe v10) (coe v7) (coe v3))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (", .snd = " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_compile'45'c'45'expr_12 (coe v0) (coe v11) (coe v8) (coe v3))
                             (" }" :: Data.Text.Text))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v6
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(OnceSum){ .tag = 0, .value = " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                (" }" :: Data.Text.Text))
      MAlonzo.Code.Once.IR.C_inr_54 v6
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(OnceSum){ .tag = 1, .value = " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                (" }" :: Data.Text.Text))
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v9 v10
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("(" :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (".tag == 0 ? " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_compile'45'c'45'expr_12
                                (coe v9) (coe v1) (coe v7)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                                   (".value" :: Data.Text.Text)))
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (" : " :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (d_compile'45'c'45'expr_12
                                      (coe v10) (coe v1) (coe v8)
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                                         (".value" :: Data.Text.Text)))
                                   (")" :: Data.Text.Text))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66
        -> coe ("((void*)0)" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_initial_70 -> coe v3
      MAlonzo.Code.Once.IR.C_curry_78 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("({ typeof(" :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (") _ = " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("; " :: Data.Text.Text)
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (d_compile'45'c'45'expr_12
                                      (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                                      (coe v11) (coe v7) (coe ("_" :: Data.Text.Text)))
                                   ("; })" :: Data.Text.Text))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_84
        -> coe
             ("/* apply not yet implemented */ ((void*)0)" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_fold_88 -> coe v3
      MAlonzo.Code.Once.IR.C_unfold_92 -> coe v3
      MAlonzo.Code.Once.IR.C_arr_98 -> coe v3
      MAlonzo.Code.Once.IR.C_Prim_104 v6
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("once_" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v6
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("(" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                      (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.C.CodeGen.compile-c-function
d_compile'45'c'45'function_66 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compile'45'c'45'function_66 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Backend.C.Emit.d_functionDecl_92
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" {\n    return " :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (d_compile'45'c'45'expr_12
               (coe v2) (coe v3) (coe v4) (coe ("x" :: Data.Text.Text)))
            (";\n}" :: Data.Text.Text)))
