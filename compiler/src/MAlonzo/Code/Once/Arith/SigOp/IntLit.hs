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

module MAlonzo.Code.Once.Arith.SigOp.IntLit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.SigOp.Info

-- Once.Arith.SigOp.IntLit.lit-int-name
d_lit'45'int'45'name_8 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_lit'45'int'45'name_8 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("lit.int." :: Data.Text.Text)
      (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v0))
-- Once.Arith.SigOp.IntLit.lit-int-info
d_lit'45'int'45'info_12 ::
  Integer -> MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_lit'45'int'45'info_12 v0
  = coe
      MAlonzo.Code.Once.SigOp.Info.du_mk'45'info_234
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe d_lit'45'int'45'name_8 (coe v0)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
      (coe MAlonzo.Code.Once.SigOp.Info.C_Pure_124)
      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
      (coe
         MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
         (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206))
