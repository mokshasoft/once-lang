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
import qualified MAlonzo.Code.Once.CCC.SigOp.Info

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
  Integer -> MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276
d_lit'45'int'45'info_12 v0
  = coe
      MAlonzo.Code.Once.CCC.SigOp.Info.C_mk'45'info_298
      (coe d_lit'45'int'45'name_8 (coe v0)) (coe (\ v1 -> v0))
      (coe
         (\ v1 ->
            MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_266)
