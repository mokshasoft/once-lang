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

module MAlonzo.Code.Once.Postulates where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Postulates.extensionality
d_extensionality_16
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.extensionality"
-- Once.Postulates.toList-++
d_toList'45''43''43'_22
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.toList-++"
-- Once.Postulates.toList∘fromList
d_toList'8728'fromList_26
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Postulates.toList\8728fromList"
