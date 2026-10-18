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

module MAlonzo.Code.Once.Spec.Signature where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Spec.Signature.BTy
d_BTy_6 = ()
data T_BTy_6
  = C_unit_8 | C_void_10 | C_int_12 | C_float_14 |
    C__'42'__16 T_BTy_6 T_BTy_6 | C__'43'__18 T_BTy_6 T_BTy_6
-- Once.Spec.Signature.⌜_⌝
d_'8988'_'8989'_22 ::
  Integer -> T_BTy_6 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_'8988'_'8989'_22 ~v0 v1 = du_'8988'_'8989'_22 v1
du_'8988'_'8989'_22 ::
  T_BTy_6 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_'8988'_'8989'_22 v0
  = case coe v0 of
      C_unit_8 -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      C_void_10 -> coe MAlonzo.Code.Once.Spec.Type.C_Void_20
      C_int_12 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_float_14 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      C__'42'__16 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe du_'8988'_'8989'_22 (coe v1))
             (coe du_'8988'_'8989'_22 (coe v2))
      C__'43'__18 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe du_'8988'_'8989'_22 (coe v1))
             (coe du_'8988'_'8989'_22 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.⟦_⟧ᵇ
d_'10214'_'10215''7495'_32 :: T_BTy_6 -> ()
d_'10214'_'10215''7495'_32 = erased
-- Once.Spec.Signature.NotEmpty
d_NotEmpty_42 :: T_BTy_6 -> ()
d_NotEmpty_42 = erased
-- Once.Spec.Signature.notEmpty?
d_notEmpty'63'_54 ::
  T_BTy_6 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_notEmpty'63'_54 v0
  = case coe v0 of
      C_unit_8
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      C_void_10
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_int_12
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      C_float_14
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      C__'42'__16 v1 v2
        -> coe
             du_both_64 (coe d_notEmpty'63'_54 (coe v1))
             (coe d_notEmpty'63'_54 (coe v2))
      C__'43'__18 v1 v2
        -> coe
             du_either_90 (coe d_notEmpty'63'_54 (coe v1))
             (coe d_notEmpty'63'_54 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature._.both
d_both_64 ::
  T_BTy_6 ->
  T_BTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_both_64 ~v0 ~v1 v2 v3 = du_both_64 v2 v3
du_both_64 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_both_64 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then case coe v3 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v4
                      -> case coe v1 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                             -> if coe v5
                                  then case coe v6 of
                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                           -> coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v4) (coe v7)))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  else coe
                                         seq (coe v6)
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe v5)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v3)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v2)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature._.either
d_either_90 ::
  T_BTy_6 ->
  T_BTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_either_90 ~v0 ~v1 v2 v3 = du_either_90 v2 v3
du_either_90 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_either_90 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then case coe v3 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v4
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe v2)
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then case coe v5 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                                       -> coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                               (coe
                                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                  (coe v6)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.DeclType
d_DeclType_106 = ()
data T_DeclType_106
  = C_constant_108 T_BTy_6 |
    C_value_110 T_BTy_6 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                T_BTy_6 |
    C_operation_112 T_BTy_6 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                    T_BTy_6
-- Once.Spec.Signature.Decl
d_Decl_114 = ()
data T_Decl_114
  = C__'8758'__124 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                   T_DeclType_106
-- Once.Spec.Signature.Decl.name
d_name_120 ::
  T_Decl_114 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_name_120 v0
  = case coe v0 of
      C__'8758'__124 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.Decl.type
d_type_122 :: T_Decl_114 -> T_DeclType_106
d_type_122 v0
  = case coe v0 of
      C__'8758'__124 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.Signature
d_Signature_126 :: ()
d_Signature_126 = erased
-- Once.Spec.Signature.OneName
d_OneName_128 :: [T_Decl_114] -> ()
d_OneName_128 = erased
-- Once.Spec.Signature.⌜_⌝ᵈ
d_'8988'_'8989''7496'_134 ::
  Integer -> T_DeclType_106 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_'8988'_'8989''7496'_134 ~v0 v1 = du_'8988'_'8989''7496'_134 v1
du_'8988'_'8989''7496'_134 ::
  T_DeclType_106 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_'8988'_'8989''7496'_134 v0
  = case coe v0 of
      C_constant_108 v1 -> coe du_'8988'_'8989'_22 (coe v1)
      C_value_110 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe du_'8988'_'8989'_22 (coe v1))
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v2)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
             (coe du_'8988'_'8989'_22 (coe v3))
      C_operation_112 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe du_'8988'_'8989'_22 (coe v1))
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v2)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
             (coe du_'8988'_'8989'_22 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.NotSingleton
d_NotSingleton_150 :: T_BTy_6 -> ()
d_NotSingleton_150 = erased
-- Once.Spec.Signature.EffCod
d_EffCod_160 :: T_BTy_6 -> ()
d_EffCod_160 = erased
-- Once.Spec.Signature.WellFormedDecl
d_WellFormedDecl_164 :: T_DeclType_106 -> ()
d_WellFormedDecl_164 = erased
-- Once.Spec.Signature.WellFormed
d_WellFormed_180 a0 = ()
data T_WellFormed_180
  = C_'91''93'_182 | C__'8759'__188 AgdaAny T_WellFormed_180
-- Once.Spec.Signature.argAt
d_argAt_190 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> T_BTy_6 -> T_BTy_6
d_argAt_190 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8 -> coe C_unit_8
      MAlonzo.Code.Once.Spec.Grade.C_One_10 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.Op
d_Op_200 a0 = ()
data T_Op_200
  = C_op_224 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 T_BTy_6
             MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_BTy_6
             MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
-- Once.Spec.Signature.Op.opName
d_opName_214 ::
  T_Op_200 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_opName_214 v0
  = case coe v0 of
      C_op_224 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.Op.dom
d_dom_216 :: T_Op_200 -> T_BTy_6
d_dom_216 v0
  = case coe v0 of
      C_op_224 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.Op.q
d_q_218 :: T_Op_200 -> MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
d_q_218 v0
  = case coe v0 of
      C_op_224 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.Op.ans
d_ans_220 :: T_Op_200 -> T_BTy_6
d_ans_220 v0
  = case coe v0 of
      C_op_224 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.Op.declared
d_declared_222 ::
  T_Op_200 -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_declared_222 v0
  = case coe v0 of
      C_op_224 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.arg
d_arg_228 :: T_Op_200 -> T_BTy_6
d_arg_228 v0
  = coe d_argAt_190 (coe d_q_218 (coe v0)) (coe d_dom_216 (coe v0))
-- Once.Spec.Signature.Layer
d_Layer_236 a0 a1 = ()
data T_Layer_236 = C_call_244 T_Op_200 AgdaAny (AgdaAny -> AgdaAny)
-- Once.Spec.Signature.Event
d_Event_246 = ()
data T_Event_246
  = C_event_260 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 T_BTy_6
                AgdaAny
-- Once.Spec.Signature.Event.ev-name
d_ev'45'name_254 ::
  T_Event_246 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_ev'45'name_254 v0
  = case coe v0 of
      C_event_260 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.Event.ev-arg
d_ev'45'arg_256 :: T_Event_246 -> T_BTy_6
d_ev'45'arg_256 v0
  = case coe v0 of
      C_event_260 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.Event.ev-val
d_ev'45'val_258 :: T_Event_246 -> AgdaAny
d_ev'45'val_258 v0
  = case coe v0 of
      C_event_260 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Signature.eventOf
d_eventOf_266 :: T_Op_200 -> AgdaAny -> T_Event_246
d_eventOf_266 v0 v1
  = coe
      C_event_260 (coe d_opName_214 (coe v0))
      (coe d_argAt_190 (coe d_q_218 (coe v0)) (coe d_dom_216 (coe v0)))
      (coe v1)
