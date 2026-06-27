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

module MAlonzo.Code.Once.Grammar.ImportBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Import
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Grammar.ImportBridge.wordHead
d_wordHead_6 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
d_wordHead_6 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_is'45'just_20
      (coe MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118 (coe v0))
-- Once.Grammar.ImportBridge.pmp-dot≢nothing
d_pmp'45'dot'8802'nothing_24 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_pmp'45'dot'8802'nothing_24 = erased
-- Once.Grammar.ImportBridge.pmp-tail≢nothing
d_pmp'45'tail'8802'nothing_60 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_pmp'45'tail'8802'nothing_60 = erased
-- Once.Grammar.ImportBridge.mp-nothing→aw
d_mp'45'nothing'8594'aw_86 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mp'45'nothing'8594'aw_86 = erased
-- Once.Grammar.ImportBridge.mp-nothing→wh-false
d_mp'45'nothing'8594'wh'45'false_120 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mp'45'nothing'8594'wh'45'false_120 = erased
-- Once.Grammar.ImportBridge.wh-false→nothing
d_wh'45'false'8594'nothing_132 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wh'45'false'8594'nothing_132 = erased
-- Once.Grammar.ImportBridge.ParsesModulePath
d_ParsesModulePath_160 a0 a1 a2 = ()
data T_ParsesModulePath_160
  = C_pmp'45'cons_170 T_ParsesModulePath_160 | C_pmp'45'dotfail_176 |
    C_pmp'45'nodot_182
-- Once.Grammar.ImportBridge.sound-mpWF
d_sound'45'mpWF_194 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ParsesModulePath_160
d_sound'45'mpWF_194 v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'mpWF_194 v0
du_sound'45'mpWF_194 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesModulePath_160
du_sound'45'mpWF_194 v0
  = case coe v0 of
      (:) v1 v2
        -> coe
             seq (coe v1)
             (let v3
                    = MAlonzo.Code.Once.Parser.Module.Import.d_dotHead_18 (coe v2) in
              coe
                (if coe v3
                   then let v4
                              = coe
                                  MAlonzo.Code.Once.Parser.Module.Import.du_parseModulePath'45'WFB_22
                                  (coe
                                     MAlonzo.Code.Once.Parser.Module.Import.d_dropDot_8 (coe v2)) in
                        coe
                          (case coe v4 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                               -> case coe v5 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                      -> coe
                                           seq (coe v7)
                                           (coe
                                              C_pmp'45'cons_170
                                              (coe
                                                 du_sound'45'mpWF_194
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Import.d_dropDot_8
                                                    (coe v2))))
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> coe C_pmp'45'dotfail_176
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else coe C_pmp'45'nodot_182))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ImportBridge.sound-mp
d_sound'45'mp_342 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ParsesModulePath_160
d_sound'45'mp_342 v0 ~v1 ~v2 ~v3 ~v4 = du_sound'45'mp_342 v0
du_sound'45'mp_342 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesModulePath_160
du_sound'45'mp_342 v0 = coe du_sound'45'mpWF_194 (coe v0)
-- Once.Grammar.ImportBridge.complete-mpWF
d_complete'45'mpWF_358 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  T_ParsesModulePath_160 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'mpWF_358 v0 v1 v2 ~v3 v4
  = du_complete'45'mpWF_358 v0 v1 v2 v4
du_complete'45'mpWF_358 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesModulePath_160 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'mpWF_358 v0 v1 v2 v3
  = case coe v3 of
      C_pmp'45'cons_170 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    (:) v12 v13
                      -> let v14
                               = coe
                                   du_complete'45'mpWF_358
                                   (coe
                                      MAlonzo.Code.Once.Parser.Module.Import.d_dropDot_8 (coe v11))
                                   (coe v13) (coe v2) (coe v9) in
                         coe
                           (case coe v14 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                        (coe
                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                           (coe
                                              (\ v17 v18 -> addInt (coe (1 :: Integer)) (coe v18)))
                                           (coe (0 :: Integer))
                                           (coe
                                              MAlonzo.Code.Once.Parser.Module.Import.d_dropDot_8
                                              (coe v11)))
                                        (coe v15)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                           (coe
                                              MAlonzo.Code.Once.Parser.Module.Import.d_dropDot'45''8804'_14
                                              (coe v11))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                 (coe
                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                    (let v17
                                                           = \ v17 ->
                                                               addInt
                                                                 (coe (1 :: Integer)) (coe v17) in
                                                     coe (coe (\ v18 -> v17)))
                                                    (coe (0 :: Integer)) (coe v11))))))
                                     erased
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pmp'45'dotfail_176
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe (\ v8 v9 -> addInt (coe (1 :: Integer)) (coe v9)))
                      (coe (0 :: Integer)) (coe v2))))
             erased
      C_pmp'45'nodot_182
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe (\ v7 v8 -> addInt (coe (1 :: Integer)) (coe v8)))
                      (coe (0 :: Integer)) (coe v2))))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ImportBridge.complete-mp
d_complete'45'mp_434 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesModulePath_160 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'mp_434 v0 v1 v2 v3
  = coe du_complete'45'mpWF_358 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Grammar.ImportBridge.anyWordB-inv
d_anyWordB'45'inv_448 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anyWordB'45'inv_448 = erased
-- Once.Grammar.ImportBridge.ij-false
d_ij'45'false_454 ::
  () ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ij'45'false_454 = erased
-- Once.Grammar.ImportBridge.ParsesImportAlias
d_ParsesImportAlias_458 a0 a1 a2 a3 = ()
data T_ParsesImportAlias_458
  = C_pia'45'alias'45'r_466 | C_pia'45'neq'45'r_472 |
    C_pia'45'nonword'45'r_476
-- Once.Grammar.ImportBridge.sound-alias
d_sound'45'alias_488 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ParsesImportAlias_458
d_sound'45'alias_488 ~v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'alias_488 v1
du_sound'45'alias_488 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesImportAlias_458
du_sound'45'alias_488 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7
                                  = coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v7 ->
                                         coe
                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                           (coe v3))
                                      (coe
                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                         (coe v3) (coe ("as" :: Data.Text.Text))) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                   -> if coe v8
                                        then coe
                                               seq (coe v9)
                                               (let v10
                                                      = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                                          (coe v5) in
                                                coe
                                                  (case coe v10 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                              -> coe
                                                                   seq (coe v13)
                                                                   (coe C_pia'45'alias'45'r_466)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                        else coe seq (coe v9) (coe C_pia'45'neq'45'r_472)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_pia'45'nonword'45'r_476
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Grammar.ImportBridge.complete-alias
d_complete'45'alias_650 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesImportAlias_458 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'alias_650 ~v0 v1 ~v2 v3 v4
  = du_complete'45'alias_650 v1 v3 v4
du_complete'45'alias_650 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesImportAlias_458 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'alias_650 v0 v1 v2
  = case coe v2 of
      C_pia'45'alias'45'r_466
        -> case coe v0 of
             (:) v5 v6
               -> case coe v6 of
                    (:) v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_length_268
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7)
                                       (coe v1)))
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (let v9 = \ v9 -> addInt (coe (1 :: Integer)) (coe v9) in
                                           coe (coe (\ v10 -> v9)))
                                          (coe (0 :: Integer)) (coe v1))))
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (let v9 = \ v9 -> addInt (coe (1 :: Integer)) (coe v9) in
                                           coe (coe (\ v10 -> v9)))
                                          (coe (0 :: Integer))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7)
                                             (coe v1)))))))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pia'45'neq'45'r_472
        -> case coe v0 of
             (:) v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Parser.Token.C_TWord_8 v8
                      -> let v9
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v9 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v8))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v8)
                                      (coe ("as" :: Data.Text.Text))) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                -> if coe v10
                                     then coe
                                            seq (coe v11)
                                            (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                     else coe
                                            seq (coe v11)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                  (coe
                                                     addInt (coe (1 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                        (coe
                                                           (\ v12 v13 ->
                                                              addInt
                                                                (coe (1 :: Integer)) (coe v13)))
                                                        (coe (0 :: Integer)) (coe v7))))
                                               erased)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_pia'45'nonword'45'r_476
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (coe (\ v5 v6 -> addInt (coe (1 :: Integer)) (coe v6)))
                   (coe (0 :: Integer)) (coe v0)))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ImportBridge.ParsesImport
d_ParsesImport_690 a0 a1 a2 = ()
data T_ParsesImport_690
  = C_pi'45'mk_702 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                   [MAlonzo.Code.Once.Parser.Token.T_Token_6] T_ParsesModulePath_160
                   T_ParsesImportAlias_458
-- Once.Grammar.ImportBridge.sound-import
d_sound'45'import_712 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ParsesImport_690
d_sound'45'import_712 v0 ~v1 ~v2 ~v3 ~v4
  = du_sound'45'import_712 v0
du_sound'45'import_712 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_ParsesImport_690
du_sound'45'import_712 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Parser.Module.Import.du_pmp'45'aw_32
              (coe
                 MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7
                                  = MAlonzo.Code.Once.Parser.Module.Import.d_pia'45'head_162
                                      (coe v3) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                         (coe v5)) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               seq (coe v10)
                                               (coe
                                                  C_pi'45'mk_702 v3 v5
                                                  (coe du_sound'45'mp_342 (coe v0))
                                                  (coe du_sound'45'alias_488 (coe v5)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Grammar.ImportBridge.complete-import
d_complete'45'import_790 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesImport_690 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'import_790 v0 ~v1 v2 v3
  = du_complete'45'import_790 v0 v2 v3
du_complete'45'import_790 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesImport_690 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'import_790 v0 v1 v2
  = case coe v2 of
      C_pi'45'mk_702 v4 v5 v8 v9
        -> let v10
                 = coe
                     du_complete'45'mpWF_358 (coe v0) (coe v4) (coe v5) (coe v8) in
           coe
             (case coe v10 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                  -> let v13
                           = coe du_complete'45'alias_650 (coe v5) (coe v1) (coe v9) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                    (coe v14) (coe v11))
                                 erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
