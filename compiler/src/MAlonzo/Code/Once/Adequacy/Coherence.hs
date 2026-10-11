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

module MAlonzo.Code.Once.Adequacy.Coherence where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Adequacy.CoherenceHet
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Typing
import qualified MAlonzo.Code.Once.Spec.Typing.Scope
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.TypeCheck.Route

-- Once.Adequacy.Coherence._._≅_
d__'8773'__224 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.Coherence._._≅_.≅-sem
d_'8773''45'sem_352 ::
  MAlonzo.Code.Once.Adequacy.CoherenceHet.T__'8773'__382 -> AgdaAny
d_'8773''45'sem_352 = erased
-- Once.Adequacy.Coherence._._≅_.≅-ty
d_'8773''45'ty_354 ::
  MAlonzo.Code.Once.Adequacy.CoherenceHet.T__'8773'__382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'ty_354 = erased
-- Once.Adequacy.Coherence._._≅_.≅-us
d_'8773''45'us_356 ::
  MAlonzo.Code.Once.Adequacy.CoherenceHet.T__'8773'__382 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'us_356 = erased
-- Once.Adequacy.Coherence.RI
d_RI_358 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_RI_358 ~v0 = du_RI_358
du_RI_358 ::
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_RI_358
  = coe MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
-- Once.Adequacy.Coherence.RC
d_RC_360 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_RC_360 ~v0 = du_RC_360
du_RC_360 ::
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_RC_360 = coe MAlonzo.Code.Once.Denotation.Realize.d_realize_20
-- Once.Adequacy.Coherence.RD
d_RD_362 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_RD_362 ~v0 = du_RD_362
du_RD_362 ::
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_RD_362
  = coe MAlonzo.Code.Once.Denotation.Realize.d_realize'45'd_44
-- Once.Adequacy.Coherence.coh-ii
d_coh'45'ii_380 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Route.T_Rii_70 ->
  MAlonzo.Code.Once.Adequacy.CoherenceHet.T__'8773'__382
d_coh'45'ii_380 = erased
-- Once.Adequacy.Coherence.coh-cc
d_coh'45'cc_396 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Route.T_Rcc_82 ->
  MAlonzo.Code.Once.Adequacy.CoherenceHet.T__'8773'__382
d_coh'45'cc_396 = erased
-- Once.Adequacy.Coherence.coh-ic
d_coh'45'ic_416 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Route.T_Ric_96 ->
  MAlonzo.Code.Once.Spec.Type.Sub.T__'60''58'__20 ->
  MAlonzo.Code.Once.Adequacy.CoherenceHet.T__'8773'__382
d_coh'45'ic_416 = erased
-- Once.Adequacy.Coherence.coh-dc
d_coh'45'dc_440 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Route.T_Rdc_114 ->
  MAlonzo.Code.Once.Spec.Type.Sub.T__'60''58'__20 ->
  MAlonzo.Code.Once.Adequacy.CoherenceHet.T__'8773'__382
d_coh'45'dc_440 = erased
-- Once.Adequacy.Coherence.coh-di
d_coh'45'di_472 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Route.T_Rdi_138 ->
  MAlonzo.Code.Once.Spec.Type.Sub.T__'60''58'__20 ->
  MAlonzo.Code.Once.Spec.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceHet.T__'8773'__382
d_coh'45'di_472 = erased
-- Once.Adequacy.Coherence.coh-dd
d_coh'45'dd_494 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Route.T_Rdd_156 ->
  MAlonzo.Code.Once.Adequacy.CoherenceHet.T__'8773'__382
d_coh'45'dd_494 = erased
-- Once.Adequacy.Coherence.realize-invariant
d_realize'45'invariant_1104 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_realize'45'invariant_1104 = erased
