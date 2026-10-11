-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec — the definition of the Once language.
--
-- The Spec is the modules under `Once/Spec`. This module is their index, in
-- reading order. It defines nothing and re-exports nothing: a name is
-- imported from the module that defines it.
--
-- Everything else (the parser, the elaborator, the IR, code generation, the
-- machine models and every soundness or completeness proof) is the
-- implementation. It is checked against the Spec and never trusted in its
-- place.
--
-- A program is a morphism of the free cartesian closed category on a
-- signature Σ. Its `signature` declarations are the generators of Σ, and its
-- definitions are built from them. That gives three separate times:
--   * building the compiler: `correct` is proved once, for every
--     implementation of every signature (`CorrectCompiler`);
--   * compiling a program: Σ is a function of the program;
--   * implementing an interpretation: an `Impl` of the program's signature,
--     provided by its author without the compiler (`Once.Spec.Contract`).
------------------------------------------------------------------------

module Once.Spec where

-- What you may write.
import Once.Spec.Type         -- types
import Once.Spec.Syntax       -- terms, as written and as resolved
import Once.Spec.Lexing       -- text to tokens
import Once.Spec.Parsing      -- tokens to a module
import Once.Spec.Resolution   -- what each written reference denotes
import Once.Spec.Typing       -- the typing judgment

-- What it means.
import Once.Spec.Meaning      -- the denotation
import Once.Spec.Contract     -- what an interpretation owes
import Once.Spec.Program      -- what a typed program is

-- What a correct compiler is.
import Once.Spec.Correct

-- What the language promises about itself.
import Once.Spec.Metatheory
