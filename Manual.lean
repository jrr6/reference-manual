/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

-- import Manual.Intro
-- import Manual.Elaboration
-- import Manual.Types
-- import Manual.SourceFiles
-- import Manual.Attributes
-- import Manual.Defs
-- import Manual.Classes
-- import Manual.Axioms
-- import Manual.Terms
import Manual.ErrorExplanations
-- import Manual.Tactics
-- import Manual.Simp
import Manual.BasicTypes
-- import Manual.BasicProps
-- import Manual.NotationsMacros
-- import Manual.IO
-- import Manual.Interaction
-- import Manual.Monads
-- import Manual.BuildTools
-- import Manual.Releases
-- import Manual.Namespaces
-- import Manual.Runtime

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxRecDepth 1024

#doc (Manual) "The Lean Language Reference" =>
%%%
tag := "lean-language-reference"
%%%

This is the _Lean Language Reference_.
It is intended to be a comprehensive, precise description of Lean: a reference work in which Lean users can look up detailed information, rather than a tutorial intended for new users.
For other documentation, please refer to the [Lean documentation overview](https://lean-lang.org/documentation/).
This manual covers Lean version {versionString}[].

Lean is an *interactive theorem prover* based on dependent type theory, designed for use both in cutting-edge mathematics and in software verification.
Lean's core type theory is expressive enough to capture very complicated mathematical objects, but simple enough to admit independent implementations, reducing the risk of bugs that affect soundness.
The core type theory is implemented in a minimal {tech}[kernel] that does nothing other than check proof terms.
This core theory and kernel are supported by advanced automation, realized in {ref "tactics"}[an expressive tactic language].
Each tactic produces a term in the core type theory that is checked by the kernel, so bugs in tactics do not threaten the soundness of Lean as a whole.
Along with many other parts of Lean, the tactic language is user-extensible, so it can be built up to meet the needs of a given formalization project.
Tactics are written in Lean itself, and can be used immediately upon definition; rebuilding the prover or loading external modules is not required.

Lean is also a pure *functional programming language*, with features such as a run-time system based on reference counting that can efficiently work with packed array structures, multi-threading, and monadic {name}`IO`.
As befits a programming language, Lean is primarily implemented in itself, including the language server, build tool, {tech}[elaborator], and tactic system.
This very book is written in [Verso](https://github.com/leanprover/verso), a documentation authoring tool written in Lean.

Familiarity with Lean's programming features is valuable even for users whose primary interest is in writing proofs, because Lean programs are used to implement new tactics and proof automation.
Thus, this reference manual does not draw a barrier between the two aspects, but rather describes them together so they can shed light on one another.


{include 0 Manual.BasicTypes}

{include 0 Manual.ErrorExplanations}
