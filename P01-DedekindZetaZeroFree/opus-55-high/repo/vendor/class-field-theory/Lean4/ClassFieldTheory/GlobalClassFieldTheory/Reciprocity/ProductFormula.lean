module

public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteLocalFamily
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The local--global norm-symbol bridge

This file isolates the exact quotient calculation used by the Hilbert-symbol
product formula.  The one-place embedding sends the chosen local norm group
directly into the ordinary idele-class norm group, so it descends without an
intermediate raw-idele quotient.  The resulting character identity gives the
finite-support and
principal-idèle product identities for every character of that target.
-/

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

theorem productFormulaIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply RelativeIdeleGroup.Cohomology.ideleClassNormQuotient_baseIsMulCommutative <;> assumption

attribute [local instance] productFormulaIdeleClassGroupIsMulCommutative
