/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.ForMathlib.StandardExponents
public import CCDN.Hilbert.FilteredIntersection
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.StandardMonomials

/-! Finiteness of bounded standard-exponent families. -/

@[expose] public section
namespace CCDN
open MvPolynomial

/-- Bounded exponent sets are finite. -/
noncomputable instance finite_boundedStandardExponents {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (N : ℕ) :
    Finite (Ideal.boundedStandardExponents I m N) := by
  classical
  let e := Finsupp.degreeLeEquivSym σ N
  let f : Ideal.boundedStandardExponents I m N → Sym (Option σ) N :=
    fun a => e ⟨a.val, a.property.2⟩
  apply Finite.of_injective f
  intro a b h
  have he := e.injective h
  apply Subtype.ext
  simp_all

end CCDN
