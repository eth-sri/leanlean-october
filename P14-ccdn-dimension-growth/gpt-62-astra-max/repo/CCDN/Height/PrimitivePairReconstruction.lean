/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! A primitive coordinate pair generates the function field over the constant
field. Every finite family of functions then has polynomial reconstruction
identities with one nonzero denominator. No bound on its degree is asserted. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A generating polynomial tuple expresses any field element as a quotient
with a nonzero evaluated denominator. -/
lemma adjoin_top_polynomial_fraction {K F σ : Type*} [Field K] [Field F] [Algebra K F]
    (a : σ → F) (ha : IntermediateField.adjoin K (Set.range a) = ⊤) (x : F) :
    ∃ r s : MvPolynomial σ K, aeval a s ≠ 0 ∧ x = aeval a r / aeval a s := by
  by_cases hx : x = 0
  · exact ⟨0, 1, by simp, by simp [hx]⟩
  obtain ⟨r, s, he⟩ := (IntermediateField.mem_adjoin_range_iff K a x).mp
    (by rw [ha]; trivial)
  refine ⟨r, s, ?_, he⟩
  intro hs
  apply hx
  rw [he, hs, div_zero]

end
end CCDN
