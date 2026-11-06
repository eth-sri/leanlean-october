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

public section
namespace CCDN
open MvPolynomial

/-- A generating polynomial tuple expresses any field element as a quotient
with a nonzero evaluated denominator. -/
lemma adjoin_top_polynomial_fraction {K F σ : Type*} [Field K] [Field F] [Algebra K F]
    (a : σ → F) (ha : IntermediateField.adjoin K (Set.range a) = ⊤) (x : F) :
    ∃ r s : MvPolynomial σ K, x = aeval a r / aeval a s := by
  exact (IntermediateField.mem_adjoin_range_iff K a x).mp (by rw [ha]; trivial)

end CCDN
