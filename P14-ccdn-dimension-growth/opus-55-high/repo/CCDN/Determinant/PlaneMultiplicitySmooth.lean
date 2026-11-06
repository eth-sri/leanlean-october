/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.SingularReduction
import CCDN.Determinant.PlaneSingularities

/-! Multiplicity greater than one forces a singular point. -/

namespace CCDN
section
open MvPolynomial

section
variable {K σ : Type*} [Field K] {μ : ℕ}

/-- Only singular points can have local order at least two. -/
theorem singular_of_origin_order_ge_two
    (f : MvPolynomial σ K) (a : σ → K) (hμ : 2 ≤ μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ) :
    ∀ j, eval a (pderiv j f) = 0 := by
  intro j
  rw [← eval_zero_originShift, ← pderiv_originShift]
  rw [mem_pow_idealOfVars_iff'] at hf
  have hc := hf (Finsupp.single j 1)
    (by aesop)
  simpa [eval_zero, constantCoeff_eq, coeff_pderiv, zero_add,
    Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add, mul_one] using hc

/-- In particular, every positive order at a smooth point is one. -/
theorem origin_order_eq_one_of_smooth
    (f : MvPolynomial σ K) (a : σ → K) (hμ : 0 < μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ)
    (hs : ∃ j, eval a (pderiv j f) ≠ 0) : μ = 1 := by
  by_contra h
  obtain ⟨j, hj⟩ := hs
  exact hj (singular_of_origin_order_ge_two f a (by omega) hf j)

end

variable {p : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin 2) ℤ)

lemma planeResidueMultiplicity_singular
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (a : PlaneResidue f p) (ha : 2 ≤ planeResidueMultiplicity f p hf a) :
    ∀ j, eval a.val (pderiv j (map (Int.castRingHom (ZMod p)) f)) = 0 := by
  have hp := (planeResidueMultiplicity_spec f p hf a).2.2.1
  rw [originShift_map] at hp
  have he : (fun j => (Int.castRingHom (ZMod p)) (planeResidueLift a j)) = a.val := by
    funext j
    exact cast_planeResidueLift a j
  rw [he] at hp
  exact singular_of_origin_order_ge_two _ a.val ha hp

