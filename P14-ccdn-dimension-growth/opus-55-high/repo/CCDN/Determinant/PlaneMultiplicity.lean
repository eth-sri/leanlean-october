/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.SingularPlaneChart

/-! Positive singular multiplicity is derived from a nonzero equation
vanishing at the origin; it is bounded by the equation's total degree. -/

namespace CCDN
section
open MvPolynomial

/-- The first nonzero homogeneous component realizes the order at the origin. -/
theorem exists_origin_multiplicity {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hz : eval (0 : σ → K) f = 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      f ∈ idealOfVars σ K ^ μ ∧ homogeneousComponent μ f ≠ 0 := by
  classical
  have hex : ∃ n, homogeneousComponent n f ≠ 0 := by
    by_contra h
    apply hf
    rw [← sum_homogeneousComponent f]
    simp_all
  let μ := Nat.find hex
  have hμ := Nat.find_spec hex
  have hdeg : μ ≤ f.totalDegree := by
    by_contra h
    exact hμ (homogeneousComponent_eq_zero μ f (by omega))
  exact ⟨μ, (by aesop), hdeg, (by
    rw [mem_pow_idealOfVars_iff']
    intro e he
    have hzero :=
      not_not.mp (Nat.find_min hex he)
    have hc := congrArg (fun u => u.coeff e) hzero
    simpa [coeff_homogeneousComponent] using hc), hμ⟩

/-- Substituting affine linear polynomials does not increase total degree. -/
theorem linear_eval₂_totalDegree_le {R S σ τ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : σ → MvPolynomial τ S) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (f : MvPolynomial σ R) :
    (eval₂Hom (C.comp φ) g f).totalDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial, RingHom.comp_apply]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  calc _ ≤ ∑ j ∈ e.support, (g j ^ e j).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ j ∈ e.support, e j := by
      apply Finset.sum_le_sum
      intro j _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (e j) (hg j))
    _ ≤ f.totalDegree := le_totalDegree he

/-- A reduced hypersurface point determines a positive, degree-bounded
multiplicity in every ambient dimension. -/
theorem exists_hypersurface_reduction_multiplicity {p : ℕ} [Fact p.Prime] {σ : Type*}
    (f : MvPolynomial σ ℤ) (a : σ → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      map (Int.castRingHom (ZMod p)) (originShift a f) ∈ idealOfVars σ (ZMod p) ^ μ ∧
      homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0 := by
  let φ := Int.castRingHom (ZMod p)
  have hshift := originShift_map φ a f
  have hz : eval (0 : σ → ZMod p) (map φ (originShift a f)) = 0 := by
    rwa [hshift, eval_zero_originShift, eval_map]
  have he : map φ (originShift a f) =
      eval₂Hom (C.comp φ) (fun j => X j + C (φ (a j))) f := by
    rw [hshift]
    exact eval₂Hom_map_hom φ _ C f
  obtain ⟨μ, hpos, hμdeg, hpow, hμ⟩ := exists_origin_multiplicity _ (by
    rw [hshift]
    exact (map_ne_zero_iff _ (show Function.Injective (originShift _) from Function.LeftInverse.injective (originShift_neg _))).2 hf) hz
  exact ⟨μ, hpos, hμdeg.trans (by
    rw [he]
    apply linear_eval₂_totalDegree_le
    intro j
    exact (totalDegree_add _ _).trans
      (max_le (le_of_eq (totalDegree_X _)) (by rw [totalDegree_C]; omega))), hpow, hμ⟩

