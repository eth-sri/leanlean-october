/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.SingularPlaneChart

/-! Positive singular multiplicity is derived from a nonzero equation
vanishing at the origin; it is bounded by the equation's total degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/- The first nonzero homogeneous component realizes the order at the origin. -/

/-- Substituting affine linear polynomials does not increase total degree. -/
theorem linear_eval₂_totalDegree_le {R S σ τ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : σ → MvPolynomial τ S) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (f : MvPolynomial σ R) :
    (eval₂Hom (C.comp φ) g f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial, RingHom.comp_apply]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  change (∏ j ∈ e.support, g j ^ e j).totalDegree ≤ f.totalDegree
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
  classical
  let φ := Int.castRingHom (ZMod p)
  let g := map φ (originShift a f)
  have hshift := originShift_map φ a f
  have hn : g ≠ 0 := by dsimp [g]; rw [hshift]; exact originShift_ne_zero _ hf
  have hz : eval (0 : σ → ZMod p) g = 0 := by
    rw [show g = _ from hshift, eval_zero_originShift, eval_map]; exact ha
  have hdeg : g.totalDegree ≤ f.totalDegree := by
    rw [show g = eval₂Hom (C.comp φ) (fun j => X j + C (φ (a j))) f from
      hshift.trans (eval₂Hom_map_hom φ _ C f)]
    exact linear_eval₂_totalDegree_le φ _ (fun j => (totalDegree_add _ _).trans
      (max_le (le_of_eq (totalDegree_X _)) (by rw [totalDegree_C]; omega))) f
  have hex : ∃ n, homogeneousComponent n g ≠ 0 := by
    by_contra! h
    exact hn (by rw [← sum_homogeneousComponent g]; simp only [h, Finset.sum_const_zero])
  let μ := Nat.find hex
  have hμ : homogeneousComponent μ g ≠ 0 := Nat.find_spec hex
  refine ⟨μ, ?_, (show μ ≤ g.totalDegree by
      by_contra h; exact hμ (homogeneousComponent_eq_zero μ g (by omega))).trans hdeg,
    (mem_pow_idealOfVars_iff' _ _).mpr fun e he => by
      simpa [coeff_homogeneousComponent] using
        congrArg (fun u : MvPolynomial σ (ZMod p) => u.coeff e) (not_not.mp (Nat.find_min hex he)),
    hμ⟩
  by_contra h
  have hconst : g.coeff 0 = 0 := by simpa only [eval_zero, constantCoeff_eq] using hz
  exact hμ (by rw [show μ = 0 by omega, homogeneousComponent_zero, hconst, map_zero])

end
end CCDN
