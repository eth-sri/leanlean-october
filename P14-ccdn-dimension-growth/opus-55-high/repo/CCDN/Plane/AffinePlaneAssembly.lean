/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Plane.AffineNonzeroConstant
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.ForMathlib.Log

/-! All affine scaling, coefficient-height and zero-constant-term reductions
for primitive absolutely irreducible plane equations. The resulting bound
assumes the sharp finite-field estimate. -/

namespace CCDN
section
open MvPolynomial Real

lemma curveBound_translation_radius {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    curveBound d (((d : ℝ) + 1) * B) ≤ 2 * Real.exp 1 * curveBound d B := by
  have hB0 : 0 < B := by linarith
  have hdplus : (0 : ℝ) < d + 1 := by positivity
  have hlogB := Real.log_nonneg hB
  have hlogd := Real.log_add_one_le_self d.cast_nonneg
  have hpow : ((d : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hdplus, mul_one_div]
    apply Real.exp_le_exp.mpr
    exact (div_le_one (mod_cast hd)).mpr hlogd
  have hlog : Real.log ((d + 1) * B) + d ≤ 2 * (Real.log B + d) := by
    rw [Real.log_mul hdplus.ne' hB0.ne']
    linarith
  unfold curveBound
  rw [Real.mul_rpow hdplus.le hB0.le]
  have hh := mul_le_mul hpow hlog
    (by
      have hR : 1 ≤ (d + 1) * B := one_le_mul_of_one_le_of_one_le (by linarith) hB
      have := Real.log_nonneg hR
      positivity)
    (Real.exp_pos 1).le
  have ht := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) by positivity)
  convert ht using 1 <;> ring

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f) (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) (hd : 0 < f.totalDegree) {B C : ℝ}
include hprim hir hd

/-- Coefficient-uniform point count for a primitive absolutely irreducible
integer plane equation, assuming the sharp finite-field point estimate at
primes above 27*d^4. -/
theorem plane_finite_count_of_residue_bound
    {t : ℕ}
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z) (hzB : IsBoxZeroFamily f B z)
    (hC : 0 ≤ C) (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤ (2 * Real.exp 1 * affineNonzeroConstantBound C) * curveBound f.totalDegree B := by
  obtain ⟨hB, hz, hbox⟩ := hzB
  obtain ⟨a, ha, ha0⟩ : ∃ a : Fin 2 → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      (affineTranslation ℤ a f).coeff 0 ≠ 0 := by
    obtain ⟨a, ha, hn, _⟩ := exists_integer_multivariate_grid_height_witness f (fun h => hir.ne_zero (by grind)) le_rfl
    exact ⟨a, ha, by rwa [affineTranslation_constantCoeff]⟩
  let q := affineTranslation ℤ a f
  let z' : Fin t → Fin 2 → ℤ := fun i => z i - a
  let R := (f.totalDegree + 1) * B
  have hdeg := affineTranslation_totalDegree a f
  have hprimq := hprim.translate_affine a
  have hirq : Irreducible (MvPolynomial.map (Int.castRingHom F) q) := by
    rwa [affineTranslation_map, affineTranslation_irreducible_iff]
  have hinj' : Function.Injective z' := by
    intro i j hij
    grind
  have hz' : ∀ i, eval (z' i) q = 0 := by
    intro i
    rw [affineTranslation_eval, sub_add_cancel]
    grind
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le
    (by grind) hB
  have hbox' : ∀ i j, |(z' i j : ℝ)| ≤ R := by
    intro i j
    exact homogeneousTranslation_integer_point_box hB a (z i) ha (hbox i) j
  have hcount' : PlaneResidueCountBound C q.totalDegree q := by
    intro ℓ hℓ hsize hirℓ
    rw [hdeg] at hsize ⊢
    rw [show Nat.card (PlaneResidue q ℓ) = Nat.card (PlaneResidue f ℓ) from
      Nat.card_congr (affineTranslationResidueEquiv a f ℓ)]
    exact hcount ℓ hℓ hsize (by
      rwa [affineTranslation_map, affineTranslation_irreducible_iff] at hirℓ)
  have hh := plane_finite_count_nonzero_constant q hprimq hirq (by rwa [hdeg]) ha0 z' hinj'
    ⟨hR, hz', hbox'⟩ hC hcount'
  rw [hdeg] at hh
  have ht := hh.trans (mul_le_mul_of_nonneg_left (curveBound_translation_radius hd hB)
    (affineNonzeroConstantBound_pos C).le)
  convert ht using 1
  ring

/-- For a primitive absolutely irreducible integer plane equation, the number of integer
zeros of height at most a real `B ≥ 1` is bounded by a constant multiple of `curveBound`,
assuming the finite-field point estimate `p + C d² √p` at primes above `27 d⁴`. -/
theorem count_plane_of_residue_bound
    (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      (2 * Real.exp 1 * affineNonzeroConstantBound C) * curveBound f.totalDegree B := by
  apply integer_zero_count_le_of_family_bound
  intro t z hinj hz hbox
  exact plane_finite_count_of_residue_bound f hprim hir hd z hinj ⟨hB, hz, hbox⟩ hC hcount

