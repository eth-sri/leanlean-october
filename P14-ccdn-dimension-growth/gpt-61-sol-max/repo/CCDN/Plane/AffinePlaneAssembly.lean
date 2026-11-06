/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Plane.AffineNonzeroConstant
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.ForMathlib.Log

/-! All affine scaling, coefficient-height and zero-constant-term reductions
for primitive absolutely irreducible plane equations. The resulting bound
assumes the sharp finite-field estimate. -/

public section
namespace CCDN
open MvPolynomial Real

private lemma curveBound_translation_radius {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    curveBound d ((↑d + 1) * B) ≤ 2 * Real.exp 1 * curveBound d B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hB0 : 0 < B := by linarith
  have hdplus : (0 : ℝ) < d + 1 := by positivity
  have hlogB := Real.log_nonneg hB
  have hlogd := Real.log_add_one_le_self d.cast_nonneg
  have hpow : (↑d + 1) ^ (1 / (d : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hdplus, mul_one_div]
    apply Real.exp_le_exp.mpr
    exact (div_le_one hd0).mpr hlogd
  have hlog : Real.log ((↑d + 1) * B) + d ≤ 2 * (Real.log B + d) := by
    grind [Real.log_mul]
  unfold curveBound
  rw [Real.mul_rpow hdplus.le hB0.le]
  have hh := mul_le_mul hpow hlog
    (by
      grind [one_le_mul_of_one_le_of_one_le, Real.log_nonneg])
    (Real.exp_pos 1).le
  have ht := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ ↑d ^ 3 * B ^ (1 / (d : ℝ)) by positivity)
  convert ht using 1 <;> ring

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]


/-- For a primitive absolutely irreducible integer plane equation, the number of integer
zeros of height at most a real `B ≥ 1` is bounded by a constant multiple of `curveBound`,
assuming the finite-field point estimate `p + C d² √p` at primes above `27 d⁴`. -/
theorem count_plane_of_residue_bound
    
    (f : CCDN.IntegerPolynomial 2) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) (hd : 0 < f.totalDegree)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (count (zeroLocus (CCDN.rationalPolynomial f)) B : ℝ) ≤
      (2 * Real.exp 1 * affineNonzeroConstantBound C) * curveBound f.totalDegree B := by
  apply integer_zero_count_le_of_family_bound
  intro t z hinj hz hbox
  exact (show ↑t ≤ (2 : ℝ) * rexp (1 : ℝ) * affineNonzeroConstantBound C * curveBound (totalDegree f) B from (by
          let inline_hzB : IsBoxZeroFamily f B z := { one_le_radius := hB, eval_eq_zero := hz, abs_le := hbox }
          obtain ⟨hB, hz, hbox⟩ := inline_hzB
          have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
          obtain ⟨a, ha, ha0⟩ := exists_bounded_translation_nonzero_constant f hf0
          let q := affineTranslation ℤ a f
          let z' := fun i => z i - a
          let R := (↑f.totalDegree + 1) * B
          have hdeg := affineTranslation_totalDegree a f
          have hprimq := hprim.translate_affine a
          have hirq : Irreducible (MvPolynomial.map (Int.castRingHom F) q) := by
            grind [affineTranslation_map, affineTranslation_irreducible_iff]
          have hinj' : Function.Injective z' := by
            intro i j hij
            apply hinj
            have hh := congrArg (fun v : CCDN.IntPoint 2 => v + a) hij
            simpa only [z', sub_add_cancel] using hh
          have hz' : ∀ i, eval (z' i) q = 0 := by
            grind [affineTranslation_eval, sub_add_cancel]
          have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le
            (by simp_all) hB
          have hbox' : ∀ i j, |(z' i j : ℝ)| ≤ R := by
            solve_by_elim [homogeneousTranslation_integer_point_box]
          have hcount' : PlaneResidueCountBound C q.totalDegree q := by
            intro ℓ hℓ hsize hirℓ
            rw [hdeg] at hsize ⊢
            have hirf : Irreducible (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) := by
              grind [affineTranslation_map, affineTranslation_irreducible_iff]
            rw [(affineTranslation_residue_card a f ℓ)]
            exact hcount ℓ hℓ hsize hirf
          have hh := plane_finite_count_nonzero_constant q hprimq hirq (by rwa [hdeg]) ha0 z' hinj'
            ⟨hR, hz', hbox'⟩ hC hcount'
          rw [hdeg] at hh
          have ht := hh.trans (mul_le_mul_of_nonneg_left (curveBound_translation_radius hd hB)
            (affineNonzeroConstantBound_pos C).le)
          convert ht using 1
          ring))

end CCDN
