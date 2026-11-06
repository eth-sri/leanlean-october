/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import CCDN.ClassGroup.NumberFieldLatticeBox
import CCDN.ClassGroup.OddDegreeNormCurveCount

/-! The odd-degree class-group counting step uses the finite
translation classes and their two signed norm curves. The curve equation
retains its full odd degree, including when the translating generator
belongs to a proper subfield. -/

namespace CCDN
section
open NumberField NumberField.InfinitePlace

/-- For `n ≥ 2` and `B ≥ 1`, the norm-curve box height `H = max (2 * B) (√(B ^ n))` satisfies
`H ^ (1 / n) ≤ 2 * √B`. -/
lemma normCurveBoxHeight_root_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    (max (2 * B) (Real.sqrt (B ^ n))) ^ (1 / (n : ℝ)) ≤ 2 * Real.sqrt B := by
  have hB0 := zero_le_one.trans hB
  have hs : 1 ≤ Real.sqrt B := by simp_all
  have hbase : 1 ≤ 2 * Real.sqrt B := by linarith
  have hsquare : (2 * Real.sqrt B) ^ 2 = 4 * B := by grind
  have hpower :=
    pow_le_pow_right₀ hbase hn
  have hH : max (2 * B) (Real.sqrt (B ^ n)) ≤ (2 * Real.sqrt B) ^ n := by
    apply max_le
    · grind
    · apply (Real.sqrt_le_left (pow_nonneg (by positivity) _)).mpr
      calc
        B ^ n ≤ ((2 * Real.sqrt B) ^ 2) ^ n :=
          pow_le_pow_left₀ hB0 (by grind) n
        _ = ((2 * Real.sqrt B) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm n 2]
  have hh := Real.rpow_le_rpow (by positivity) hH (by positivity : 0 ≤ 1 / (n : ℝ))
  rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)] at hh
  simpa using hh

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- The algebraic and curve-counting reduction combined with the
finite lattice packing, given a short integral basis `b`. -/
theorem boundedSquareNormIntegers_odd_count_of_relative_short_basis
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : ∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K)
    (hn : 2 ≤ Module.finrank ℚ K) (hodd : Odd (Module.finrank ℚ K))
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hnorm : ∀ i, ‖b i‖ ≤ C * B) :
    ((boundedSquareNormIntegers K B).ncard : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      (12 * affineHypersurfaceAuxiliaryConstant 0 * (Module.finrank ℚ K : ℝ) ^ 4) *
        (numberFieldLatticeBoxConstant (Module.finrank ℚ K) C *
          (2 : ℝ) ^ Module.finrank ℚ K) *
        (B ^ (Module.finrank ℚ K - 1) * Real.sqrt B) := by
  have hs : ((boundedSquareNormIntegers K B).ncard : ℝ) ≤
      (12 * affineHypersurfaceAuxiliaryConstant 0 * (Module.finrank ℚ K : ℝ) ^ 4) *
        (boundedSquareNormTranslationClasses K B).card * Real.sqrt B := by
    obtain ⟨β, hcover⟩ : ∃ β : (boundedSquareNormTranslationClasses K B) → 𝓞 K,
        (boundedSquareNormIntegers K B).ncard ≤
          ∑ q : boundedSquareNormTranslationClasses K B,
            (count (signedNormCurveLocus K (β q) 1)
              (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) +
            count (signedNormCurveLocus K (β q) (-1))
              (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K)))) := by
      obtain ⟨β, hb, hcov⟩ := exists_norm_translate_cover K B
      refine ⟨β, ?_⟩
      let sf := (boundedSquareNormIntegers_finite K B).toFinset
      let tf (q : boundedSquareNormTranslationClasses K B) :=
        (squareNormTranslateFiber_finite K (β q) B).toFinset
      have hcover : sf ⊆ Finset.univ.biUnion tf := by
        intro α hα
        obtain ⟨q, hq⟩ := hcov α ((boundedSquareNormIntegers_finite K B).mem_toFinset.mp hα)
        exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q,
          (squareNormTranslateFiber_finite K (β q) B).mem_toFinset.mpr hq⟩
      calc
        _ = sf.card := Set.ncard_eq_toFinset_card _ _
        _ ≤ ∑ q, (tf q).card := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
        _ ≤ _ := Finset.sum_le_sum fun q _ ↦ (Set.ncard_eq_toFinset_card _ _).symm.trans_le
          (squareNormTranslateFiber_count_le K (β q) (hb q))
    let H := max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))
    have hH : 1 ≤ H := le_trans (by linarith) (le_max_left _ _)
    have hroot := normCurveBoxHeight_root_le hn hB
    have hC : 0 ≤ 3 * affineHypersurfaceAuxiliaryConstant 0 *
        (Module.finrank ℚ K : ℝ) ^ 4 := by
      have := (affineHypersurfaceAuxiliaryConstant_pos 0).le
      positivity
    have hpair (q : boundedSquareNormTranslationClasses K B) :
        ((count (signedNormCurveLocus K (β q) 1) H +
          count (signedNormCurveLocus K (β q) (-1)) H : ℕ) : ℝ) ≤
        (12 * affineHypersurfaceAuxiliaryConstant 0 * (Module.finrank ℚ K : ℝ) ^ 4) *
          Real.sqrt B := by
      have hp := signed_norm_curve_log_free_count K (β q) (ε := 1) isUnit_one hn hodd hH
      have hm := signed_norm_curve_log_free_count K (β q) (ε := -1) (by simp) hn hodd hH
      change (count (signedNormCurveLocus K (β q) 1) H : ℝ) ≤ _ at hp
      change (count (signedNormCurveLocus K (β q) (-1)) H : ℝ) ≤ _ at hm
      push_cast
      calc
        _ ≤ 2 * (3 * affineHypersurfaceAuxiliaryConstant 0 *
            (Module.finrank ℚ K : ℝ) ^ 4) * H ^ (1 / (Module.finrank ℚ K : ℝ)) := by
          linarith
        _ ≤ 2 * (3 * affineHypersurfaceAuxiliaryConstant 0 *
            (Module.finrank ℚ K : ℝ) ^ 4) * (2 * Real.sqrt B) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
        _ = _ := by ring
    have hcoverR :
        ((boundedSquareNormIntegers K B).ncard : ℝ) ≤
          ∑ q : boundedSquareNormTranslationClasses K B,
            ((count (signedNormCurveLocus K (β q) 1) H +
              count (signedNormCurveLocus K (β q) (-1)) H : ℕ) : ℝ) := by
      exact_mod_cast hcover
    calc
      _ ≤ _ := hcoverR
      _ ≤ ∑ _q : boundedSquareNormTranslationClasses K B,
          (12 * affineHypersurfaceAuxiliaryConstant 0 * (Module.finrank ℚ K : ℝ) ^ 4) *
            Real.sqrt B := Finset.sum_le_sum (fun q _ ↦ hpair q)
      _ = _ := by simp; ring
  have hq := boundedSquareNormTranslationClasses_count_of_relative_short_basis
    K b hb hB hC hnorm
  have hcurve : 0 ≤ 12 * affineHypersurfaceAuxiliaryConstant 0 *
      (Module.finrank ℚ K : ℝ) ^ 4 := by
    have := (affineHypersurfaceAuxiliaryConstant_pos 0).le
    positivity
  have h₁ := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg |(discr K : ℝ)|)
  have h₂ := mul_le_mul_of_nonneg_left hq
    (mul_nonneg hcurve (Real.sqrt_nonneg B))
  nlinarith

