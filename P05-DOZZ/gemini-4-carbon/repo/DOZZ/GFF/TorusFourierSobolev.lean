/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.LocalSchur
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# DOZZ.GFF.TorusFourierSobolev

Fourier coefficient weights for the concrete two dimensional torus Sobolev space. The square
inverse weights are summable, which is the numerical core of the G5 Hilbert--Schmidt estimate.
-/

@[expose] public section


namespace DOZZ

/-- The inhomogeneous squared frequency weight for the unit two-torus. -/
def torusSobolevWeight (k : Fin 2 → ℤ) : ℝ :=
  1 + (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2

private noncomputable def intOneDimWeight (n : ℤ) : ℝ := 1 / (1 + |(n : ℝ)|) ^ 2




private def finTwoIntEquiv : (Fin 2 → ℤ) ≃ ℤ × ℤ where
  toFun k := (k 0, k 1)
  invFun p i := if i = 0 then p.1 else p.2
  left_inv k := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    cases p
    rfl

/-- The reciprocal square weights of the two dimensional Fourier modes are summable. -/
theorem summable_torusSobolevWeight_inv_sq :
    Summable (fun k : Fin 2 → ℤ => (torusSobolevWeight k)⁻¹ ^ 2) := by
  have summable_pair_weight_inv_sq : Summable (fun p : ℤ × ℤ => (1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)⁻¹ ^ 2) := by
    have pair_weight_le_product (m n : ℤ) : (1 + (m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹ ≤
          2 * (1 + |(m : ℝ)|)⁻¹ * (1 + |(n : ℝ)|)⁻¹ := by
      have hn : 0 ≤ |(n : ℝ)| := abs_nonneg _
      have hcore : (1 + |(m : ℝ)|) * (1 + |(n : ℝ)|) ≤
          2 * (1 + (m : ℝ) ^ 2 + (n : ℝ) ^ 2) := by
        have : |(m : ℝ)| ^ 2 = (m : ℝ) ^ 2 := sq_abs _
        have : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
        nlinarith [sq_nonneg (|(m : ℝ)| - 1 / 2),
          sq_nonneg (|(n : ℝ)| - 1 / 2), sq_nonneg (|(m : ℝ)| - |(n : ℝ)|)]
      have hden : 0 < 1 + (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by positivity
      have hden' : 0 < (1 + |(m : ℝ)|) * (1 + |(n : ℝ)|) := by positivity
      let prodDen := (1 + |(m : ℝ)|) * (1 + |(n : ℝ)|)
      have hdenHalf : 0 < prodDen / 2 := by positivity
      have hhalf : prodDen / 2 ≤
          1 + (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by nlinarith [hcore])
      have hinv : (1 + (m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹ ≤
          (2 / prodDen) := by
        have h := (inv_le_inv₀ hden hdenHalf).2 hhalf
        refine (h).trans_eq (?_)
        field_simp [ne_of_gt hden']
      refine (hinv).trans_eq (?_)
      field_simp [prodDen, ne_of_gt hden']
      ring
    have summable_intOneDimWeight : Summable intOneDimWeight := by
      apply Summable.of_nonneg_of_le (fun n => by unfold intOneDimWeight; positivity)
        (fun n => ?_) ((Real.summable_one_div_int_add_rpow (1 / 2) 2).mpr (by norm_num))
      have : |(n : ℝ) + 1 / 2| ≤ 1 + |(n : ℝ)| := by
        refine (abs_add_le _ _).trans (?_)
        calc |(n : ℝ)| + |(1 / 2 : ℝ)| = |(n : ℝ)| + 1 / 2 := by norm_num
          _ ≤ 1 + |(n : ℝ)| := by linarith
      have hpos : 0 < |(n : ℝ) + 1 / 2| := by
        apply abs_pos.mpr
        intro hn
        have hn' : (2 * n + 1 : ℤ) = 0 := by exact_mod_cast (by linarith : (2 : ℝ) * n + 1 = 0)
        omega
      have hpow : |(n : ℝ) + 1 / 2| ^ (2 : ℝ) ≤ (1 + |(n : ℝ)|) ^ (2 : ℝ) := by
        gcongr
      have hbig : 0 < (1 + |(n : ℝ)|) ^ (2 : ℝ) := by positivity
      simpa [intOneDimWeight, one_div] using (inv_le_inv₀ hbig (Real.rpow_pos_of_pos hpos _)).2 hpow
    have hq := summable_intOneDimWeight
    have hweight_nonneg (n : ℤ) : 0 ≤ intOneDimWeight n := by
      unfold intOneDimWeight
      positivity
    refine Summable.of_nonneg_of_le
      (f := fun p : ℤ × ℤ => 4 * (intOneDimWeight p.1 * intOneDimWeight p.2))
      (g := fun p : ℤ × ℤ => (1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)⁻¹ ^ 2)
      (fun p => sq_nonneg _) (fun p => ?_) ?_
    · have h := pair_weight_le_product p.1 p.2
      have hnonneg : 0 ≤ (1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)⁻¹ := by positivity
      have hqnonneg : 0 ≤ 2 * (1 + |(p.1 : ℝ)|)⁻¹ * (1 + |(p.2 : ℝ)|)⁻¹ := by positivity
      refine ((sq_le_sq₀ hnonneg hqnonneg).mpr h).trans_eq (?_)
      simp only [intOneDimWeight]
      field_simp [ne_of_gt (show 0 < 1 + |(p.1 : ℝ)| by positivity),
        ne_of_gt (show 0 < 1 + |(p.2 : ℝ)| by positivity)]
      ring
    · exact (hq.mul_of_nonneg hq hweight_nonneg hweight_nonneg).mul_left 4
  exact finTwoIntEquiv.summable_iff.mpr (summable_pair_weight_inv_sq)

end DOZZ

end
