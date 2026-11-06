module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.DampedWeightedKernel
public import WeylPort.AFE.LowerIntegralEstimate

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Actual finite-frequency main terms and integral assembly

The Gamma evaluation is summed over the actual positive integer frequencies.
The harmonic estimate keeps the isolated unit term and the literal cutoff.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex MeasureTheory

/-- The dual polynomial has the source's uniform logarithmic bound, including both strip endpoints. -/
theorem norm_sum_dual_powers_le {σ t y : ℝ} (hσ : 0 ≤ σ) (hy : 1 ≤ y) :
    ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ ≤
      y ^ σ * Real.log y + 1 := by
  let S := Finset.Icc 1 ⌊y⌋₊
  have h1 : 1 ∈ S := Finset.left_mem_Icc.mpr (Nat.floor_pos.mpr hy)
  have hpos (m : ℕ) (hm : m ∈ S) : 0 < (m : ℝ) := by
    aesop
  have hle (m : ℕ) (hm : m ∈ S) : (m : ℝ) ≤ y :=
    (by aesop : (m : ℝ) ≤ (⌊y⌋₊ : ℝ)).trans
      (Nat.floor_le (by linarith))
  have hterm (m : ℕ) (hm : m ∈ S) :
      ‖(m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ ≤ y ^ σ * (1 / (m : ℝ)) := by
    rw [← Complex.ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (hpos m hm)]
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, one_re]
    rw [Real.rpow_sub (hpos m hm), Real.rpow_one, mul_one_div]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (hpos m hm).le (hle m hm) hσ)
      (hpos m hm).le
  have hh : (∑ m ∈ S.erase 1, 1 / (m : ℝ)) ≤ Real.log y := by
    have h := sum_reciprocals_floor_le hy
    change (∑ m ∈ S, 1 / (m : ℝ)) ≤ Real.log y + 1 at h
    rw [← Finset.sum_erase_add S _ h1] at h
    norm_num at h
    simpa only [one_div] using h
  calc
    _ ≤ ∑ m ∈ S, ‖(m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ := norm_sum_le _ _
    _ = 1 + ∑ m ∈ S.erase 1, ‖(m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ := by
      rw [← Finset.sum_erase_add S _ h1]
      simp only [Nat.cast_one, one_cpow, norm_one, add_comm]
    _ ≤ 1 + y ^ σ * ∑ m ∈ S.erase 1, 1 / (m : ℝ) := by
      rw [Finset.mul_sum]
      apply add_le_add (le_refl _)
      exact Finset.sum_le_sum (fun m hm => hterm m (Finset.mem_of_mem_erase hm))
    _ ≤ 1 + y ^ σ * Real.log y :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by linarith) _))
    _ = _ := by ring

section
variable {σ t y t₀ : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
include σ t y t₀ hσ
/-- The actual improper integral main terms sum to the exact chi factor times the dual polynomial. -/
theorem sum_weightedIntegralTail_zero_eq_chi
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 (m : ℝ)) =
      chi ((σ : ℂ) + (t : ℂ) * I) * (1 + gammaChiError ((σ : ℂ) + (t : ℂ) * I)) *
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  simpa only [Complex.ofReal_natCast] using weightedIntegralTail_zero_eq_chi hσ hmpos ht₀ ht

/-- The error in replacing the actual main integrals by the dual polynomial has the printed logarithmic size. -/
theorem norm_sum_weightedIntegralTail_sub_chi_le
    (hy : 1 ≤ y) (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖(∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 (m : ℝ)) -
      chi ((σ : ℂ) + (t : ℂ) * I) *
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * I)‖ *
        (Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))) *
        (y ^ σ * Real.log y + 1) := by
  rw [sum_weightedIntegralTail_zero_eq_chi hσ ht₀ ht]
  rw [show chi ((σ : ℂ) + (t : ℂ) * I) *
      (1 + gammaChiError ((σ : ℂ) + (t : ℂ) * I)) *
      (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)) -
      chi ((σ : ℂ) + (t : ℂ) * I) *
      (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)) =
      chi ((σ : ℂ) + (t : ℂ) * I) * gammaChiError ((σ : ℂ) + (t : ℂ) * I) *
      (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)) by ring,
    norm_mul, norm_mul]
  have he : ‖gammaChiError ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀)) := by
    simpa using norm_gammaChiError_le (s := (σ : ℂ) + (t : ℂ) * I) ht₀ (by simpa using ht)
  exact mul_le_mul (mul_le_mul_of_nonneg_left he (norm_nonneg _))
    (norm_sum_dual_powers_le hσ.1.le hy) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans he))
end

end DhimanKadiriQuesadaHerrera2026
