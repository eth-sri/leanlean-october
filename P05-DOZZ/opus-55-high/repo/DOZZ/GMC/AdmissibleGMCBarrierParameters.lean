/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.GaussianTailBound

/-! Robust subcritical barrier parameters for the admissible mixed-root estimate. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A subcritical charge admits a barrier exponent with room for the covariance-error parameter
in the two-root Gaussian tail estimate. -/
theorem exists_fixed_charge_robust_barrier_parameters
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ a κ η : ℝ, γ < a ∧ a < 2 * γ ∧ 0 < κ ∧ κ < 2 ∧
      0 < η ∧ η < 1 ∧
      γ ^ 2 - ((1 - η) ^ 2 * (2 * γ - a) ^ 2 / (2 * (1 + η))) ≤ κ := by
  obtain ⟨a, κ₀, hγa, ha2, hκeq, hκ₀pos, hκ₀lt⟩ :=
    exists_fixed_charge_barrier_parameters γ hγ hγ2
  let κ := (κ₀ + 2) / 2
  have hκ₀κ : κ₀ < κ := by grind
  have hκpos : 0 < κ := by positivity
  have hκlt : κ < 2 := by grind
  let b : ℝ := 2 * γ - a
  have hb : 0 < b := by positivity
  let gap := κ - κ₀
  have hgap : 0 < gap := by positivity
  let η := min (1 / 2) (gap / (3 * b ^ 2))
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min (by norm_num) (div_pos hgap (by positivity))
  have hηhalf : η ≤ 1 / 2 := min_le_left ..
  have hηgap : η ≤ gap / (3 * b ^ 2) := min_le_right ..
  have hηlt : η < 1 := by linarith
  have hfrac : (3 * η - η ^ 2) / (2 * (1 + η)) ≤ 3 * η / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hηerr : η * (3 * b ^ 2 / 2) ≤ gap / 2 := by
    calc
      η * (3 * b ^ 2 / 2) ≤ (gap / (3 * b ^ 2)) * (3 * b ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hηgap (by positivity)
      _ = gap / 2 := by
        have hb2 := ne_of_gt (sq_pos_of_pos hb)
        field_simp
  have hidentity : γ ^ 2 -
      ((1 - η) ^ 2 * b ^ 2 / (2 * (1 + η))) =
        κ₀ + b ^ 2 * ((3 * η - η ^ 2) / (2 * (1 + η))) := by
    have hden : 1 + η ≠ 0 := ne_of_gt (by positivity)
    rw [hκeq]
    dsimp [b]
    field_simp
    ring
  refine ⟨a, κ, η, hγa, ha2, hκpos, hκlt, hηpos, hηlt, ?_⟩
  rw [show (2 * γ - a) ^ 2 = b ^ 2 by rfl, hidentity]
  calc
    κ₀ + b ^ 2 * ((3 * η - η ^ 2) / (2 * (1 + η))) ≤
        κ₀ + b ^ 2 * (3 * η / 2) := by
          simpa [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left hfrac (sq_nonneg b)) κ₀
    _ = κ₀ + η * (3 * b ^ 2 / 2) := by ring
    _ ≤ κ₀ + gap / 2 := by linarith
    _ ≤ κ := by linarith

/-- Beyond one natural scale, all linear error conditions for a fixed two-root barrier hold and
the coarse radius is below the admissible cutoff. -/
theorem exists_natural_scale_after_covariance_errors
    (C γ η b cutoff : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) (hη : 0 < η)
    (hb : 0 < b) (hcutoff : 0 < cutoff) :
    ∃ k₀ : ℕ, Real.exp (-(k₀ : ℝ)) ≤ cutoff ∧
      C < (k₀ : ℝ) ∧ C ≤ η * (k₀ : ℝ) ∧
        2 * γ * C + 1 ≤ η * b * (k₀ : ℝ) := by
  let T₁ := max 0 (Real.log (1 / cutoff))
  let T₂ := max (C + 1) (C / η + 1)
  let T₃ := max ((2 * γ * C + 1) / (η * b) + 1) T₁
  let T := max T₂ T₃
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt T
  have hT₂ : T₂ ≤ T := le_max_left ..
  have hT₃ : T₃ ≤ T := le_max_right ..
  have hCplus := le_trans (le_max_left ..) hT₂
  have hCrate := le_trans (le_max_right ..) hT₂
  have hoffset :=
    le_trans (le_max_left ..) hT₃
  have hlog :=
    le_trans (le_max_right ..) (le_trans (le_max_right ..) hT₃)
  have hTnonneg : 0 ≤ T := by positivity
  have hkC : C < k₀ := by linarith
  have hkCrate : C / η < k₀ := by linarith
  have hkoffset : (2 * γ * C + 1) / (η * b) < k₀ := by linarith
  have hkcut : Real.exp (-k₀) ≤ cutoff := by
    by_cases hcutoff1 : cutoff < 1
    · have hdiv : 1 < 1 / cutoff := by
        rwa [one_lt_div₀ hcutoff]
      have hlogpos := Real.log_pos hdiv
      have hklog := lt_of_le_of_lt hlog hk₀
      have hexp : Real.exp (-Real.log (1 / cutoff)) = cutoff := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
      exact le_of_lt <| calc
        Real.exp (-k₀) < Real.exp _ :=
          Real.exp_lt_exp.mpr (by linarith)
        _ = cutoff := hexp
    · have hcutoffge := le_of_not_gt hcutoff1
      exact (Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (Nat.cast_nonneg k₀))).trans hcutoffge
  refine ⟨k₀, hkcut, hkC, ?_, ?_⟩
  · have hmul := mul_lt_mul_of_pos_left hkCrate hη
    have hcancel : η * (C / η) = C := by field_simp
    linarith
  · have hmul := mul_lt_mul_of_pos_left hkoffset (mul_pos hη hb)
    have hcancel : (η * b) * ((2 * γ * C + 1) / (η * b)) = 2 * γ * C + 1 := by
      field_simp
    have hstrict : 2 * γ * C + 1 < η * b * k₀ := by
      calc
        2 * γ * C + 1 = (η * b) * ((2 * γ * C + 1) / (η * b)) := hcancel.symm
        _ < (η * b) * k₀ := hmul
        _ = η * b * k₀ := by ring
    exact le_of_lt hstrict


end DOZZ.Proofs
