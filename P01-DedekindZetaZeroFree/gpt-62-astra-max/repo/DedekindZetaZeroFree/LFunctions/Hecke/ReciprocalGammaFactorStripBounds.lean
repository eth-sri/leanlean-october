module
public import DedekindZetaZeroFree.Analysis.Gamma.ReflectionAndReciprocalStripBounds

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Real.Pi.Bounds
public import DedekindZetaZeroFree.Analysis.Gamma.ElementaryNormBounds

@[expose] public section

namespace DedekindZetaZeroFree

private lemma gamma_inv_reflection {s : ℂ} (hs : s.im ≠ 0) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi := by exact GammaBounds.inverse_Gamma_reflection s hs

variable (a b : ℝ) (hab : a ≤ b)

include hab in
theorem gamma_inverse_strip_exp_bound :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := by

  obtain ⟨n, hn⟩ : ∃ n : ℕ, b ≤ (n : ℝ) := ⟨Nat.ceil b, Nat.le_ceil b⟩

  obtain ⟨M, hMpos, hM⟩ :=
    gamma_real_interval_bound (a := 1 - b + n) (b := 1 - a + n) (by linarith)

  have hcont : Continuous fun p : ℝ × ℝ =>
      ‖(Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))⁻¹‖ := by
    apply Continuous.norm
    exact Complex.differentiable_one_div_Gamma.continuous.comp (by continuity)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc).prod (isCompact_Icc)
      |>.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max (M / Real.pi) (max C 1), ?_, ?_⟩
  · positivity
  · intro s hs
    obtain ⟨hsa, hsb⟩ := hs
    rcases le_or_gt (1 : ℝ) |s.im| with hbig | hsmall
    ·
      have him : s.im ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hbig; norm_num at hbig
      have hre : (1 - s + (n : ℂ)).re = 1 - s.re + (n : ℝ) := by simp
      have hmem : (1 - s + (n : ℂ)).re ∈ Set.Icc (1 - b + n) (1 - a + n) := by
        rw [hre, Set.mem_Icc]; constructor <;> linarith
      have hGbound : ‖Complex.Gamma (1 - s)‖ ≤ M := by
        calc ‖Complex.Gamma (1 - s)‖ ≤ ‖Complex.Gamma (1 - s + (n : ℂ))‖ :=
              gamma_norm_le_add_nat (by
                have : (1 - s).im = -s.im := by simp
                rw [this, abs_neg]; exact hbig) n
          _ ≤ Real.Gamma ((1 - s + (n : ℂ)).re) := gamma_norm_le_real (by
            linarith)
          _ ≤ M := hM _ hmem
      have hSbound : ‖Complex.sin ((Real.pi : ℂ) * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
        have h := complex_sin_norm_le_exp_im ((Real.pi : ℂ) * s)
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          abs_mul, abs_of_pos Real.pi_pos] at h
        exact h
      rw [gamma_inv_reflection him, norm_div, norm_mul]
      have hnorm : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
      rw [hnorm]
      calc _
          ≤ M * Real.exp (Real.pi * |s.im|) / Real.pi := by
            apply div_le_div_of_nonneg_right _ Real.pi_pos.le
            exact mul_le_mul hGbound hSbound (norm_nonneg _) hMpos.le
        _ = M / Real.pi * Real.exp (Real.pi * |s.im|) := by ring
        _ ≤ max (M / Real.pi) (max C 1) * Real.exp (Real.pi * |s.im|) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    ·
      have hmemK : (s.re, s.im) ∈ Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1 :=
        ⟨⟨hsa, hsb⟩,
          ⟨by linarith [neg_abs_le s.im, hsmall], by linarith [le_abs_self s.im, hsmall]⟩⟩
      have hCapp := hC (s.re, s.im) hmemK
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Complex.re_add_im] at hCapp
      calc _ ≤ C := hCapp
        _ ≤ max (M / Real.pi) (max C 1) := le_trans (le_max_left C 1) (le_max_right _ _)
        _ = max (M / Real.pi) (max C 1) * 1 := (mul_one _).symm
        _ ≤ max (M / Real.pi) (max C 1) * Real.exp (Real.pi * |s.im|) :=
            mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))).le

include hab in
theorem gammaC_inverse_strip_exp_bound :
    ∃ GC : ℝ, 0 < GC ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(Complex.Gammaℂ s)⁻¹‖ ≤ GC * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨G, hGpos, hG⟩ := gamma_inverse_strip_exp_bound a b hab
  refine ⟨max (G * (2 * Real.pi) ^ b / 2) 1, ?_, ?_⟩
  · positivity
  · intro s hs
    obtain ⟨hsa, hsb⟩ := hs
    have hbase : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring

    have hpow : ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹‖ = (2 * Real.pi) ^ s.re / 2 := by
      rw [norm_inv, norm_mul, hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.neg_re, Complex.norm_ofNat, Real.rpow_neg (by positivity)]
      field_simp
    rw [Complex.Gammaℂ_def]
    have hnorm : ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s)⁻¹‖ =
        ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹‖ * ‖(Complex.Gamma s)⁻¹‖ := by
      rw [mul_inv, norm_mul]
    rw [hnorm]
    calc _
        ≤ ((2 * Real.pi) ^ s.re / 2) * (G * Real.exp (Real.pi * |s.im|)) := by
          bound
      _ ≤ ((2 * Real.pi) ^ b / 2) * (G * Real.exp (Real.pi * |s.im|)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hGpos.le (Real.exp_pos _).le)
          exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hsb) (by norm_num)
      _ = G * (2 * Real.pi) ^ b / 2 * Real.exp (Real.pi * |s.im|) := by ring
      _ ≤ max (G * (2 * Real.pi) ^ b / 2) 1 * Real.exp (Real.pi * |s.im|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end DedekindZetaZeroFree
