module
public import DedekindZetaZeroFree.Analysis.Gamma.ReflectionAndReciprocalStripBounds

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

open scoped NumberField Classical
open Complex MeasureTheory

private alias norm_Gamma_le_Gamma_re := DedekindZetaZeroFree.GammaBounds.norm_Gamma_le_real

private alias norm_sin_le_exp_im := DedekindZetaZeroFree.GammaBounds.norm_sin_le_exp_abs_im

private theorem sin_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) : Complex.sin z ≠ 0 := by
  intro h
  have h2 : (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * (Complex.I / 2) = 0 := by
    rw [show (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * (Complex.I / 2)
          = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 by ring]
    exact h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (by simp)))
  have hre : (-z * Complex.I).re = (z * Complex.I + (n:ℂ) * (2 * (Real.pi:ℂ) * Complex.I)).re := by
    rw [hn]
  simp [Complex.mul_I_re, Complex.neg_re, Complex.neg_im] at hre
  exact hz (by linarith)

private theorem Gamma_one_sub_add_nat (s : ℂ) (n : ℕ) (h : ∀ k < n, s ≠ ((k:ℂ) + 1)) :
    Complex.Gamma (1 - s + n) = (∏ k ∈ Finset.range n, (((k:ℂ) + 1) - s)) * Complex.Gamma (1 - s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw : (1 - s + n) ≠ 0 := fun hc => (h n (Nat.lt_succ_self n)) (by linear_combination -hc)
    have hcast : (1 - s + ((n:ℂ) + 1)) = (1 - s + n) + 1 := by ring
    rw [Nat.cast_succ, hcast, Complex.Gamma_add_one _ hw, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), Finset.prod_range_succ]
    ring

private theorem inv_Gamma_eq (s : ℂ) (hs : Complex.sin ((Real.pi:ℂ) * s) ≠ 0) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1 - s) * Complex.sin ((Real.pi:ℂ) * s) / (Real.pi:ℂ) := by
  apply inv_eq_of_mul_eq_one_right
  have e : Complex.Gamma s * (Complex.Gamma (1 - s) * Complex.sin ((Real.pi:ℂ) * s) / (Real.pi:ℂ))
      = (Complex.Gamma s * Complex.Gamma (1 - s)) * (Complex.sin ((Real.pi:ℂ) * s) / (Real.pi:ℂ)) := by
    ring
  rw [e, (Complex.Gamma_mul_Gamma_one_sub s)]
  field_simp

private theorem continuousOn_RealGamma_Icc {l u : ℝ} (hl : 0 < l) :
    ContinuousOn Real.Gamma (Set.Icc l u) := by
  intro x hx
  have hx0 := lt_of_lt_of_le hl hx.1
  have hc : ContinuousAt (fun y : ℝ => Complex.Gamma ((y:ℝ):ℂ)) x :=
    (Complex.continuousAt_Gamma (x:ℂ) (fun m hm => by
      have := congrArg Complex.re hm
      simp at this
      linarith)).comp (continuous_ofReal.continuousAt)
  exact (Complex.continuous_re.continuousAt.comp hc).continuousWithinAt

private theorem inverse_Gamma_strip_bound (a b : ℝ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ, s.re ∈ Set.Icc a b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * Real.exp (A * |s.im|) := by
  let n := ⌈b⌉₊
  have hbn := Nat.le_ceil b
  have hb1n : (0:ℝ) < 1 - b + (n:ℝ) := by linarith
  have hcont : ContinuousOn Real.Gamma (Set.Icc (1 - b + n) (1 - a + n)) :=
    continuousOn_RealGamma_Icc hb1n
  obtain ⟨D0, hD0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let D := max D0 0 / Real.pi
  have hlarge : ∀ s : ℂ, s.re ∈ Set.Icc a b → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ D * Real.exp (Real.pi * |s.im|) := by
    intro s hs ht
    have hsim : s.im ≠ 0 := by intro h; rw [h] at ht; exact absurd ht (by norm_num)
    have hsin : Complex.sin ((Real.pi:ℂ) * s) ≠ 0 := by
      apply sin_ne_zero_of_im_ne_zero
      show ((Real.pi:ℂ) * s).im ≠ 0
      rw [Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_ne_zero Real.pi_ne_zero hsim
    have hfac : ∀ k : ℕ, (1:ℝ) ≤ ‖((k:ℂ) + 1) - s‖ := by
      intro k
      have h1 : |s.im| ≤ ‖((k:ℂ) + 1) - s‖ := by
        have := Complex.abs_im_le_norm (((k:ℂ) + 1) - s)
        simpa [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.one_im] using this
      linarith
    have hPnorm : (1:ℝ) ≤ ‖∏ k ∈ Finset.range n, (((k:ℂ) + 1) - s)‖ := by
      rw [norm_prod]
      induction n with
      | zero => simp
      | succ m ih => rw [Finset.prod_range_succ]; exact one_le_mul_of_one_le_of_one_le ih (hfac m)
    have hrec := Gamma_one_sub_add_nat s n (fun k _ => by
      intro hc
      refine hsim ?_
      rw [hc]; simp)
    have hG1 : ‖Complex.Gamma (1 - s)‖ ≤ ‖Complex.Gamma (1 - s + n)‖ := by
      have hnorms : ‖Complex.Gamma (1 - s + n)‖
          = ‖∏ k ∈ Finset.range n, (((k:ℂ) + 1) - s)‖ * ‖Complex.Gamma (1 - s)‖ := by
        rw [hrec, norm_mul]
      rw [hnorms]
      calc _ = 1 * ‖Complex.Gamma (1 - s)‖ := by ring
        _ ≤ ‖∏ k ∈ Finset.range n, (((k:ℂ) + 1) - s)‖ * ‖Complex.Gamma (1 - s)‖ :=
            mul_le_mul_of_nonneg_right hPnorm (norm_nonneg (Complex.Gamma (1 - s)))
    have hGn : ‖Complex.Gamma (1 - s + n)‖ ≤ max D0 0 := by
      have hre_pos : 0 < (1 - s + n).re := by
        have h2 : (1:ℝ) ≤ (1 - s + n).re := by
          simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re,
            Complex.ofReal_re]
          linarith [hs.2, hbn]
        linarith
      have hle := norm_Gamma_le_Gamma_re (1 - s + n) hre_pos
      have hmem : (1 - s + n).re ∈ Set.Icc (1 - b + n) (1 - a + n) := by
        simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re,
          Complex.ofReal_re]
        exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hb := hD0 _ hmem
      rw [Real.norm_eq_abs] at hb
      linarith [le_max_left D0 0, (abs_le.mp hb).2]
    rw [inv_Gamma_eq s hsin, norm_div, norm_mul]
    have hsinb : ‖Complex.sin ((Real.pi:ℂ) * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
      have := norm_sin_le_exp_im ((Real.pi:ℂ) * s)
      rwa [show ((Real.pi:ℂ) * s).im = Real.pi * s.im by
            simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im],
          abs_mul, abs_of_pos Real.pi_pos] at this
    rw [(Complex.norm_of_nonneg Real.pi_pos.le)]
    calc _
        ≤ (max D0 0) * Real.exp (Real.pi * |s.im|) / Real.pi := by
          apply div_le_div_of_nonneg_right _ Real.pi_pos.le
          exact mul_le_mul (hG1.trans hGn) hsinb (norm_nonneg _) (le_max_right _ _)
      _ = D * Real.exp (Real.pi * |s.im|) := by ring
  have hK : IsCompact ((fun p : ℝ × ℝ => (p.1:ℂ) + (p.2:ℂ) * Complex.I) ''
      (Set.Icc a b ×ˢ Set.Icc (-1:ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn
    (Complex.differentiable_one_div_Gamma.continuous.norm.continuousOn)
  refine ⟨max (max C0 D) 0, Real.pi, le_max_right _ _, Real.pi_pos.le, ?_⟩
  intro s hs
  by_cases ht : |s.im| ≤ 1
  · have hmem : s ∈ (fun p : ℝ × ℝ => (p.1:ℂ) + (p.2:ℂ) * Complex.I) ''
        (Set.Icc a b ×ˢ Set.Icc (-1:ℝ) 1) := by
      refine ⟨(s.re, s.im), ⟨hs, ?_⟩, ?_⟩
      · rw [Set.mem_Icc]; exact abs_le.mp ht
      · exact Complex.re_add_im s
    have hb := hC0 s hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    calc _ ≤ C0 := hb
      _ ≤ max (max C0 D) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
      _ ≤ max (max C0 D) 0 * Real.exp (Real.pi * |s.im|) :=
          le_mul_of_one_le_right (le_max_right _ _) (Real.one_le_exp (by positivity))
  · rw [not_le] at ht
    calc _ ≤ D * Real.exp (Real.pi * |s.im|) := (hlarge s hs ht.le)
      _ ≤ max (max C0 D) 0 * Real.exp (Real.pi * |s.im|) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _))
            (Real.exp_nonneg _)

theorem inverse_Gammaℂ_strip_exp_bound (a b : ℝ) (r : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ s : ℂ, s.re ∈ Set.Icc a b →
        ‖(Complex.Gammaℂ s)⁻¹‖ ^ r ≤ C * Real.exp (A * |s.im|) := by
  obtain ⟨C, A, hC, hA, hbound⟩ := inverse_Gamma_strip_bound a b
  refine ⟨(C * (2 * Real.pi) ^ (max a b)) ^ r, (r:ℝ) * A,
    pow_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith [Real.pi_pos]) _)) r,
    mul_nonneg (Nat.cast_nonneg r) hA, ?_⟩
  intro s hs
  have hkey : (Complex.Gammaℂ s)⁻¹
      = (1/2 : ℂ) * (2 * (Real.pi : ℂ)) ^ s * (Complex.Gamma s)⁻¹ := by
    rw [Complex.Gammaℂ_def, mul_inv, mul_inv, Complex.cpow_neg, inv_inv]
    ring_nf
  let exp₀ := Real.exp (A * |s.im|)
  have hnorm : ‖(Complex.Gammaℂ s)⁻¹‖ ≤ C * (2 * Real.pi) ^ (max a b) * exp₀ := by
    rw [hkey, norm_mul, norm_mul]
    have hhalf : ‖(1/2 : ℂ)‖ = 1/2 := by
      rw [show (1/2 : ℂ) = (((1/2 : ℝ)) : ℂ) by norm_num]
      exact Complex.norm_of_nonneg (by norm_num)
    have hcpow : ‖(2 * (Real.pi : ℂ)) ^ s‖ = (2 * Real.pi) ^ s.re := by
      rw [show (2 * (Real.pi:ℂ)) = ((2*Real.pi:ℝ):ℂ) by push_cast; ring]
      exact norm_cpow_eq_rpow_re_of_pos (by positivity) s
    rw [hhalf, hcpow]
    calc _
        ≤ (1/2) * (2 * Real.pi) ^ (max a b) * (C * exp₀) := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (hs.2.trans (le_max_right _ _))) (by norm_num)
          · exact hbound s hs
          · exact norm_nonneg _
          · positivity
      _ ≤ (2 * Real.pi) ^ (max a b) * (C * exp₀) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_of_le_one_left (by positivity)
          norm_num
      _ = C * (2 * Real.pi) ^ (max a b) * exp₀ := by ring
  calc _
      ≤ (C * (2 * Real.pi) ^ (max a b) * exp₀) ^ r :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm r
    _ = (C * (2 * Real.pi) ^ (max a b)) ^ r * exp₀ ^ r := by rw [mul_pow]
    _ = (C * (2 * Real.pi) ^ (max a b)) ^ r * Real.exp (((r:ℝ) * A) * |s.im|) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring_nf

end DedekindZetaZeroFree.LargeSieve.Vendor
