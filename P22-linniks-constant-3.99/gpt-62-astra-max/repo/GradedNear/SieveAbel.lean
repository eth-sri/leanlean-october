module
public import GradedNear.SieveBasic
@[expose] public section
namespace GradedNear
open Finset MeasureTheory Set

/-- A real-endpoint prefix, starting at the first integer in the cell. -/
noncomputable abbrev prefixSum {V : Type*} [AddCommMonoid V] (f : ℕ → V) (A x : ℝ) :=
  ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊x⌋₊, f n

/-- Abel's identity with a real lower cutoff. Clip the coefficients, not the
multiplier: the partial sums are zero strictly before `A`. -/
lemma abel_cell {𝕜 : Type*} [RCLike 𝕜] {A B : ℝ} (hA : 1 ≤ A) (f : ℕ → 𝕜)
    {W : ℝ → 𝕜} (hd : ∀ x ∈ Set.Icc 1 B, DifferentiableAt ℝ W x) (hi : IntegrableOn (deriv W) (Set.Icc 1 B)) :
    prefixSum (fun n => W n*f n) A B = W B * prefixSum f A B - ∫ x in Set.Icc A B, deriv W x * prefixSum f A x := by
  let c (n : ℕ) := if A ≤ n then f n else 0
  have clip (F : ℕ → 𝕜) x :
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if A ≤ n then F n else 0) = prefixSum F A x := by
    rw [← sum_filter]; congr 1; ext; simp [Nat.ceil_le]; tauto
  have H := sum_mul_eq_sub_integral_mul₀ c (by simp [c, (zero_lt_one.trans_le hA).not_ge]) B hd hi
  simp_rw [c, mul_ite_zero, clip] at H
  rw [H, ← integral_Icc_eq_integral_Ioc]; congr 1
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc (Set.Icc_subset_Icc hA le_rfl)
  rintro t ⟨ht,hn⟩
  have h : ⌊t⌋₊ < ⌈A⌉₊ := Nat.lt_ceil.mpr ((Nat.floor_le ((zero_le_one.trans ht.1))).trans_lt (lt_of_not_ge fun h => hn ⟨h,ht.2⟩))
  simp [prefixSum, Finset.Icc_eq_empty_of_lt h]

open Complex Real

/-- The variation of `log x · x^(-s)` costs at most the increment of
`log x + ‖s‖ (log x)²/2`. The same estimate at `s = 1` retains the leading
coefficient of the diagonal main term. -/
lemma wt_bound {f : ℕ → ℂ} {A B E : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (hE : 0 ≤ E)
    (hP : ∀ x ∈ Set.Icc A B, ‖prefixSum f A x‖ ≤ E*x) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖prefixSum (fun n => wt s n * f n) A B‖ ≤ E*(2*Real.log B + ‖s‖ * (Real.log B^2 - Real.log A^2)/2) := by
  let d (x : ℝ) := (x : ℂ)^(-s) * (1-s*Real.log x) / x
  have hd x (hx : 0 < x) : HasDerivAt (wt s) (d x) x := by
    have h := (Real.hasDerivAt_log hx.ne').ofReal_comp.mul
      (hasDerivAt_ofReal_cpow_const hx.ne' (show -s ≠ 0 by intro h; simp_all; linarith))
    convert h using 1 <;> first | rfl | (simp [d, cpow_sub _ _ (ofReal_ne_zero.mpr hx.ne')]; ring)
  have hp (x : ℝ) (hx : 1 ≤ x) : ‖(x:ℂ)^(-s)‖ ≤ x⁻¹ := by
    rw [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx), ← rpow_neg_one]
    apply rpow_le_rpow_of_exponent_le hx; simpa
  have hB := hA.trans hAB
  have hL := log_nonneg hB
  have hc : ContinuousOn d (Set.Icc 1 B) := by
    intro x hx; have h := zero_lt_one.trans_le hx.1; apply ContinuousAt.continuousWithinAt
    dsimp [d]; fun_prop (disch := first | positivity | simp [h, h.ne'])
  rw [abel_cell hA f (fun x hx => (hd x (zero_lt_one.trans_le hx.1)).differentiableAt)
    (hc.congr (fun x hx => (hd x (zero_lt_one.trans_le hx.1)).deriv)).integrableOn_Icc]
  let g (x : ℝ) := (1+‖s‖*Real.log x)/x
  let G (x : ℝ) := Real.log x + ‖s‖*Real.log x^2/2
  have hgc : ContinuousOn g (Set.Icc A B) := by
    intro x hx; have h := zero_lt_one.trans_le (hA.trans hx.1); dsimp [g]; fun_prop (disch := positivity)
  have hi : ‖∫ x in Set.Icc A B, deriv (wt s) x * prefixSum f A x‖ ≤ E*(G B-G A) := calc
    _ ≤ ∫ x in Set.Icc A B, E*g x := by
      apply norm_integral_le_of_norm_le (hgc.const_mul E).integrableOn_Icc
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hx1 := hA.trans hx.1; have hx0 := zero_lt_one.trans_le hx1
      rw [norm_mul, (hd x hx0).deriv]; dsimp only [d]; rw [norm_div, norm_mul, Complex.norm_of_nonneg hx0.le]
      grw [hP x hx, hp x hx1, norm_sub_le, norm_mul, Complex.norm_of_nonneg (log_nonneg hx1)]
      dsimp [g]; simp; field_simp; rfl
    _ = _ := by
      rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]; congr 1
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx; rw [Set.uIcc_of_le hAB] at hx; have h := Real.hasDerivAt_log (zero_lt_one.trans_le (hA.trans hx.1)).ne'
        convert h.add (((h.pow 2).const_mul ‖s‖).div_const 2) using 1; dsimp [g]; ring
      · exact (Set.uIcc_of_le hAB ▸ hgc : ContinuousOn g (Set.uIcc A B)).intervalIntegrable
  grw [norm_sub_le, hi, norm_mul, hP B (Set.right_mem_Icc.mpr hAB)]
  rw [wt, norm_mul, Complex.norm_of_nonneg (log_nonneg hB)]; grw [hp B hB]
  dsimp [G]; have hb0 := zero_lt_one.trans_le hB
  calc _ = E*(Real.log B + (Real.log B + ‖s‖*Real.log B^2/2 - (Real.log A + ‖s‖*Real.log A^2/2))) := by field_simp
       _ ≤ _ := by apply mul_le_mul_of_nonneg_left _ hE; linarith [log_nonneg hA]

end GradedNear
