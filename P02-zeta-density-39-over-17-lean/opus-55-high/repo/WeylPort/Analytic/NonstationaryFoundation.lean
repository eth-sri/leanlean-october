module
/- Extracted from PNT (Apache-2.0), via pinned McColm source; see analytic-extraction.json. -/
public import Mathlib
import WeylPort.Analytic.RealLaplace

@[expose] public section

-- Lean 4.34 elaborator compatibility; kernel checking stays enabled.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ZetaAppendix
open Real Complex MeasureTheory Finset Filter Topology Set Summable
private noncomputable def e (α : ℝ) : ℂ := exp (2 * π * I * α)
/-- For C¹ functions `g` and `F`, the error in integration by parts is bounded by
`sup ‖F‖ · ∫ |g'|`. -/
private theorem lemma_IBP_bound_C1 {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hg : ContDiffOn ℝ 1 g (Icc a b)) (hF : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * ∫ t in Icc a b, |deriv g t| := by
  have hint_parts : ∫ t in Icc a b, (g t) * (deriv F t) =
      (g b) * (F b) - (g a) * (F a) - ∫ t in Icc a b, (F t) * (deriv g t) := by
    pm_5634
    · rw [Set.uIcc_of_le hab.le]
      exact ContinuousOn.mul
        (continuous_ofReal.comp_continuousOn hg.continuousOn) hF.continuousOn
    pm_1597
    pm_1598
  pm_1599

/-- Integration by parts bound for `C¹` monotone functions.
For `C¹` monotone `g` and `C¹` `F`, `‖∫ g F' - [gF]‖ ≤ sup ‖F‖ · (g(b) - g(a))`. -/
private theorem lemma_IBP_bound_C1_monotone {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hg : ContDiffOn ℝ 1 g (Icc a b)) (hg_mono : MonotoneOn g (Icc a b))
    (hF : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
    (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) := by pm_1600

open scoped unitInterval in
set_option hygiene false in
macro "pf_6" : tactic => `(tactic| (
  intro x y hxy
  simp only [bernsteinApproximation, smul_eq_mul, ContinuousMap.coe_sum, ContinuousMap.coe_mul,
    ContinuousMap.coe_const, Finset.sum_apply, Pi.mul_apply, Function.const_apply]
  have hmono : ∀ i j : Fin (n + 1), i ≤ j → f (bernstein.z i) ≤ f (bernstein.z j) :=
    fun i j hij ↦ hf <| Subtype.mk_le_mk.mpr <| by simpa [bernstein.z] using by gcongr; aesop
  have hsum : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (bernstein n i x * bernstein n j y - bernstein n i y * bernstein n j x) *
        (f (bernstein.z j) - f (bernstein.z i)) ≥ 0 := by
    refine Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
    by_cases hij : i ≤ j
    · refine mul_nonneg ?_ (sub_nonneg.mpr (hmono i j hij))
      have hineq : x.val ^ (i : ℕ) * (1 - x.val) ^ (n - i : ℕ) * y.val ^ (j : ℕ) *
          (1 - y.val) ^ (n - j : ℕ) ≥ x.val ^ (j : ℕ) * (1 - x.val) ^ (n - j : ℕ) *
          y.val ^ (i : ℕ) * (1 - y.val) ^ (n - i : ℕ) := by
        have hdiv : y.val ^ (j - i : ℕ) * (1 - x.val) ^ (j - i : ℕ) ≥
            x.val ^ (j - i : ℕ) * (1 - y.val) ^ (j - i : ℕ) := by
          rw [← mul_pow, ← mul_pow]
          exact pow_le_pow_left₀ (mul_nonneg (Subtype.property x |>.1)
            (sub_nonneg.2 (Subtype.property y |>.2)))
            (by nlinarith [show (x : ℝ) ≤ y from hxy, show (x : ℝ) ≥ 0 from Subtype.property x |>.1,
              show (y : ℝ) ≤ 1 from Subtype.property y |>.2]) _
        simp_all only [Finset.mem_univ, ge_iff_le, mul_comm, mul_left_comm, mul_assoc]
        convert mul_le_mul_of_nonneg_left hdiv (show 0 ≤ (x : ℝ) ^ (i : ℕ) * (y : ℝ) ^ (i : ℕ) *
            (1 - x : ℝ) ^ (n - j : ℕ) * (1 - y : ℝ) ^ (n - j : ℕ) by
          exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (mod_cast x.2.1) _)
            (pow_nonneg (mod_cast y.2.1) _)) (pow_nonneg (sub_nonneg.2 <| mod_cast x.2.2) _))
            (pow_nonneg (sub_nonneg.2 <| mod_cast y.2.2) _)) using 1 <;> ring_nf
        · simp only [mul_assoc, ← pow_add, add_tsub_cancel_of_le (show (i : ℕ) ≤ j from hij),
            mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq, Icc.coe_eq_zero, Fin.val_eq_zero_iff]
          exact Or.inl <| Or.inl <| Or.inl <|
            by rw [tsub_add_tsub_cancel (mod_cast Fin.is_le _) (mod_cast hij)]
        · simp only [mul_assoc, ← pow_add, add_tsub_cancel_of_le (show (i : ℕ) ≤ j from hij),
            mul_eq_mul_left_iff, mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq, Icc.coe_eq_zero,
            Fin.val_eq_zero_iff]
          exact Or.inl <| Or.inl <| Or.inl <|
            by rw [tsub_add_tsub_cancel (mod_cast Fin.is_le _) (mod_cast hij)]
      simp_all only [Finset.mem_univ, ge_iff_le, bernstein, Polynomial.toContinuousMapOn_apply,
        Polynomial.toContinuousMap_apply, sub_nonneg]
      simp_all only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
      convert mul_le_mul_of_nonneg_left hineq
        (show 0 ≤ (n.choose i : ℝ) * (n.choose j : ℝ) by positivity) using 1 <;> ring
    · refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
      · norm_num [bernstein, bernsteinPolynomial]
        have hexp : (x.val : ℝ) ^ (i : ℕ) * (y.val : ℝ) ^ (j : ℕ) ≤
            (x.val : ℝ) ^ (j : ℕ) * (y.val : ℝ) ^ (i : ℕ) := by
          rw [show (i : ℕ) = j + (i - j) by rw [Nat.add_sub_cancel' (le_of_not_ge hij)]]
          ring_nf
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by exact_mod_cast x.2.1)
            (by exact_mod_cast hxy) _) (mul_nonneg (pow_nonneg (by exact_mod_cast x.2.1) _)
            (pow_nonneg (by exact_mod_cast y.2.1) _))
        have hexp2 : (1 - x.val) ^ (n - i.val) * (1 - y.val) ^ (n - j.val) ≤
            (1 - x.val) ^ (n - j.val) * (1 - y.val) ^ (n - i.val) := by
          rw [show n - (i : ℕ) = n - (j : ℕ) - (i - j : ℕ) by
            rw [tsub_tsub, add_tsub_cancel_of_le (mod_cast le_of_not_ge hij)]]
          rw [show (1 - x.val) ^ (n - j.val) = (1 - x.val) ^ (n - j.val - (i.val - j.val)) *
              (1 - x.val) ^ (i.val - j.val) by rw [← pow_add, Nat.sub_add_cancel
              (show (i.val - j.val) ≤ n - j.val from Nat.sub_le_sub_right (mod_cast Fin.is_le i) _)],
            show (1 - y.val) ^ (n - j.val) = (1 - y.val) ^ (n - j.val - (i.val - j.val)) *
              (1 - y.val) ^ (i.val - j.val) by rw [← pow_add, Nat.sub_add_cancel
              (show (i.val - j.val) ≤ n - j.val from Nat.sub_le_sub_right (mod_cast Fin.is_le i) _)]]
          rw [mul_assoc, mul_comm ((1 - x.val) ^ (i.val - j.val))]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (sub_nonneg.2 <| mod_cast y.2.2)
            (sub_le_sub_left (mod_cast hxy) _) _) <| pow_nonneg (sub_nonneg.2 <| mod_cast y.2.2) _)
            <| pow_nonneg (sub_nonneg.2 <| mod_cast x.2.2) _
        convert mul_le_mul_of_nonneg_left (mul_le_mul hexp hexp2 (?_) (?_))
          (show (0 : ℝ) ≤ (n.choose i : ℝ) * (n.choose j : ℝ) by positivity) using 1 <;> ring_nf
        · exact mul_nonneg (pow_nonneg (sub_nonneg.2 <| mod_cast x.2.2) _)
            (pow_nonneg (sub_nonneg.2 <| mod_cast y.2.2) _)
        · exact mul_nonneg (pow_nonneg (Subtype.property x |>.1) _)
            (pow_nonneg (Subtype.property y |>.1) _)
      · exact sub_nonpos_of_le <| hmono _ _ <| le_of_not_ge hij
  contrapose! hsum
  simp_all only [mul_comm, mul_sub, sum_sub_distrib, ← Finset.mul_sum _ _ _, bernstein.probability,
    one_mul, sub_neg]
  simp_all only [← mul_assoc, ← sum_comm, ← sum_mul, ← Finset.mul_sum _ _ _, bernstein.probability,
    mul_one]
  linarith))
open scoped unitInterval in
open scoped unitInterval in
/-- The Bernstein approximation of a monotone function is monotone. -/
private theorem bernsteinApproximation_monotone (n : ℕ) (f : C(I, ℝ)) (hf : Monotone f) :
    Monotone (bernsteinApproximation n f) := by pf_6

open scoped unitInterval in
set_option hygiene false in
macro "pf_92" : tactic => `(tactic| (
  intro ε hεpos
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp (tendsto_iff_norm_sub_tendsto_zero.mp
    (bernsteinApproximation_uniform f)) ε hεpos
  have hn : ‖bernsteinApproximation n f - f‖ < ε := by simpa [dist_zero_right, norm_norm] using hn n le_rfl
  let P : ℝ → ℝ := fun x ↦ ∑ k : Fin (n + 1), (n.choose k : ℝ) * x ^ (k : ℕ) * (1 - x) ^ (n - k : ℕ) * f (bernstein.z k)
  have hP (x) (hx : x ∈ I) : P x = bernsteinApproximation n f ⟨x, hx⟩ := by
    simp [P, bernsteinApproximation, bernstein, bernsteinPolynomial, mul_comm]
  refine ⟨P, ContDiff.contDiffOn <| ContDiff.sum fun k _ ↦ ?_, fun x hx y hy hxy ↦ ?_, fun x ↦ ?_⟩
  · apply_rules [ContDiff.mul, ContDiff.pow, contDiff_const, contDiff_id, ContDiff.sub]
  · rw [hP x hx, hP y hy]
    exact bernsteinApproximation_monotone n f hf_mono (Subtype.mk_le_mk.mpr hxy)
  · rw [abs_sub_comm, hP x x.2]
    exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (bernsteinApproximation n f - f) x) hn))
open scoped unitInterval in
open scoped unitInterval in
/-- Continuous monotone functions on `[0,1]` can be uniformly approximated by smooth monotone
functions (polynomials). -/
private theorem lemma_approx_monotone_C1_I (f : C(I, ℝ)) (hf_mono : Monotone f) :
    ∀ ε > 0, ∃ P : ℝ → ℝ, ContDiffOn ℝ 1 P I ∧ MonotoneOn P I ∧ ∀ x : I, |f x - P x| < ε := by pf_92

/-- Continuous monotone functions on a compact interval can be uniformly approximated by `C¹`
monotone functions. -/
private theorem lemma_approx_monotone_C1 {a b : ℝ} (hab : a < b) (g : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Set.Icc a b)) (hg_mono : MonotoneOn g (Set.Icc a b)) :
    ∀ ε > 0, ∃ g' : ℝ → ℝ, ContDiffOn ℝ 1 g' (Set.Icc a b) ∧ MonotoneOn g' (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, |g x - g' x| < ε := by pm_1601

/-- Integration by parts bound for continuous monotone functions.
For continuous monotone `g` and `C¹` `F`, `‖∫ g F' - [gF]‖ ≤ sup ‖F‖ · (g(b) - g(a))`. -/
private theorem lemma_IBP_bound_monotone {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_mono : MonotoneOn g (Icc a b))
    (hF_C1 : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
    (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) := by pm_1602

/-- Integration by parts bound for continuous functions with antitone absolute value.
If `|g|` is antitone, `‖∫ g F'‖ ≤ sup ‖F‖ · 2 |g(a)|`. -/
private theorem lemma_IBP_bound_abs_antitone {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hgcont : ContinuousOn g (Icc a b)) (hganti : AntitoneOn (|g ·|) (Icc a b))
    (hF : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖∫ t in Icc a b, (g t : ℂ) * deriv F t‖ ≤ (⨆ t ∈ Icc a b, ‖F t‖) * (2 * |g a|) := by pm_1603

set_option backward.isDefEq.respectTransparency false in

set_option hygiene false in
macro "pf_43" : tactic => `(tactic| (
  let F : ℝ → ℂ := fun t ↦ (1 / (2 * Real.pi * I)) * (exp (2 * Real.pi * I * φ t))
  have h_integral_bound : ‖∫ t in Set.Icc a b, (g t : ℂ) * (deriv F t)‖ ≤ (⨆ t ∈ Set.Icc a b, ‖F t‖) * (2 * |g a|) :=
    lemma_IBP_bound_abs_antitone ha g F hg_cont hg_mon <|
      ContDiffOn.mul contDiffOn_const <| contDiff_exp.comp_contDiffOn <|
        ContDiffOn.mul contDiffOn_const <| ofRealCLM.contDiff.comp_contDiffOn hφ_C1
  have h_deriv_F : ∀ t ∈ Set.Ioo a b, deriv F t = (exp (2 * Real.pi * I * φ t)) * (deriv φ t) := by
    intro t ht
    rw [deriv_const_mul]
    · norm_num [Complex.exp_ne_zero, mul_comm]
      erw [HasDerivAt.deriv (HasDerivAt.comp t (Complex.hasDerivAt_exp _) (HasDerivAt.mul (HasDerivAt.ofReal_comp
        (hφ_C1.differentiableOn_one |> DifferentiableOn.hasDerivAt <| Icc_mem_nhds ht.1 ht.2)) <| hasDerivAt_const ..))]
      norm_num
      ring_nf
      simp
    · apply Complex.differentiableAt_exp.comp
      apply DifferentiableAt.const_mul <| ofRealCLM.differentiableAt.comp _ <| DifferentiableOn.differentiableAt
        hφ_C1.differentiableOn_one (Icc_mem_nhds ht.1 ht.2) ..
  have h_norm_F : ⨆ t ∈ Set.Icc a b, ‖F t‖ = 1 / (2 * Real.pi) := by
    dsimp only [F]
    rw [@ciSup_eq_of_forall_le_of_forall_lt_exists_gt] <;> norm_num [norm_exp, abs_of_nonneg pi_pos.le]
    · exact fun t ↦ by rw [ciSup_eq_ite]; split_ifs <;> norm_num; linarith [pi_pos]
    · exact fun w hw ↦ ⟨a, hw.trans_le <| by rw [ciSup_pos]; norm_num; linarith⟩
  have h_integral_subst : ‖∫ t in Set.Icc a b, (g t : ℂ) * (deriv F t)‖ = ‖∫ t in Set.Icc a b,
      (h t : ℂ) * (exp (2 * Real.pi * I * φ t))‖ := by
    simp only [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by rw [h_deriv_F t ht, hg t]]
    simp only [div_eq_mul_inv, ofReal_mul, ofReal_inv, mul_comm, mul_left_comm, mul_assoc]
    refine congr_arg Norm.norm <| setIntegral_congr_fun measurableSet_Ioo <| fun x hx ↦ ?_
    simp [mul_inv_cancel_left₀ (ofReal_ne_zero.mpr (hφ'_ne0 x (Set.Ioo_subset_Icc_self hx)))]
  exact h_integral_subst ▸ h_integral_bound.trans (by rw [h_norm_F]; ring_nf; norm_num [pi_pos.ne'])))

section
variable {a b : ℝ} (ha : a < b) (φ : ℝ → ℝ) (hφ_C1 : ContDiffOn ℝ 1 φ (Set.Icc a b)) (hφ'_ne0 : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) (h g : ℝ → ℝ) (hg : ∀ t, g t = h t / deriv φ t) (hg_cont : ContinuousOn g (Set.Icc a b)) (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b))
include a b ha φ hφ_C1 hφ'_ne0 h g hg hg_cont hg_mon
private theorem lemma_aachmonophase :
    ‖∫ t in Set.Icc a b, h t * e (φ t)‖ ≤ |g a| / π := by pf_43

/-- Public form of the non-stationary phase estimate used in the sharp-zeta
Poisson argument.  This wrapper exposes the proved first-derivative test
without exposing the appendix's private notation `e`. -/
theorem nonstationary_phase_integral_bound :
    ‖∫ t in Set.Icc a b,
        (h t : ℂ) * Complex.exp (2 * Real.pi * I * (φ t : ℂ))‖ ≤
      |g a| / Real.pi := by
  simpa only [e] using
    lemma_aachmonophase ha φ hφ_C1 hφ'_ne0 h g hg hg_cont hg_mon
end

end ZetaAppendix
