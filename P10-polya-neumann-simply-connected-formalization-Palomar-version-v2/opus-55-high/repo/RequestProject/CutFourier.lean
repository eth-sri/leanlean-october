module

public import RequestProject.CutPhase
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries

/-!
# A smooth periodic version of the cut argument and its Fourier series

Fix a cut direction `e^{iε}` (`0 < ε < 2π`) and a radius `r > 0`. We construct a smooth
`2π`-periodic function `h` with `h(t) = argCut ε (e^{it})` and `h'(t) = 1` whenever `e^{it}` is at
distance at least `r` from `e^{iε}`, and expand it in an absolutely convergent Fourier series
`h(t) = ∑ₖ cₖ e^{ikt}` with `∑ₖ |k| |cₖ| < ∞`. In real form (`c_{-k} = conj cₖ`), for such
`z = e^{it}`: `argCut ε z = ∑_{n ≥ 1} 2 Re(cₙ (zⁿ - 1))` and `1 = ∑_{n ≥ 1} 2 Re(i n cₙ zⁿ)`.
-/

@[expose] public section

open MeasureTheory Set Filter AddCircle
open scoped Real Topology ComplexConjugate

noncomputable section

namespace PolyaNeumann

variable (n : ℤ) (x : ℝ) {f : ℝ → ℂ}

lemma two_pi_pos' : 0 < 2 * π := by positivity

lemma norm_fourier_coe : ‖fourier (T := 2 * π) n x‖ = 1 := by
  rw [fourier_coe_apply]
  have : (2 * π * Complex.I * n * x / (2 * π : ℝ)) = (n * x : ℝ) * Complex.I := by
    push_cast
    field_simp
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma fourier_coe_two_pi :
    fourier (T := 2 * π) n x = Complex.exp (n * x * Complex.I) := by
  rw [fourier_coe_apply]
  push_cast
  field_simp

/-- Bound for Fourier coefficients on `[0, 2π]`. -/
lemma norm_fourierCoeffOn_le {M : ℝ} (hf : ∀ x ∈ Icc 0 (2 * π), ‖f x‖ ≤ M) (k : ℤ) :
    ‖fourierCoeffOn two_pi_pos' f k‖ ≤ M := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have h2 : ‖∫ x in 0..(2 * π), fourier (T := 2 * π) (-k) x • f x‖ ≤
      M * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    rw [uIoc_of_le two_pi_pos'.le] at hx
    rw [norm_smul, norm_fourier_coe]
    grind
  rw [sub_zero, abs_of_pos two_pi_pos'] at h2
  rw [sub_zero, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / (2 * π) * ‖_‖ ≤ 1 / (2 * π) * (M * (2 * π)) := by gcongr
    _ = M := by field_simp

/-- Integration by parts for Fourier coefficients of a periodic function. -/
lemma fourierCoeffOn_deriv {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hper : f 0 = f (2 * π)) (k : ℤ) :
    fourierCoeffOn two_pi_pos' f' k = (Complex.I * k) * fourierCoeffOn two_pi_pos' f k := by
  by_cases hk : k = 0
  · simp_all [fourierCoeffOn_eq_integral, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)       (hf'.intervalIntegrable _ _)]
  · rw [fourierCoeffOn_of_hasDerivAt two_pi_pos' hk (fun x _ => hf x) (hf'.intervalIntegrable _ _),
      ← hper]
    push_cast
    field_simp
    ring_nf

/-- Pointwise convergence of an absolutely summable Fourier series on `[0, 2π)`. -/
lemma hasSum_fourierCoeffOn {f : ℝ → ℂ} (hc : Continuous f) (hper : f 0 = f (2 * π))
    (hs : Summable (fourierCoeffOn two_pi_pos' f)) {t : ℝ} (ht : t ∈ Ico 0 (2 * π)) :
    HasSum (fun k  => fourierCoeffOn two_pi_pos' f k * Complex.exp (k * t * Complex.I))
      (f t) := by
  haveI : Fact (0 < 2 * π) := ⟨two_pi_pos'⟩
  set F : C(AddCircle (2 * π), ℂ) :=
    ⟨AddCircle.liftIco (2 * π) 0 f, AddCircle.liftIco_continuous (by simp_all) hc.continuousOn⟩ with hF
  have hcoef : fourierCoeff F = fourierCoeffOn two_pi_pos' f := by
    funext k
    simp_all [fourierCoeff_liftIco_eq]
  have h := has_pointwise_sum_fourier_series_of_summable  (by rw [hcoef]; assumption)
    t
  rw [hcoef] at h
  have hFt : F t = f t := AddCircle.liftIco_coe_apply (by simp_all)
  rw [hFt] at h
  simpa only [smul_eq_mul, fourier_coe_two_pi] using h

/-- Fourier coefficients of a real-valued function: `c_{-k} = conj c_k`. -/
lemma fourierCoeffOn_neg_of_real (g : ℝ → ℝ) (k : ℤ) :
    fourierCoeffOn two_pi_pos' (fun t => (g t : ℂ)) (-k) =
      conj (fourierCoeffOn two_pi_pos' (fun t => (g t : ℂ)) k) := by
  simp only [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le two_pi_pos'.le,
    Complex.real_smul, map_mul, Complex.conj_ofReal, ← integral_conj]
  norm_num

/-- Absolute summability of the Fourier coefficients of the derivative of a periodic function with
three continuous derivatives (periodic up to order two). -/
lemma summable_norm_fourierCoeffOn_deriv {f f1 f2 f3 : ℝ → ℂ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) (h3 : ∀ x, HasDerivAt f2 (f3 x) x) (hc3 : Continuous f3)
    (p0 : f 0 = f (2 * π)) (p1 : f1 0 = f1 (2 * π)) (p2 : f2 0 = f2 (2 * π)) :
    Summable (fun k => ‖fourierCoeffOn two_pi_pos' f1 k‖) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn  hc3.continuousOn
  have hb : ∀ k : ℤ, ‖fourierCoeffOn two_pi_pos' f1 k‖ ≤ M * (1 / k ^ 2) := by
    intro k
    have e1 := fourierCoeffOn_deriv h1 (continuous_iff_continuousAt.mpr fun x => (h2 x).continuousAt) p0 k
    by_cases hk : k = 0
    · simp_all
    · have hb3 := norm_fourierCoeffOn_le hM k
      rw [fourierCoeffOn_deriv h3 hc3 p2 k, fourierCoeffOn_deriv h2 (continuous_iff_continuousAt.mpr fun x => (h3 x).continuousAt) p1 k] at hb3
      simp  at hb3
      rw [one_div, ← div_eq_mul_inv, le_div_iff₀ (by positivity), ← sq_abs]
      linarith
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb ?_
  exact ((Real.summable_one_div_int_pow ).mpr one_lt_two).mul_left M

/-- A smooth bump `ρ ≥ 0` supported in `(ε - δ, ε + δ) ⊂ (0, 2π)` with `∫₀^{2π} ρ = 1`. -/
lemma exists_cut_bump {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε) (hεδ : ε + δ < 2 * π) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ t, δ ≤ |t - ε| → ρ t = 0) ∧
      (∫ t in 0..(2 * π), ρ t) = 1 ∧ ρ =ᶠ[𝓝 0] 0 ∧ ρ =ᶠ[𝓝 (2 * π)] 0 := by
  let f : ContDiffBump ε := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  refine ⟨f.normed volume, f.contDiff_normed, fun t ht => ?_, ?_, ?_, ?_⟩
  · rw [← Function.notMem_support, f.support_normed_eq]
    simpa [Real.dist_eq] using ht
  · rw [intervalIntegral.integral_of_le two_pi_pos'.le,
      setIntegral_eq_integral_of_forall_compl_eq_zero, f.integral_normed ]
    intro t ht
    rw [← Function.notMem_support, f.support_normed_eq]
    intro hb
    rw [Metric.mem_ball, Real.dist_eq] at hb
    grind
  · rw [← notMem_tsupport_iff_eventuallyEq, f.tsupport_normed_eq]
    simp 
    grind
  · rw [← notMem_tsupport_iff_eventuallyEq, f.tsupport_normed_eq]
    simp only [Metric.mem_closedBall, Real.dist_eq]
    grind

/-- `e^{it}` is within `|t - ε|` of `e^{iε}`. -/
lemma norm_exp_sub_exp_le (t ε : ℝ) :
    ‖Complex.exp (t * Complex.I) - Complex.exp (ε * Complex.I)‖ ≤ |t - ε| := by
  have h : Complex.exp (t * Complex.I) - Complex.exp (ε * Complex.I) =
      Complex.exp (ε * Complex.I) * (Complex.exp (Complex.I * (t - ε : ℝ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t - ε)
  assumption

/-- **Fourier expansion of the cut argument.** For `0 < ε < 2π` and `r > 0` there are
coefficients `cₙ` with `∑ n |cₙ| < ∞` such that every unimodular `z` with `|z - e^{iε}| ≥ r`
satisfies `argCut ε z = ∑_{n ≥ 1} 2 Re(cₙ (zⁿ - 1))` and `1 = ∑_{n ≥ 1} 2 Re(i n cₙ zⁿ)`. -/
theorem exists_cutFourier {ε r : ℝ} (hε0 : 0 < ε) (hε : ε < 2 * π) (hr : 0 < r) :
    ∃ c : ℕ → ℂ, Summable (fun n  => n * ‖c n‖) ∧
      ∀ z : ℂ, ‖z‖ = 1 → r ≤ ‖z - Complex.exp (ε * Complex.I)‖ →
        HasSum (fun n  => 2 * (c n * (z ^ n - 1)).re) (argCut ε z) ∧
        HasSum (fun n  => 2 * (Complex.I * n * c n * z ^ n).re) 1 := by
  set δ := min (r / 2) (min ε (2 * π - ε) / 2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ2 : δ ≤ min ε (2 * π - ε) / 2 := min_le_right _ _
  have hδε : δ < ε := by
    grind
  obtain ⟨ρ, hρ, hρ0, hρint, hρe0, hρe2⟩ := exists_cut_bump hδ hδε (by
    grind)
  have hρd  := hρ.differentiable (by simp)
  have hρ'  := (contDiff_infty_iff_deriv.mp hρ).2
  have hρc''  := (contDiff_infty_iff_deriv.mp hρ').2.continuous
  set h : ℝ → ℝ := fun t => t - 2 * π * ∫ s in 0..t, ρ s with hh
  set F : ℝ → ℂ := fun t => h t with hF
  set F1 : ℝ → ℂ := fun t => (1 - 2 * π * ρ t : ℝ) with hF1
  set F2 : ℝ → ℂ := fun t => (-(2 * π * deriv ρ t) : ℝ) with hF2
  set F3 : ℝ → ℂ := fun t => (-(2 * π * deriv (deriv ρ) t) : ℝ) with hF3
  have d1 : ∀ x, HasDerivAt F (F1 x) x := fun x =>
    ((hasDerivAt_id x).sub (((hρ.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt).const_mul
      (2 * π))).ofReal_comp
  have d2 : ∀ x, HasDerivAt F1 (F2 x) x := fun x =>
    ((((hρd x).hasDerivAt).const_mul (2 * π)).const_sub 1).ofReal_comp
  have d3  := fun x =>
    (((hρ'.differentiable (by simp) x).hasDerivAt).const_mul (2 * π)).neg.ofReal_comp
  have hc1  := continuous_iff_continuousAt.mpr fun x => (d2 x).continuousAt
  have hc3 : Continuous F3 := by fun_prop
  have hdρ0 : deriv ρ 0 = 0 := by simp [hρe0.deriv_eq]
  have hdρ2 : deriv ρ (2 * π) = 0 := by simp [hρe2.deriv_eq]
  have p0 : F 0 = F (2 * π) := by
    simp_all
  have p1 : F1 0 = F1 (2 * π) := by
    grind
  have hs1 := summable_norm_fourierCoeffOn_deriv d1 d2 d3 hc3 p0 p1 (by simp_all)
  set C : ℤ → ℂ := fourierCoeffOn two_pi_pos' F with hC
  have hC1 : ∀ k : ℤ, fourierCoeffOn two_pi_pos' F1 k = (Complex.I * k) * C k :=
    fourierCoeffOn_deriv d1 hc1 p0
  have hCneg : ∀ k : ℤ, C (-k) = conj (C k) := fun k => fourierCoeffOn_neg_of_real h k
  have hsC : Summable C := by
    refine Summable.of_norm ?_
    refine (hs1.add ((hasSum_ite_eq 0 ‖C 0‖).summable)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun k => ?_)
    by_cases hk : k = 0
    · simp_all
    · rw [if_neg hk, add_zero, hC1, norm_mul, Complex.norm_mul, Complex.norm_I, one_mul,
        Complex.norm_intCast]
      have : 1 ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]; grind
      nlinarith [norm_nonneg (C k)]
  refine ⟨fun n => C n, ?_, fun z hz hzr => ?_⟩
  · have := hs1.comp_injective Nat.cast_injective
    refine this.congr (fun n => ?_)
    simp_all
  -- the angle of `z`
  set t := argNeg z + 2 * π with ht
  have hz_exp : Complex.exp (t * Complex.I) = z := by
    simp [ht, add_mul, Complex.exp_add, exp_argNeg hz, Complex.exp_two_pi_mul_I, mul_one]
  have ht_mem : t ∈ Ico 0 (2 * π) := by
    rw [ht, argNeg]
    have hlo := Complex.neg_pi_lt_arg z
    have hhi := Complex.arg_le_pi z
    grind 
  have htε : δ ≤ |t - ε| := by
    have := norm_exp_sub_exp_le t ε
    grind
  -- values of `h` and `h'` at `t`
  have hρt  := hρ0 t htε
  have hF1t : F1 t = 1 := by simp_all
  have hFt : F t = argCut ε z := by
    simp only [hF]
    congr 1
    rw [argCut]
    split_ifs with hlt
    · have hle : t ≤ ε - δ := by
        grind
      have : ∫ s in 0..t, ρ s = 0 := by
        refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun s hs => ?_)
        grind
      simp_all
    · have hge : ε + δ ≤ t := by
        grind
      have h2 : ∫ s in t..(2 * π), ρ s = 0 := by
        refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun s hs => ?_)
        grind
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hρ.continuous.intervalIntegrable (μ := volume) 0 t)
        (hρ.continuous.intervalIntegrable  t (2 * π))
      simp_all
  -- Fourier series
  have hcF  := continuous_iff_continuousAt.mpr fun x => (d1 x).continuousAt
  have hpow : ∀ n : ℕ, Complex.exp ((n : ℤ) * t * Complex.I) = z ^ n := by
    intro n
    rw [← hz_exp, ← Complex.exp_nat_mul]
    push_cast; ring
  have hpowneg : ∀ n : ℕ, Complex.exp ((-n : ℤ) * t * Complex.I) = conj (z ^ n) := by
    simp [← hpow, ← Complex.exp_conj]
  have hpow0 : ∀ n : ℕ, Complex.exp ((n : ℤ) * (0 : ℝ) * Complex.I) = 1 := by
    simp
  have hpowneg0 : ∀ n : ℕ, Complex.exp ((-n : ℤ) * (0 : ℝ) * Complex.I) = 1 := by
    simp
  have hA := (hasSum_fourierCoeffOn hcF p0 hsC ht_mem).nat_add_neg
  have hB := (hasSum_fourierCoeffOn hcF p0 hsC ⟨le_rfl, two_pi_pos'⟩).nat_add_neg
  rw [← hC] at hA hB
  simp only [hpow, hpowneg, hCneg] at hA
  simp only [hpow0, hpowneg0, hCneg, mul_one] at hB
  have hF0 : F 0 = 0 := by simp_all
  refine ⟨?_, ?_⟩
  · have hD := hA.sub hB
    rw [hFt, hF0] at hD
    simp only [Int.cast_zero, zero_mul] at hD
    rw [add_sub_add_right_eq_sub, sub_zero] at hD
    refine Complex.hasSum_ofReal.mp ?_
    convert hD using 1
    funext n
    rw [← map_mul, Complex.add_conj, Complex.add_conj]
    simp 
    ring
  · have hE := (hasSum_fourierCoeffOn hc1 p1 hs1.of_norm ht_mem).nat_add_neg
    simp only [hpow, hpowneg, hC1, hCneg, hF1t] at hE
    simp only [Int.cast_zero, mul_zero, zero_mul, add_zero] at hE
    refine Complex.hasSum_ofReal.mp ?_
    convert hE using 1
    · funext n
      have : Complex.I * ((-n : ℤ)) * conj (C n) * conj (z ^ n) =
          conj (Complex.I * n * C n * z ^ n) := by
        norm_num
      rw [this, Int.cast_natCast, Complex.add_conj]

end PolyaNeumann

end
