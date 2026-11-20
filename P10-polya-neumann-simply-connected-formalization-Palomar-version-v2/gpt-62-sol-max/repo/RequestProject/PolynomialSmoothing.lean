module

public import RequestProject.SmoothCompactExtension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Metric MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution Polynomial

/-- Integrating a polynomial kernel against a compactly supported function
leaves a polynomial in the free variables. -/
private theorem analytic_polynomial_convolution (q : ℝ[X]) {f : ℂ → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (x₀ : ℂ) :
    AnalyticAt ℝ (fun x : ℂ => ∫ y, q.eval (‖x - y‖ ^ 2) * f y) x₀ := by
  let p : MvPolynomial (Fin 4) ℝ := q.aeval
    ((MvPolynomial.X 0 - MvPolynomial.X 2) ^ 2 + (MvPolynomial.X 1 - MvPolynomial.X 3) ^ 2)
  let a (x y : ℂ) : Fin 4 → ℝ := ![x.re, x.im, y.re, y.im]
  have hpoly (x y : ℂ) : p.eval (a x y) = q.eval (‖x - y‖ ^ 2) := by
    let E := (MvPolynomial.aeval (a x y) : MvPolynomial (Fin 4) ℝ →ₐ[ℝ] ℝ)
    change E (q.aeval _) = _
    rw [← Polynomial.aeval_algHom_apply E, Polynomial.coe_aeval_eq_eval]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [E, a, pow_two]
  let A (d : Fin 4 →₀ ℕ) (x : ℂ) := p.coeff d * x.re ^ d 0 * x.im ^ d 1
  let B (d : Fin 4 →₀ ℕ) (y : ℂ) := y.re ^ d 2 * y.im ^ d 3 * f y
  have heval (x y : ℂ) : q.eval (‖x - y‖ ^ 2) * f y = ∑ d ∈ p.support, A d x * B d y := by
    rw [← hpoly, MvPolynomial.eval_eq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    change (p.coeff d * d.prod (fun i n => a x y i ^ n)) * f y = _
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [a, B, Fin.prod_univ_succ]
    ring
  have hBi (d) : Integrable (B d) :=
    (show Continuous (B d) by fun_prop).integrable_of_hasCompactSupport hc.mul_left
  have h (x : ℂ) : (∫ y, q.eval (‖x - y‖ ^ 2) * f y) =
      ∑ d ∈ p.support, A d x * ∫ y, B d y := by
    simp_rw [heval]
    rw [integral_finset_sum _ (fun d _ => (hBi d).const_mul _)]
    simp  [integral_const_mul]
  simp_rw [h]
  apply Finset.analyticAt_fun_sum
  intro d _
  exact (((analyticAt_const.mul ((Complex.reCLM.analyticAt x₀).pow _)).mul
    ((Complex.imCLM.analyticAt x₀).pow _)).mul analyticAt_const :
      AnalyticAt ℝ (fun x : ℂ => A d x * ∫ y, B d y) x₀)

private theorem convolution_poly_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℂ → E} (hg : Continuous g) (hgc : HasCompactSupport g)
    {k l : ℂ → ℝ} (hk : Continuous k) (hl : Continuous l) {x : ℂ} {ε : ℝ}
    (hkl : ∀ y ∈ tsupport g, ‖k (x - y) - l (x - y)‖ ≤ ε) :
    ‖(k ⋆[lsmul ℝ ℝ] g) x - (l ⋆[lsmul ℝ ℝ] g) x‖ ≤ ε * ∫ y, ‖g y‖ := by
  have hi (a : ℂ → ℝ) (ha : Continuous a) : Integrable (fun y => a (x - y) • g y) :=
    (show Continuous (fun y => a (x - y) • g y) by fun_prop).integrable_of_hasCompactSupport
      hgc.smul_left
  rw [← convolution_flip, ← convolution_flip (f := l)]
  simp  [convolution_def, flip_apply, lsmul_apply]
  rw [← integral_sub (hi k hk) (hi l hl)]
  simp only [← sub_smul, ← integral_const_mul]
  apply norm_integral_le_of_norm_le ((hg.integrable_of_hasCompactSupport hgc).norm.const_mul _)
  filter_upwards with y
  by_cases hy : y ∈ tsupport g
  · rw [norm_smul]; gcongr; tauto
  · rw [image_eq_zero_of_notMem_tsupport hy, smul_zero, norm_zero, mul_zero]

private theorem exists_radial_kernel {r : ℝ} (hr : 0 < r) :
    ∃ k : ℝ → ℝ, Continuous k ∧ (∀ x : ℂ, 0 ≤ k (‖x‖ ^ 2)) ∧
      Function.support (fun x : ℂ => k (‖x‖ ^ 2)) ⊆ ball 0 r ∧
      (∫ x : ℂ, k (‖x‖ ^ 2)) = 1 := by
  let m (t : ℝ) := max 0 (r ^ 2 - t)
  let K (x : ℂ) := m (‖x‖ ^ 2)
  have hK : Continuous K := by fun_prop
  have hs : Function.support K = ball 0 r := by
    ext x
    rw [mem_ball_zero_iff]
    change max 0 (r ^ 2 - ‖x‖ ^ 2) ≠ 0 ↔ _
    simp  [ne_eq, max_eq_left_iff, not_le, sub_pos, sq_lt_sq,
      abs_of_nonneg (norm_nonneg _), abs_of_pos hr]
  have hc : HasCompactSupport K := by
    rw [HasCompactSupport, tsupport, hs, closure_ball _ hr.ne']
    exact isCompact_closedBall _ _
  have hm : 0 ≤ K := fun _ => le_max_left _ _
  have hpos : 0 < ∫ x, K x := by
    rw [integral_pos_iff_support_of_nonneg hm (hK.integrable_of_hasCompactSupport hc), hs]
    exact isOpen_ball.measure_pos volume ⟨0, mem_ball_self hr⟩
  let c := ∫ x, K x
  refine ⟨fun t => c⁻¹ * m t, by fun_prop,
    fun x => mul_nonneg (inv_nonneg.mpr hpos.le) (hm x), ?_, ?_⟩
  · intro x hx
    by_contra hn
    rw [← hs] at hn
    exact hx (mul_eq_zero_of_right _ (Function.notMem_support.mp hn))
  · change ∫ x, c⁻¹ * K x = 1
    rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

/-- Approximation in value and derivative on a ball by real-analytic functions. -/
theorem exists_analytic_C1_approximation {f : ℂ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {R ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℂ → ℝ, (∀ z, AnalyticAt ℝ P z) ∧ ∀ z ∈ closedBall 0 R,
      ‖P z - f z‖ ≤ ε ∧ ‖fderiv ℝ P z - fderiv ℝ f z‖ ≤ ε := by
  obtain ⟨χ, hχ, hχc, _, hχone⟩ := exists_smooth_compact_cutoff
    (isCompact_closedBall (0 : ℂ) R) isOpen_univ (subset_univ _)
  let g : ℂ → ℝ := χ * f
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hχ.mul hf
  have hgc : HasCompactSupport g := hχc.mul_right
  have hge {z} (hz : z ∈ closedBall (0 : ℂ) R) : g =ᶠ[𝓝 z] f := by
    filter_upwards [hχone z hz] with y hy
    aesop
  let g' := fderiv ℝ g
  have hg' : Continuous g' := hg.continuous_fderiv (by simp)
  have hg'c : HasCompactSupport g' := hgc.fderiv ℝ
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.uniformContinuous_iff.mp
    (hgc.uniformContinuous_of_continuous hg.continuous) (ε / 2) (half_pos hε)
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.uniformContinuous_iff.mp
    (hg'c.uniformContinuous_of_continuous hg') (ε / 2) (half_pos hε)
  obtain ⟨k, hk, hk0, hks, hki⟩ := exists_radial_kernel (lt_min hr₁ hr₂)
  let K (z : ℂ) := k (‖z‖ ^ 2)
  have hKu (z : ℂ) : ‖(K ⋆ g) z - g z‖ ≤ ε / 2 := by
    rw [← dist_eq_norm]
    exact dist_convolution_le (half_pos hε).le hks hk0 hki hg.continuous.aestronglyMeasurable
      (fun x hx => (h₁ (lt_of_lt_of_le hx (min_le_left _ _))).le)
  have hKv (z : ℂ) : ‖(K ⋆[lsmul ℝ ℝ] g') z - g' z‖ ≤ ε / 2 := by
    rw [← dist_eq_norm]
    exact dist_convolution_le (half_pos hε).le hks hk0 hki hg'.aestronglyMeasurable
      (fun x hx => (h₂ (lt_of_lt_of_le hx (min_le_right _ _))).le)
  obtain ⟨D, hD⟩ := ((hgc.isCompact.union hg'c.isCompact).isBounded).subset_closedBall (0 : ℂ)
  set N := (∫ y, ‖g y‖) + (∫ y, ‖g' y‖) + 1
  have hN₁ : 0 ≤ ∫ y, ‖g y‖ := integral_nonneg fun _ => norm_nonneg _
  have hN₂ : 0 ≤ ∫ y, ‖g' y‖ := integral_nonneg fun _ => norm_nonneg _
  have hN : 0 < N := by linarith
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 ((R + D) ^ 2) k hk.continuousOn
    (ε / (2 * N)) (by positivity)
  let Q (z : ℂ) := q.eval (‖z‖ ^ 2)
  have hQc : Continuous Q := q.continuous.comp (by fun_prop)
  have hKc : Continuous K := hk.comp (by fun_prop)
  have hQK {z} (hz : z ∈ closedBall 0 R) (y : ℂ) (hy : y ∈ tsupport g ∪ tsupport g') :
      ‖Q (z - y) - K (z - y)‖ ≤ ε / (2 * N) := by
    have hz' := mem_closedBall_zero_iff.mp hz
    have hy' := mem_closedBall_zero_iff.mp (hD hy)
    exact (hq _ ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg _)
      ((norm_sub_le _ _).trans (add_le_add hz' hy')) _⟩).le
  refine ⟨Q ⋆ g, fun z => ?_, fun z hz => ?_⟩
  · rw [← convolution_flip]
    exact analytic_polynomial_convolution q hg.continuous hgc z
  · have hder := hgc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) (hQc.locallyIntegrable (μ := volume))
      (hg.of_le (by simp) : ContDiff ℝ 1 g) z
    have hder' : fderiv ℝ (Q ⋆ g) z = (Q ⋆[lsmul ℝ ℝ] g') z := hder.fderiv
    rw [← (hge hz).self_of_nhds, ← (hge hz).fderiv_eq, hder']
    constructor
    · refine (norm_sub_le_norm_sub_add_norm_sub _ ((K ⋆ g) z) _).trans ?_
      refine (add_le_add ((convolution_poly_error hg.continuous hgc hQc hKc
        (fun y hy => hQK hz y (Or.inl hy))).trans (show _ ≤ ε / 2 from ?_)) (hKu z)).trans (by linarith)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    · refine (norm_sub_le_norm_sub_add_norm_sub _ ((K ⋆[lsmul ℝ ℝ] g') z) _).trans ?_
      refine (add_le_add ((convolution_poly_error hg' hg'c hQc hKc
        (fun y hy => hQK hz y (Or.inr hy))).trans (show _ ≤ ε / 2 from ?_)) (hKv z)).trans (by linarith)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith

/-- A uniformly small smooth perturbation, Lipschitz with any prescribed positive
constant, makes a smooth function analytic near a prescribed compact set. -/
theorem exists_analytic_perturbation {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {K : Set ℂ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ z ∈ K, AnalyticAt ℝ ρ z) ∧
      (∀ z, |ρ z - f z| ≤ δ) ∧ LipschitzWith δ.toNNReal (ρ - f) := by
  obtain ⟨χ, hχ, hc, _, hχK⟩ := exists_smooth_compact_cutoff hK isOpen_univ (subset_univ _)
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  let A (z : ℂ) := ‖χ z‖ + ‖fderiv ℝ χ z‖
  have hAc := hχ.continuous.norm.add (hχ.continuous_fderiv (by simp)).norm
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) R).image hAc).isBounded.subset_closedBall (0 : ℝ)
  let N := max 0 M + 1
  have hN : 0 < N := by positivity
  have hAN (z) (hz : z ∈ closedBall (0 : ℂ) R) : A z ≤ N := by
    have h := mem_closedBall_zero_iff.mp (hM (mem_image_of_mem A hz))
    exact (le_abs_self (A z)).trans (h.trans (by grind))
  let ε := δ / N
  have hε := div_pos hδ hN
  obtain ⟨P, hP, hPε⟩ := exists_analytic_C1_approximation hf (R := R) hε
  have hPs : ContDiff ℝ (⊤ : ℕ∞) P := contDiff_iff_contDiffAt.2 fun z => (hP z).contDiffAt
  let d := χ * (P - f)
  let ρ := f + d
  have hd : ContDiff ℝ (⊤ : ℕ∞) d := hχ.mul (hPs.sub hf)
  have hρ (z) : ρ z - f z = d z := by aesop
  have hεδ : N * ε = δ := by grind
  have hdiff : Differentiable ℝ (P - f) := (hPs.sub hf).differentiable (by simp)
  have hds (z : ℂ) (hz : z ∉ tsupport χ) : d =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
    aesop
  refine ⟨ρ, hf.add hd, ?_, ?_, ?_⟩
  · intro z hz
    apply (hP z).congr
    filter_upwards [hχK z hz] with y hy
    simp only [ρ, d, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, hy, one_mul]
    ring
  · intro z
    rw [hρ]
    by_cases hz : z ∈ tsupport χ
    · change ‖χ z * (P z - f z)‖ ≤ δ
      rw [norm_mul, ← hεδ]
      exact mul_le_mul ((le_add_of_nonneg_right (norm_nonneg _)).trans (hAN z (hR hz)))
        (hPε z (hR hz)).1 (norm_nonneg _) hN.le
    · simp [(hds z hz).self_of_nhds, hδ.le]
  · have heq : ρ - f = d := funext hρ
    rw [heq]
    apply lipschitzWith_of_nnnorm_fderiv_le (hd.differentiable (by simp))
    intro z
    change ‖fderiv ℝ d z‖ ≤ (δ.toNNReal : ℝ)
    rw [Real.coe_toNNReal _ hδ.le]
    by_cases hz : z ∈ tsupport χ
    · rw [fderiv_mul ((hχ.differentiable (by simp)) z) (hdiff z)]
      calc
        _ ≤ ‖χ z‖ * ‖fderiv ℝ (P - f) z‖ + ‖P z - f z‖ * ‖fderiv ℝ χ z‖ := by
          rw [← norm_smul, ← norm_smul]
          exact norm_add_le _ _
        _ ≤ ‖χ z‖ * ε + ε * ‖fderiv ℝ χ z‖ := by
          rw [fderiv_sub (hPs.differentiable (by simp) z) (hf.differentiable (by simp) z)]
          exact add_le_add (mul_le_mul_of_nonneg_left (hPε z (hR hz)).2 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hPε z (hR hz)).1 (norm_nonneg _))
        _ = A z * ε := by ring
        _ ≤ δ := hεδ ▸ mul_le_mul_of_nonneg_right (hAN z (hR hz)) hε.le
    · rw [(hds z hz).fderiv_eq]
      simpa using hδ.le

end PolyaNeumann

end
