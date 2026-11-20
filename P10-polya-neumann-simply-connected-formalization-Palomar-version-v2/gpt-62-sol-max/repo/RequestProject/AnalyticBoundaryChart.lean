module

public import RequestProject.SmoothDomain
public import RequestProject.BoundaryChart
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Filter Complex Metric FormalMultilinearSeries
open scoped Topology ComplexConjugate ContDiff Interval

/-- Complexify the convergent scalar power series of a real-analytic function. -/
private theorem exists_complexification {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ (∀ᶠ x : ℝ in 𝓝 0, H x = ↑(f x)) := by
  obtain ⟨p, r, hp⟩ := hf
  let q := ofScalars ℂ (fun n => (p.coeff n : ℂ))
  have hr : q.radius = p.radius := by
    simp  [radius, q, ofScalars_norm, Complex.norm_real, p.norm_apply_eq_norm_coef]
  have hq : HasFPowerSeriesOnBall q.sum q 0 r :=
    ⟨hr ▸ hp.r_le, hp.r_pos, fun hz => by
      simpa using q.hasSum (eball_subset_eball (hr ▸ hp.r_le) hz)⟩
  refine ⟨q.sum, ⟨q, r, hq⟩, ?_⟩
  filter_upwards [eball_mem_nhds (0 : ℝ) hp.r_pos] with x hx
  have h := (hp.hasSum hx).tsum_eq
  rw [zero_add] at h
  rw [← h, ofReal_tsum]
  apply tsum_congr
  intro n
  rw [p.apply_eq_pow_smul_coeff, ofScalars_apply_eq]
  simp [mul_comm]

/-- A holomorphic local coordinate at a real-analytic boundary point, with the
real diameter on the boundary and the upper half-disk on the interior side. -/
theorem exists_analytic_boundary_chart {Ω : Set ℂ} (hA : IsAnalyticDomain Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (B : ℂ → ℂ) (r : ℝ), 0 < r ∧ B 0 = p ∧
      DifferentiableOn ℂ B (ball 0 r) ∧ InjOn B (ball 0 r) ∧
      (∀ z ∈ ball 0 r, B z ∈ Ω ↔ 0 < z.im) ∧
      (∀ z ∈ ball 0 r, z.im = 0 → B z ∈ frontier Ω) := by
  obtain ⟨c, a, b, K, f, hc, ha, hb, ⟨hfs, hfa⟩, hLip, hf₀, hfbox, hΩ⟩ := hA.2 p hp
  have hc' : c * conj c = 1 := by simp_all [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcn : conj c ≠ 0 := by grind
  obtain ⟨H, hH, he⟩ := exists_complexification hfa
  have hH₀ : H 0 = 0 := by simpa [hf₀] using he.self_of_nhds
  have hderH : deriv H 0 = ↑(deriv f 0) := by
    have h₁ := HasDerivAt.comp_ofReal (z := (0 : ℝ)) (e := H) (e' := deriv H 0) (DifferentiableAt.hasDerivAt (AnalyticAt.differentiableAt hH))
    have h₂ := ((hfs.differentiable (by simp)).differentiableAt.hasDerivAt (x := (0 : ℝ))).ofReal_comp
    exact h₁.unique (h₂.congr_of_eventuallyEq he)
  let D (z : ℂ) := z + H z * I
  have hD : AnalyticAt ℂ D 0 := analyticAt_id.add (hH.mul analyticAt_const)
  have hD₀ : D 0 = 0 := by grind
  have hdD : HasDerivAt D (1 + ↑(deriv f 0) * I) 0 := by
    rw [← hderH]
    exact (hasDerivAt_id (0 : ℂ)).add (hH.differentiableAt.hasDerivAt.mul_const I)
  let B (z : ℂ) := p + conj c * D z
  have hB : AnalyticAt ℂ B 0 := analyticAt_const.add (analyticAt_const.mul hD)
  have hB₀ : B 0 = p := by grind
  have hnz : deriv B 0 ≠ 0 := by
    rw [((hdD.const_mul (conj c)).const_add p).deriv (f := B)]
    apply mul_ne_zero hcn
    intro h
    have := congrArg re h
    simp  at this
  have hcoords (z) : c * (B z - p) = D z := by
    grind
  let σ (z : ℂ) := (D z).im - f (D z).re
  have hDs : ContDiffAt ℝ 1 D 0 := hD.restrictScalars.contDiffAt
  have hσs :=
    (Complex.imCLM.contDiff.contDiffAt.comp _ hDs).sub
      (hfs.contDiffAt.of_le (by simp) |>.comp _ (Complex.reCLM.contDiff.contDiffAt.comp _ hDs))
  have hσd : fderiv ℝ σ 0 I = 1 + (deriv f 0) ^ 2 := by
    have hD' := hdD.hasFDerivAt.restrictScalars ℝ
    have hr := Complex.reCLM.hasFDerivAt.comp (0 : ℂ) hD'
    have hi := Complex.imCLM.hasFDerivAt.comp (0 : ℂ) hD'
    have hf' := (hfs.differentiable (by simp)).differentiableAt.hasDerivAt (x := (D 0).re)
    have h := hi.sub (hf'.hasFDerivAt.comp 0 hr)
    change HasFDerivAt σ _ 0 at h
    rw [h.fderiv]
    simp [hD₀, Complex.mul_im, pow_two]
  have hσp : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < fderiv ℝ σ z I := by
    have hpos : 0 < fderiv ℝ σ 0 I := by rw [hσd]; positivity
    exact ((ContinuousLinearMap.apply ℝ ℝ I).continuous.continuousAt.comp
      (hσs.continuousAt_fderiv (by simp))).eventually (lt_mem_nhds hpos)
  have hbox : ∀ᶠ z in 𝓝 (0 : ℂ), |(D z).re| < a ∧ |(D z).im| < b := by
    have hr :=
      continuous_abs.continuousAt.comp (continuous_re.continuousAt.comp hD.continuousAt)
    have hi :=
      continuous_abs.continuousAt.comp (continuous_im.continuousAt.comp hD.continuousAt)
    exact (hr.eventually (gt_mem_nhds (by simp_all))).and
      (hi.eventually (gt_mem_nhds (by simp_all)))
  have hreal : ∀ᶠ z : ℂ in 𝓝 0, H z.re = (f z.re : ℂ) := by
    simpa only [zero_re] using (continuous_re.tendsto (0 : ℂ)).eventually (by simpa using he)
  let A := hB.hasStrictDerivAt.localInverse B (deriv B 0) 0 hnz
  have hAl : ∀ᶠ z in 𝓝 (0 : ℂ), A (B z) = z := HasStrictDerivAt.eventually_left_inverse ..
  have hlocal : ∀ᶠ z : ℂ in 𝓝 0,
      AnalyticAt ℂ B z ∧ A (B z) = z ∧ (|(D z).re| < a ∧ |(D z).im| < b) ∧
        H z.re = (f z.re : ℂ) ∧ DifferentiableAt ℝ σ z ∧ 0 < fderiv ℝ σ z I := by
    filter_upwards [hB.eventually_analyticAt, hAl, hbox, hreal, hσs.eventually (by simp), hσp]
      with z hz hAz hbz hrz hsz hpz
    exact ⟨hz, hAz, hbz, hrz, hsz.differentiableAt (by simp), hpz⟩
  obtain ⟨r, hr, hrl⟩ := eventually_nhds_iff_ball.mp hlocal
  have hfront (z) (hz : z ∈ ball 0 r) (hz₀ : z.im = 0) : B z ∈ frontier Ω := by
    have heq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz₀]
    have hval : B z = chartPt p c f z.re := by
      simp only [D, ← hrl z hz |>.2.2.2.1, chartPt]
      rw [← heq]
    rw [hval]
    apply chartPt_mem_frontier hA.1.1 ⟨hc, ha, hb, hLip, hf₀, hfbox, hΩ⟩
    have h := (hrl z hz).2.2.1.1
    change |(z + H z * I).re| < a at h
    rwa [heq, (hrl z hz).2.2.2.1, add_re, mul_re, ofReal_im, I_re, mul_zero, zero_mul,
      sub_zero, add_zero, ofReal_re] at h
  refine ⟨B, r, hr, hB₀, fun z hz => (hrl z hz).1.differentiableAt.differentiableWithinAt,
    fun z hz w hw eq => ((hrl z hz).2.1.symm.trans (congrArg A eq)).trans (hrl w hw).2.1,
    ?_, hfront⟩
  intro z hz
  have hslice (t : ℝ) (ht : t ∈ [[0, z.im]]) : (z.re : ℂ) + t * I ∈ ball 0 r := by
    refine mem_ball_zero_iff.mpr (lt_of_le_of_lt ?_ (mem_ball_zero_iff.mp hz))
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    simp [Complex.normSq_apply, Complex.add_im, Complex.mul_re, Complex.mul_im]
    rcases mem_uIcc.mp ht with h | h
    · nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ z.im + t by linarith)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h.1) (show 0 ≤ -z.im - t by linarith)]
  let g (t : ℝ) := σ (z.re + t * I)
  have hdg (t : ℝ) (ht : t ∈ [[0, z.im]]) : HasDerivAt g
      (fderiv ℝ σ ((z.re : ℂ) + t * I) I) t := by
    have hlin : HasDerivAt (fun u : ℝ => (z.re : ℂ) + u * I) I t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (z.re : ℂ)
    exact (hrl _ (hslice t ht)).2.2.2.2.1.hasFDerivAt.comp_hasDerivAt t hlin
  have hmono := strictMonoOn_of_deriv_pos (convex_uIcc _ _)
    (fun t ht => (hdg t ht).continuousAt.continuousWithinAt) (fun t ht => by
      have ht' := interior_subset ht
      rw [(hdg t ht').deriv]
      exact (hrl _ (hslice t ht')).2.2.2.2.2)
  have hs0 : g 0 = 0 := by
    have h := (hrl z hz).2.2.2.1
    simp [g, σ, D, h, Complex.mul_im]
  have hsz : g z.im = σ z := by simp [g]
  have hpos : 0 < σ z ↔ 0 < z.im := by
    rw [← hmono.lt_iff_lt left_mem_uIcc right_mem_uIcc, hs0, hsz]
  have hbz := (hrl z hz).2.2.1
  dsimp [σ] at hpos
  rw [← hcoords z] at hbz hpos
  exact (hΩ _ hbz.1 hbz.2).trans (sub_pos.symm.trans hpos)

end PolyaNeumann

end
