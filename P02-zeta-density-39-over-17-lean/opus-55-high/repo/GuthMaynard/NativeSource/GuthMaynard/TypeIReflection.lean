module
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.MellinInversion
public import GuthMaynard.NativeSource.GuthMaynard.LargeValuesReflection
public import GuthMaynard.NativeSource.GuthMaynard.MediumReflection
public import GuthMaynard.NativeSource.GuthMaynard.TypeISmoothing
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace GuthMaynard.NativeMoment

/-!
# Exact smooth Type-I Poisson reflection

This file is the literal analytic bridge from the smooth source block to its
Poisson modes.  Negative Fourier frequency `-m` has phase
`m*x - t/(2π)*log x`; its stationary point is therefore `t/(2πm)`, and the
stationary frequencies have scale `t/(2^r Y)`.
-/

/-! ## Mellin transform of the actual Type-I cutoff

The exact Mellin route is the formal replacement for appealing to an
unavailable black-box stationary-phase theorem.  It keeps the fixed cutoff
as a Schwartz transform and leaves one common logarithmic reflection
integral, which is controlled by the weighted B-process estimate in
`LargeValuesReflection.lean`.
-/

noncomputable def typeIDyadicCutoffComplex (x : ℝ) : ℂ :=
  (typeIDyadicCutoff x : ℂ)

private theorem contDiff_typeIDyadicCutoffComplex :
    ContDiff ℝ ∞ typeIDyadicCutoffComplex := by
  exact Complex.ofRealCLM.contDiff.comp contDiff_typeIDyadicCutoff

private theorem hasCompactSupport_typeIDyadicCutoffComplex :
    HasCompactSupport typeIDyadicCutoffComplex := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (1 / 2 : ℝ) 2))
  intro x hx
  by_cases hhalf : x ≤ 1 / 2
  · simp [typeIDyadicCutoffComplex,
      typeIDyadicCutoff_eq_zero_of_le_half hhalf]
  · have htwo : 2 ≤ x := by
      by_contra hnot
      exact hx ⟨le_of_not_ge hhalf, le_of_not_ge hnot⟩
    simp [typeIDyadicCutoffComplex,
      typeIDyadicCutoff_eq_zero_of_two_le htwo]

theorem mellinConvergent_typeIDyadicCutoff_one :
    MellinConvergent typeIDyadicCutoffComplex (1 : ℂ) := by
  rw [MellinConvergent]
  have hInt : Integrable typeIDyadicCutoffComplex volume :=
    contDiff_typeIDyadicCutoffComplex.continuous.integrable_of_hasCompactSupport
      hasCompactSupport_typeIDyadicCutoffComplex
  simpa using hInt.integrableOn

/-- Logarithmic-coordinate Schwartz kernel for the literal cutoff used in
the #15 smooth partition. -/
noncomputable def typeIDyadicMellinKernel (u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * typeIDyadicCutoffComplex (Real.exp (-u))

theorem contDiff_typeIDyadicMellinKernel :
    ContDiff ℝ ∞ typeIDyadicMellinKernel := by
  pb_1975
  exact (Complex.ofRealCLM.contDiff.comp hExp).mul
    (contDiff_typeIDyadicCutoffComplex.comp hExp)

theorem hasCompactSupport_typeIDyadicMellinKernel :
    HasCompactSupport typeIDyadicMellinKernel := by
  pm_1595
  have hcut : typeIDyadicCutoff (Real.exp (-u)) = 0 := by
    by_cases hleft : u < -Real.log 2
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      have hlog : Real.log 2 < -u := by linarith
      pm_4809
      exact (Real.exp_lt_exp).mpr hlog |>.le
    · have hright : Real.log 2 < u := by
        by_contra hnot
        exact hu ⟨le_of_not_gt hleft, le_of_not_gt hnot⟩
      apply typeIDyadicCutoff_eq_zero_of_le_half
      have hneg : -u < -Real.log 2 := by linarith
      rw [Real.exp_neg]
      have hinv : (Real.exp u)⁻¹ ≤ (2 : ℝ)⁻¹ := by
        apply (inv_le_inv₀ (Real.exp_pos u) (by norm_num : (0 : ℝ) < 2)).2
        pm_4809
        exact (Real.exp_lt_exp).mpr hright |>.le
      simpa only [inv_eq_one_div] using hinv
  simp [typeIDyadicMellinKernel, typeIDyadicCutoffComplex, hcut]

/-- Schwartz realization of the logarithmic cutoff. -/
noncomputable def typeIDyadicMellinSchwartz : 𝓢(ℝ, ℂ) :=
  hasCompactSupport_typeIDyadicMellinKernel.toSchwartzMap
    contDiff_typeIDyadicMellinKernel

@[simp]
theorem typeIDyadicMellinSchwartz_apply (u : ℝ) :
    typeIDyadicMellinSchwartz u = typeIDyadicMellinKernel u := rfl

/-- Mellin transform of the fixed Type-I cutoff on `Re s = 1`. -/
noncomputable def typeIDyadicCutoffMellin (r : ℝ) : ℂ :=
  mellin typeIDyadicCutoffComplex ((1 : ℂ) + (r : ℂ) * I)

theorem typeIDyadicCutoffMellin_eq_fourier (r : ℝ) :
    typeIDyadicCutoffMellin r =
      𝓕 typeIDyadicMellinSchwartz (r / (2 * Real.pi)) := by
  unfold typeIDyadicCutoffMellin
  pb_2675
  rw [typeIDyadicMellinSchwartz_apply]
  simp [typeIDyadicMellinKernel, typeIDyadicCutoffComplex,
    Complex.ofReal_exp]

theorem continuous_typeIDyadicCutoffMellin :
    Continuous typeIDyadicCutoffMellin := by
  have hEq : typeIDyadicCutoffMellin = fun r : ℝ =>
      𝓕 typeIDyadicMellinSchwartz (r / (2 * Real.pi)) := by
    funext r
    exact typeIDyadicCutoffMellin_eq_fourier r
  rw [hEq]
  exact (𝓕 typeIDyadicMellinSchwartz).continuous.comp
    (continuous_id.div_const (2 * Real.pi))

/-- The Mellin transform of the fixed Type-I dyadic cutoff has arbitrary
polynomial decay, uniformly in its vertical ordinate. -/
theorem typeIDyadicCutoffMellin_polynomial_decay (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      |r| ^ n * ‖typeIDyadicCutoffMellin r‖ ≤ C := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 typeIDyadicMellinSchwartz
  pm_524
  pm_4855
  pm_4862
  pm_1228 r
  rw [typeIDyadicCutoffMellin_eq_fourier]
  pm_4861

theorem verticalIntegrable_typeIDyadicCutoffMellin :
    VerticalIntegrable (mellin typeIDyadicCutoffComplex) 1 := by
  rw [VerticalIntegrable]
  let F : 𝓢(ℝ, ℂ) := 𝓕 typeIDyadicMellinSchwartz
  pm_5906 hFourier Integrable F.integrable
  have hScaled : Integrable
      (fun u : ℝ => 𝓕 typeIDyadicMellinSchwartz
        (u / (2 * Real.pi))) := by
    simpa [F, div_eq_mul_inv] using
      hFourier.comp_mul_right'
        (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)
  apply hScaled.congr
  filter_upwards with u
  exact (typeIDyadicCutoffMellin_eq_fourier u).symm

section
variable {x : ℝ} (hx : 0 < x)
include x hx
/-- Exact pointwise Mellin inversion for the actual #15 dyadic cutoff. -/
theorem typeIDyadicCutoff_mellinInversion :
    mellinInv 1 (mellin typeIDyadicCutoffComplex) x =
      (typeIDyadicCutoff x : ℂ) := by
  exact mellinInv_mellin_eq 1 typeIDyadicCutoffComplex hx
    mellinConvergent_typeIDyadicCutoff_one
    verticalIntegrable_typeIDyadicCutoffMellin
    contDiff_typeIDyadicCutoffComplex.continuous.continuousAt

/-- Vertical-line form used inside the exact Type-I reflection formula. -/
theorem typeIDyadicCutoff_eq_verticalMellinIntegral :
    (typeIDyadicCutoff x : ℂ) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (x : ℂ) ^ (-((1 : ℂ) + (r : ℂ) * I)) *
            typeIDyadicCutoffMellin r := by
  rw [← typeIDyadicCutoff_mellinInversion hx]
  unfold mellinInv typeIDyadicCutoffMellin
  simp only [smul_eq_mul]
  norm_num
end

/-- Raw two-variable integrand obtained by inserting exact Mellin inversion
after the change of variables `v = m*x`. -/
noncomputable def typeIMellinReflectionIntegrand
    (sigma t q v r : ℝ) : ℂ :=
  (v / q : ℂ)⁻¹ *
    Complex.exp (-(((r * Real.log (v / q) : ℝ) : ℂ) * I)) *
      typeIDyadicCutoffMellin r *
        (gmReflectionPowerWeight sigma v *
          Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))

/-- Pointwise insertion of the literal cutoff's Mellin inversion into the
rescaled logarithmic phase. -/
theorem typeIDyadicCutoffPhase_eq_mellinIntegral
    (sigma t q : ℝ) {v : ℝ} (hv : 0 < v) (hq : 0 < q) :
    (typeIDyadicCutoff (v / q) : ℂ) *
        (gmReflectionPowerWeight sigma v *
          Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ, typeIMellinReflectionIntegrand sigma t q v r := by
  pm_5440 hratio v q hv hq
  rw [typeIDyadicCutoff_eq_verticalMellinIntegral hratio]
  pm_7017
  unfold typeIMellinReflectionIntegrand typeIDyadicCutoffMellin
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hratio.ne')]
  rw [← Complex.ofReal_log hratio.le]
  have hExpLog :
      Complex.exp ((Real.log (v / q) : ℝ) : ℂ) = (v / q : ℝ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hratio]
  pm_4865
  have hRatioInv : (((v / q : ℝ) : ℂ))⁻¹ =
      (q : ℂ) * (v : ℂ)⁻¹ := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  pm_4810 hRatioInvC
  rw [hRatioInv]
  rw [hRatioInvC]

/-- Algebraic factorization of the raw Mellin integrand.  All dependence on
the cutoff dilation `q` is outside the common weighted logarithmic kernel. -/
theorem typeIMellinReflectionIntegrand_eq_factored
    (sigma t : ℝ) {q v : ℝ} (r : ℝ) (hq : 0 < q) (hv : 0 < v) :
    typeIMellinReflectionIntegrand sigma t q v r =
      (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
        typeIDyadicCutoffMellin r *
          (gmReflectionPowerWeight sigma v *
            star ((v : ℂ)⁻¹ * Complex.exp
              (((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
  unfold typeIMellinReflectionIntegrand
  have hlog : Real.log (v / q) = Real.log v - Real.log q :=
    Real.log_div hv.ne' hq.ne'
  rw [hlog]
  pm_4810 hRatioInv
  rw [hRatioInv]
  pm_4851 hq.ne' hq.le
  have hstar :
      star ((v : ℂ)⁻¹ * Complex.exp
        (((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
        (v : ℂ)⁻¹ * Complex.exp
          (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
    rw [Complex.star_def, map_mul, map_inv₀, conj_ofReal,
      ← Complex.exp_conj]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring_nf
  rw [hstar]
  have hExpEq :
      Complex.exp (-(((r * (Real.log v - Real.log q) : ℝ) : ℂ) * I)) *
          Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
        Complex.exp ((Real.log q : ℂ) * ((r : ℂ) * I)) *
          Complex.exp
            (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
    pm_1378
  calc
    (q : ℂ) * (v : ℂ)⁻¹ *
          Complex.exp (-(((r * (Real.log v - Real.log q) : ℝ) : ℂ) * I)) *
          typeIDyadicCutoffMellin r *
          (gmReflectionPowerWeight sigma v *
            Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) =
        (q : ℂ) * (v : ℂ)⁻¹ * typeIDyadicCutoffMellin r *
          gmReflectionPowerWeight sigma v *
          (Complex.exp (-(((r * (Real.log v - Real.log q) : ℝ) : ℂ) * I)) *
            Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
      ring
    _ = (q : ℂ) * (v : ℂ)⁻¹ * typeIDyadicCutoffMellin r *
          gmReflectionPowerWeight sigma v *
          (Complex.exp ((Real.log q : ℂ) * ((r : ℂ) * I)) *
            Complex.exp
              (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
      rw [hExpEq]
    _ = (q : ℂ) * Complex.exp ((Real.log q : ℂ) * ((r : ℂ) * I)) *
          typeIDyadicCutoffMellin r *
          (gmReflectionPowerWeight sigma v *
            ((v : ℂ)⁻¹ * Complex.exp
              (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))) := by
      ring

/-- Absolute integrability needed to exchange the finite physical interval
with the complete Mellin line.  Compactness of the physical interval and
Schwartz decay of the literal cutoff are both used explicitly. -/
theorem integrable_typeIMellinReflectionIntegrand
    {sigma t q A B : ℝ} (hsigma : 0 ≤ sigma) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    Integrable (Function.uncurry
      (typeIMellinReflectionIntegrand sigma t q))
      ((volume.restrict (Set.uIoc A B)).prod volume) := by
  pm_4811 hH
  let C : ℝ := (q / A) * A ^ (-sigma)
  pm_4855
  have hConst : Integrable (fun _v : ℝ => C)
      (volume.restrict (Set.uIoc A B)) := by
    exact MeasureTheory.integrableOn_const (hs := by simp)
  have hDom := hConst.mul_prod hH.norm
  apply hDom.mono'
  · have hElementary : AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          (z.1 / q : ℂ)⁻¹ *
            Complex.exp (-(((z.2 * Real.log (z.1 / q) : ℝ) : ℂ) * I)) *
              (gmReflectionPowerWeight sigma z.1 *
                Complex.exp
                  (-((((t * Real.log z.1 - 2 * Real.pi * z.1 : ℝ) : ℂ) * I)))))
        ((volume.restrict (Set.uIoc A B)).prod volume) := by
      apply StronglyMeasurable.aestronglyMeasurable
      unfold gmReflectionPowerWeight
      measurability
    pm_6206 typeIMellinReflectionIntegrand
  · rw [Measure.ae_prod_iff_ae_ae (by
      apply measurableSet_le
      · have hHM : Measurable fun z : ℝ × ℝ =>
            typeIDyadicCutoffMellin z.2 :=
          continuous_typeIDyadicCutoffMellin.measurable.comp measurable_snd
        unfold typeIMellinReflectionIntegrand Function.uncurry
        unfold gmReflectionPowerWeight
        measurability
      · exact ((continuous_typeIDyadicCutoffMellin.norm.comp continuous_snd
          |>.const_mul C)).measurable)]
    pm_8131
    have hvIoc : v ∈ Set.Ioc A B := by
      simpa only [Set.uIoc_of_le hAB] using hv
    have hvPos : 0 < v := hA.trans hvIoc.1
    have hqv : q / v ≤ q / A := by
      exact div_le_div_of_nonneg_left hq.le hA hvIoc.1.le
    have hpow : v ^ (-sigma) ≤ A ^ (-sigma) := by
      exact Real.rpow_le_rpow_of_nonpos hA hvIoc.1.le (by linarith)
    have hNormRatio : ‖(v : ℂ) / (q : ℂ)‖⁻¹ = q / v := by
      rw [norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hvPos,
        abs_of_pos hq, inv_div]
    have hNormMellinPhase :
        ‖Complex.exp (-(((r * Real.log (v / q) : ℝ) : ℂ) * I))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hNormReflectionPhase :
        ‖Complex.exp
          (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [show ‖Function.uncurry
        (typeIMellinReflectionIntegrand sigma t q) (v, r)‖ =
        (q / v) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) by
      unfold typeIMellinReflectionIntegrand Function.uncurry
      simp only [norm_mul, norm_inv]
      rw [hNormRatio, hNormMellinPhase, hNormReflectionPhase,
        norm_gmReflectionPowerWeight hvPos]
      ring]
    change (q / v) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) ≤
      C * ‖typeIDyadicCutoffMellin r‖
    dsimp only [C]
    calc
      (q / v) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) ≤
          (q / A) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) := by
        gcongr
      _ ≤ (q / A) * ‖typeIDyadicCutoffMellin r‖ * A ^ (-sigma) := by
        gcongr
      _ = q / A * A ^ (-sigma) * ‖typeIDyadicCutoffMellin r‖ := by
        ring

/-- Common conjugated power-weighted reflection integral produced by the
exact Mellin transform. -/
noncomputable def typeIPowerReflectionIntegral
    (sigma tau A B : ℝ) : ℂ :=
  ∫ v in A..B,
    gmReflectionPowerWeight sigma v *
      star ((v : ℂ)⁻¹ * Complex.exp
        (((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))

/-- Uniform weighted B-process bound for the common integral in the exact
Mellin reflection formula. -/
theorem norm_typeIPowerReflectionIntegral_le
    {sigma tau A B : ℝ} (htau : 1 ≤ tau)
    (hA : 0 < A) (hAB : A ≤ B) :
    ‖typeIPowerReflectionIntegral sigma tau A B‖ ≤
      (10 / Real.sqrt tau) *
        (B ^ (-sigma) +
          ∫ v in A..B,
            ‖(((-sigma / v : ℝ) : ℂ) *
              gmReflectionPowerWeight sigma v)‖) := by
  simpa only [typeIPowerReflectionIntegral] using
    norm_conj_powerWeighted_gmReflectionIntegral_le htau hA hAB

/-- Exact Mellin form of the rescaled medium Type-I integral.  The right
side has one common weighted logarithmic reflection integral; the mode scale
`q` appears only in explicit unitary/Mellin factors. -/
theorem typeIDyadicRescaledIntegral_eq_mellinReflection
    {sigma t q A B : ℝ} (hsigma : 0 ≤ sigma) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∫ v in A..B,
        (typeIDyadicCutoff (v / q) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B := by
  calc
    (∫ v in A..B,
        (typeIDyadicCutoff (v / q) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))) =
      ∫ v in A..B,
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ, typeIMellinReflectionIntegrand sigma t q v r := by
        apply intervalIntegral.integral_congr
        pm_4812
        exact typeIDyadicCutoffPhase_eq_mellinIntegral sigma t q
          (hA.trans_le hvIcc.1) hq
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ v in A..B,
          ∫ r : ℝ, typeIMellinReflectionIntegrand sigma t q v r := by
        rw [intervalIntegral.integral_smul]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ∫ v in A..B, typeIMellinReflectionIntegrand sigma t q v r := by
        rw [MeasureTheory.intervalIntegral_integral_swap
          (integrable_typeIMellinReflectionIntegrand hsigma hq hA hAB)]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        unfold typeIPowerReflectionIntegral
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        pm_4812
        pm_8404

/-- Explicit Jacobian and logarithmic scale factor in `v = m*x`. -/
noncomputable def typeIReflectionScaleFactor
    (sigma t m : ℝ) : ℂ :=
  ((m : ℂ)⁻¹ *
    Complex.exp (((sigma * Real.log m : ℝ) : ℂ))) *
      Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))

/-- Physical cutoff integrand at Fourier frequency `m`. -/
noncomputable def typeIDyadicPhysicalIntegrand
    (sigma t m Q x : ℝ) : ℂ :=
  (typeIDyadicCutoff (x / Q) : ℂ) *
    (gmReflectionPowerWeight sigma x *
      Complex.exp
        (-((((t * Real.log x - 2 * Real.pi * m * x : ℝ) : ℂ) * I))))

/-- Exact physical-to-reflected rescaling before Mellin inversion. -/
theorem typeIDyadicPhysicalIntegral_rescale
    {sigma t m Q A B : ℝ} (hm : 0 < m) (hQ : 0 < Q)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∫ x in A..B, typeIDyadicPhysicalIntegrand sigma t m Q x) =
      typeIReflectionScaleFactor sigma t m *
        ∫ v in m * A..m * B,
          typeIDyadicPhysicalIntegrand sigma t 1 (m * Q) v := by
  let g : ℝ → ℂ := typeIDyadicPhysicalIntegrand sigma t 1 (m * Q)
  have hPointwise : ∀ x ∈ Set.uIcc A B,
      typeIDyadicPhysicalIntegrand sigma t m Q x =
        (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) * g (m * x) := by
    pm_4874
    have hlog : Real.log (m * x) = Real.log m + Real.log x :=
      Real.log_mul hm.ne' hxPos.ne'
    have hcut : m * x / (m * Q) = x / Q := by
      field_simp [hm.ne', hQ.ne']
    dsimp only [g]
    unfold typeIDyadicPhysicalIntegrand gmReflectionPowerWeight
    rw [hcut]
    rw [hlog]
    have hSigmaEq :
        Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
            Complex.exp (((-sigma * (Real.log m + Real.log x) : ℝ) : ℂ)) =
          Complex.exp (((-sigma * Real.log x : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hPhaseEq :
        Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I)) *
            Complex.exp
              (-((((t * (Real.log m + Real.log x) -
                2 * Real.pi * 1 * (m * x) : ℝ) : ℂ) * I))) =
          Complex.exp
            (-((((t * Real.log x - 2 * Real.pi * m * x : ℝ) : ℂ) * I))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hSigmaEq, ← hPhaseEq]
    ring
  have hChange := intervalIntegral.integral_comp_mul_left g hm.ne'
    (a := A) (b := B)
  calc
    (∫ x in A..B, typeIDyadicPhysicalIntegrand sigma t m Q x) =
      ∫ x in A..B,
        (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) * g (m * x) := by
        apply intervalIntegral.integral_congr
        exact hPointwise
    _ = (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) *
        ∫ x in A..B, g (m * x) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) *
        ((m : ℝ)⁻¹ • ∫ v in m * A..m * B, g v) := by
      rw [hChange]
    _ = typeIReflectionScaleFactor sigma t m *
        ∫ v in m * A..m * B,
          typeIDyadicPhysicalIntegrand sigma t 1 (m * Q) v := by
      unfold typeIReflectionScaleFactor
      simp only [Complex.real_smul]
      dsimp only [g]
      push_cast
      ring

/-- A rescaled dyadic integrand is supported strictly between `q/2` and
`2*q`.  Consequently any larger positive interval may be used for its
integral.  This is the support statement that lets all critical Poisson modes
share one reflection interval. -/
theorem integral_typeIDyadicPhysicalIntegrand_eq_interval
    {sigma t q L U : ℝ} (hq : 0 < q)
    (hL : L ≤ q / 2) (hU : 2 * q ≤ U) :
    (∫ v : ℝ, typeIDyadicPhysicalIntegrand sigma t 1 q v) =
      ∫ v in L..U, typeIDyadicPhysicalIntegrand sigma t 1 q v := by
  pm_6794 v hv q
  pm_4813 hlower v q hupper
  rw [Set.mem_Ioc]
  constructor
  · have hqhalf : q / 2 < v := by
      have hscaled := (lt_div_iff₀ hq).mp hlower
      nlinarith
    exact hL.trans_lt hqhalf
  · exact ((div_lt_iff₀ hq).mp hupper).le.trans hU

/-- Exact medium Type-I reflection with a mode-independent integration
interval.  For every `1 ≤ m ≤ M`, the change of variables `v = m*x` puts the
support inside `[Q/2, 2*M*Q]`; Mellin inversion then leaves the mode only in
explicit algebraic factors. -/
theorem typeIDyadicPhysicalIntegral_eq_common_mellinReflection
    {sigma t Q : ℝ} {m M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hm : 1 ≤ m) (hmM : m ≤ M) :
    (∫ x in Q / 2..2 * Q,
        typeIDyadicPhysicalIntegrand sigma t m Q x) =
      typeIReflectionScaleFactor sigma t m *
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            (((m : ℝ) * Q : ℝ) : ℂ) *
              (((m : ℝ) * Q : ℝ) : ℂ) ^ ((r : ℂ) * I) *
                typeIDyadicCutoffMellin r *
                  typeIPowerReflectionIntegral sigma (t + r)
                    (Q / 2) (2 * M * Q)) := by
  have hmPosNat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  pm_74 hmPos m hmPosNat
  pm_77 hmOne m hm
  pm_5896 hMPos M hmPosNat.trans_le hmM
  rw [typeIDyadicPhysicalIntegral_rescale hmPos hQ (by positivity)
    (by linarith)]
  congr 1
  have hNatural :
      (∫ v : ℝ,
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
        ∫ v in (m : ℝ) * (Q / 2)..(m : ℝ) * (2 * Q),
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
    apply integral_typeIDyadicPhysicalIntegrand_eq_interval (mul_pos hmPos hQ)
    · exact le_of_eq (by ring)
    · exact le_of_eq (by ring)
  pm_106 hmMReal m M hmM
  have hCommon :
      (∫ v : ℝ,
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
        ∫ v in Q / 2..2 * M * Q,
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
    apply integral_typeIDyadicPhysicalIntegrand_eq_interval (mul_pos hmPos hQ)
    · have hscale := mul_le_mul_of_nonneg_right hmOne hQ.le
      nlinarith
    · nlinarith
  rw [← hNatural, hCommon]
  have hFun : typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) =
      fun v : ℝ =>
        (typeIDyadicCutoff (v / ((m : ℝ) * Q)) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
    funext v
    unfold typeIDyadicPhysicalIntegrand
    congr 3
    ring_nf
  rw [hFun]
  exact typeIDyadicRescaledIntegral_eq_mellinReflection hsigma
    (mul_pos hmPos hQ) (by positivity) (by
      have hMOne : (1 : ℝ) ≤ M := hmOne.trans hmMReal
      have hscale := mul_le_mul_of_nonneg_right hMOne hQ.le
      nlinarith)

/-- One mode of the exact common Mellin-reflection integrand. -/
noncomputable def typeICommonMellinMode
    (sigma t q A B r : ℝ) : ℂ :=
  (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
    typeIDyadicCutoffMellin r *
      typeIPowerReflectionIntegral sigma (t + r) A B

theorem intervalIntegral_typeIMellinReflectionIntegrand_eq_commonMode
    {sigma t q A B : ℝ} (r : ℝ) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∫ v in A..B, typeIMellinReflectionIntegrand sigma t q v r) =
      typeICommonMellinMode sigma t q A B r := by
  unfold typeICommonMellinMode typeIPowerReflectionIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  pm_4812
  pm_8404

theorem integrable_typeICommonMellinMode
    {sigma t q A B : ℝ} (hsigma : 0 ≤ sigma) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    Integrable (typeICommonMellinMode sigma t q A B) := by
  have hJoint := integrable_typeIMellinReflectionIntegrand
    (sigma := sigma) (t := t) (q := q) (A := A) (B := B)
    hsigma hq hA hAB
  have hInner : Integrable (fun r : ℝ =>
      ∫ v in A..B, typeIMellinReflectionIntegrand sigma t q v r) := by
    have h := hJoint.integral_prod_right
    simpa only [intervalIntegral.integral_of_le hAB,
      Set.uIoc_of_le hAB, Function.uncurry_apply_pair] using h
  apply hInner.congr
  filter_upwards with r
  exact intervalIntegral_typeIMellinReflectionIntegrand_eq_commonMode
    r hq hA hAB

/-- The finite coefficient polynomial produced by exact medium reflection.
The coefficients are independent of the original ordinate except for the
standard unit-modulus Dirichlet phase. -/
noncomputable def typeIReflectedMellinPolynomial
    (sigma t Q : ℝ) (M : ℕ) (r : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    typeIReflectionScaleFactor sigma t m *
      (((m : ℝ) * Q : ℝ) : ℂ) *
        (((m : ℝ) * Q : ℝ) : ℂ) ^ ((r : ℂ) * I)

/-- Exact finite B-process assembly.  A whole block of critical modes is one
Mellin integral of a fixed finite Dirichlet polynomial against the common
oscillatory kernel.  No pointwise stationary-phase approximation or hidden
error term remains. -/
theorem sum_typeIDyadicPhysicalIntegral_eq_reflectedMellinPolynomial
    {sigma t Q : ℝ} {M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    (∑ m ∈ Finset.Icc 1 M,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q) := by
  pm_1314
  pm_116 hA A
  have hAB : A ≤ B := by
    dsimp only [A, B]
    pm_77 hMOne M hM
    have hscale := mul_le_mul_of_nonneg_right hMOne hQ.le
    nlinarith
  have hModeInt : ∀ m ∈ S,
      Integrable (fun r : ℝ =>
        typeIReflectionScaleFactor sigma t m *
          typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    pm_6767
    have hmPos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmRange.1)
    pm_7286
  calc
    (∑ m ∈ Finset.Icc 1 M,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      ∑ m ∈ S,
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        apply Finset.sum_congr rfl
        pm_6767
        rw [typeIDyadicPhysicalIntegral_eq_common_mellinReflection
          hsigma hQ hmRange.1 hmRange.2]
        unfold typeICommonMellinMode A B
        simp only [Complex.real_smul]
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∑ m ∈ S,
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        rw [Finset.smul_sum]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ∑ m ∈ S,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        congr 1
        exact (MeasureTheory.integral_finsetSum S hModeInt).symm
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        dsimp only [S, A, B]
        unfold typeIReflectedMellinPolynomial typeICommonMellinMode
        pm_1063 Finset.sum_mul m hm
        ring

/-- Continuous compactly supported interpolation of a smooth Type-I block. -/
noncomputable def typeIReflectionKernel
    (Y A r : ℕ) (σ t x : ℝ) : ℂ :=
  (typeISourceSmoothWeight Y A r x : ℂ) *
    Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
    Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I))

/-- At positive integers the continuous kernel is exactly the source block
summand. -/
theorem typeIReflectionKernel_natCast
    (Y A r n : ℕ) (σ t : ℝ) (hn : 0 < n) :
    typeIReflectionKernel Y A r σ t n =
      typeISourceSmoothWeight Y A r n *
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
  pm_74 hnReal n hn
  pm_146 hnNe n hn.ne'
  pm_5067 hbase n
  rw [hbase]
  unfold typeIReflectionKernel
  rw [Complex.cpow_def_of_ne_zero (hbase ▸ hnNe),
    Complex.cpow_def_of_ne_zero (hbase ▸ hnNe),
    ← Complex.ofReal_log hnReal.le]
  simp only [ofReal_neg, ofReal_mul]
  ring_nf

/-- On an interior medium scale the artificial source boundary is identically
one wherever the fixed dyadic cutoff is nonzero.  Thus the Poisson kernel is
the genuine boundary-free dyadic kernel, not a silently altered model. -/
theorem typeISourceSmoothWeight_eq_dyadic_of_interior
    {Y A r : ℕ}
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤
      (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (x : ℝ) :
    typeISourceSmoothWeight Y A r x =
      typeIDyadicCutoff (x / (2 ^ r * Y : ℕ)) := by
  let Q : ℝ := ((2 ^ r * Y : ℕ) : ℝ)
  pm_8129
  · unfold typeISourceSmoothWeight
    change typeITailBoundary Y A x * typeIDyadicCutoff (x / Q) =
      typeIDyadicCutoff (x / Q)
    rw [hcut, mul_zero]
  · have hQ : 0 < Q := by
      have hleftPos : (0 : ℝ) < ((Y + 1 : ℕ) : ℝ) := by positivity
      nlinarith
    pm_4813 hxLowerRatio x Q hxUpperRatio
    have hxLower : ((Y + 1 : ℕ) : ℝ) < x := by
      have hscaled := (lt_div_iff₀ hQ).mp hxLowerRatio
      linarith
    have hUpperReal : 2 * Q ≤ (A : ℝ) := by
      dsimp only [Q]
      exact_mod_cast hUpper
    have hxUpper : x < (A : ℝ) := by
      exact ((div_lt_iff₀ hQ).mp hxUpperRatio).trans_le hUpperReal
    have hleft : Real.smoothTransition (x - (Y : ℝ)) = 1 :=
      Real.smoothTransition.one_of_one_le (by push_cast at hxLower; linarith)
    have hright : Real.smoothTransition
        (((A + 1 : ℕ) : ℝ) - x) = 1 :=
      Real.smoothTransition.one_of_one_le (by push_cast; linarith)
    unfold typeISourceSmoothWeight typeITailBoundary
    rw [hleft, hright, one_mul, one_mul]

/-- Exact removal of the source boundary from the full continuous kernel on
an interior medium scale. -/
theorem typeIReflectionKernel_eq_dyadicPhysical_of_interior
    {Y A r : ℕ} {σ t : ℝ}
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤
      (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A) :
    typeIReflectionKernel Y A r σ t =
      typeIDyadicPhysicalIntegrand σ t 0 (2 ^ r * Y : ℕ) := by
  funext x
  unfold typeIReflectionKernel
  rw [typeISourceSmoothWeight_eq_dyadic_of_interior hLower hUpper]
  unfold typeIDyadicPhysicalIntegrand
    gmReflectionPowerWeight
  have hphase :
      Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I)) =
        Complex.exp
          (-((((t * Real.log x - 2 * Real.pi * 0 * x : ℝ) : ℂ) * I))) := by
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

/-! ## Uniform normalized Fourier tail for interior medium blocks -/

/-- The boundary-free normalized Type-I amplitude on the fixed interval
`[1/2,2]`.  Dependence on the physical dyadic scale is recovered by Fourier
dilation, while `σ` is fixed throughout one zero-density estimate. -/
noncomputable def typeINormalizedAmplitude (σ x : ℝ) : ℂ :=
  (typeIDyadicCutoff x : ℂ) *
    Complex.exp ((((-σ * Real.log x : ℝ) : ℂ)))

/-- The normalized Type-I amplitude is smooth to every order. -/
theorem contDiff_typeINormalizedAmplitude (σ : ℝ) :
    ContDiff ℝ ∞ (typeINormalizedAmplitude σ) := by
  pm_5049 x hx
  · subst x
    have hEventually : typeINormalizedAmplitude σ =ᶠ[𝓝 0] 0 := by
      pm_731
      simp [typeINormalizedAmplitude, hcut]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hcut : ContDiffAt ℝ ∞
        (fun y : ℝ => (typeIDyadicCutoff y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        contDiff_typeIDyadicCutoff.contDiffAt
    have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.2 hx
    have hpow : ContDiffAt ℝ ∞
        (fun y : ℝ => Complex.exp ((((-σ * Real.log y : ℝ) : ℂ)))) x :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.mul hlog)).cexp
    exact hcut.mul hpow

private theorem hasCompactSupport_typeINormalizedAmplitude (σ : ℝ) :
    HasCompactSupport (typeINormalizedAmplitude σ) := by
  pm_4814
  simp [typeINormalizedAmplitude, hcut]

private noncomputable def typeINormalizedAmplitudeSchwartz (σ : ℝ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeINormalizedAmplitude σ).toSchwartzMap
    (contDiff_typeINormalizedAmplitude σ)

@[simp]
private theorem typeINormalizedAmplitudeSchwartz_apply (σ x : ℝ) :
    typeINormalizedAmplitudeSchwartz σ x = typeINormalizedAmplitude σ x := rfl

/-- Normalized oscillatory kernel whose Fourier samples are the Poisson
modes of an interior dyadic block after the change of variables `x=Q*u`. -/
noncomputable def typeINormalizedKernel (σ t x : ℝ) : ℂ :=
  typeINormalizedAmplitude σ x *
    Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I))

theorem contDiff_typeINormalizedKernel (σ t : ℝ) :
    ContDiff ℝ ∞ (typeINormalizedKernel σ t) := by
  pm_5049 x hx
  · subst x
    have hEventually : typeINormalizedKernel σ t =ᶠ[𝓝 0] 0 := by
      pm_731
      simp [typeINormalizedKernel, typeINormalizedAmplitude, hcut]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hamp : ContDiffAt ℝ ∞ (typeINormalizedAmplitude σ) x :=
      (contDiff_typeINormalizedAmplitude σ).contDiffAt
    have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.2 hx
    have hphase : ContDiffAt ℝ ∞
        (fun y : ℝ => Complex.exp ((((-t * Real.log y : ℝ) : ℂ) * I))) x :=
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.mul hlog)).mul contDiffAt_const).cexp
    exact hamp.mul hphase

theorem hasCompactSupport_typeINormalizedKernel (σ t : ℝ) :
    HasCompactSupport (typeINormalizedKernel σ t) := by
  pm_4814
  simp [typeINormalizedKernel, typeINormalizedAmplitude, hcut]

/-- The `typeINormalizedKernelSchwartz` definition used by the source-facing construction in `TypeIReflection`. -/
noncomputable def typeINormalizedKernelSchwartz (σ t : ℝ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeINormalizedKernel σ t).toSchwartzMap
    (contDiff_typeINormalizedKernel σ t)

@[simp]
theorem typeINormalizedKernelSchwartz_apply (σ t x : ℝ) :
    typeINormalizedKernelSchwartz σ t x = typeINormalizedKernel σ t x := rfl

private theorem normalizedSchwartz_coe (σ t : ℝ) :
    (typeINormalizedKernelSchwartz σ t : ℝ → ℂ) = typeINormalizedKernel σ t :=
  funext (typeINormalizedKernelSchwartz_apply σ t)

/-- The `typeINormalizedFourier` definition used by the source-facing construction in `TypeIReflection`. -/
noncomputable def typeINormalizedFourier (σ t ξ : ℝ) : ℂ :=
  𝓕 (typeINormalizedKernelSchwartz σ t) ξ

private theorem typeINormalizedKernel_eq_amplitude_mul_cpow
    (σ t : ℝ) {x : ℝ} (hx : 0 < x) :
    typeINormalizedKernel σ t x =
      typeINormalizedAmplitude σ x * (x : ℂ) ^ ((-t : ℂ) * I) := by
  unfold typeINormalizedKernel
  pm_4851 hx.ne' hx.le
  congr 2
  push_cast
  ring

section
variable (t : ℝ) (n : ℕ) {x : ℝ}
include t n x
private theorem contDiffAt_ofReal_cpow_neg_mul_I (hx : 0 < x) :
    ContDiffAt ℝ n (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x := by
  have hEq :
      (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) =ᶠ[nhds x]
        fun y : ℝ => Complex.exp ((((-t * Real.log y : ℝ) : ℂ) * I)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    pm_4853
  have hExp : ContDiffAt ℝ n
      (fun y : ℝ => Complex.exp ((((-t * Real.log y : ℝ) : ℂ) * I))) x := by
    have hReal : ContDiffAt ℝ n (fun y : ℝ => -t * Real.log y) x :=
      contDiffAt_const.mul (Real.contDiffAt_log.mpr hx.ne')
    have hComplex : ContDiffAt ℝ n
        (fun y : ℝ => ((-t * Real.log y : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hReal
    exact (hComplex.mul contDiffAt_const).cexp
  exact hExp.congr_of_eventuallyEq hEq

private theorem norm_iteratedDeriv_ofReal_cpow_neg_mul_I_le (hx : 1 / 2 ≤ x) :
    ‖iteratedDeriv n (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ ≤
      2 ^ n * (|t| + n) ^ n := by
  have hxPos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hx
  rw [iteratedDeriv_ofReal_cpow ((-t : ℂ) * I) n hxPos, norm_mul]
  have hcoeff := norm_gmCpowDerivativeCoeff_le ((-t : ℂ) * I) n
  have hpow : ‖(x : ℂ) ^ ((-t : ℂ) * I - n)‖ ≤ 2 ^ n := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
    have hre : (((-t : ℂ) * I - n).re) = -(n : ℝ) := by simp
    rw [hre]
    have hmono : x ^ (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(n : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx
        (neg_nonpos.mpr (Nat.cast_nonneg n))
    calc
      x ^ (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(n : ℝ)) := hmono
      _ = 2 ^ n := by
        rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
        norm_num
  calc
    ‖gmCpowDerivativeCoeff ((-t : ℂ) * I) n‖ *
          ‖(x : ℂ) ^ ((-t : ℂ) * I - n)‖ ≤
        (‖((-t : ℂ) * I)‖ + n) ^ n * 2 ^ n :=
      mul_le_mul hcoeff hpow (norm_nonneg _) (by positivity)
    _ = 2 ^ n * (|t| + n) ^ n := by
      simp [Real.norm_eq_abs]
      ring
end

private theorem typeIMellinDerivativePower_le
    (t : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    (|t| + k) ^ k ≤
      (n + 1 : ℝ) ^ n * (1 + |t|) ^ n := by pm_4852 hnNonneg

section
variable (σ : ℝ)
include σ
/-- Uniform derivative bound for the boundary-free normalized Type-I
kernel.  The constant may depend on the fixed density line `σ`, but is
independent of the ordinate and dyadic scale. -/
theorem typeINormalizedKernel_uniform_iteratedFDeriv (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ n (typeINormalizedKernel σ t) x‖ ≤
        C * (1 + |t|) ^ n := by
  let C : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
        2 ^ n * (n + 1 : ℝ) ^ n
  pm_4855
  refine ⟨C, hC, ?_⟩
  intro t x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hxLow : x < 1 / 2
  · have hzero : typeINormalizedKernel σ t =ᶠ[nhds x] 0 := by
      filter_upwards [Iio_mem_nhds hxLow] with y hy
      pm_1223 typeIDyadicCutoff_eq_zero_of_le_half
    rw [hzero.iteratedDeriv_eq]
    simp
    positivity
  by_cases hxHigh : 2 < x
  · have hzero : typeINormalizedKernel σ t =ᶠ[nhds x] 0 := by
      filter_upwards [Ioi_mem_nhds hxHigh] with y hy
      pm_1223 typeIDyadicCutoff_eq_zero_of_two_le
    rw [hzero.iteratedDeriv_eq]
    simp
    positivity
  have hxIcc : x ∈ Set.Icc (1 / 2 : ℝ) 2 :=
    ⟨le_of_not_gt hxLow, le_of_not_gt hxHigh⟩
  have hxPos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hxIcc.1
  have hlocal : typeINormalizedKernel σ t =ᶠ[nhds x]
      fun y : ℝ => typeINormalizedAmplitude σ y *
        (y : ℂ) ^ ((-t : ℂ) * I) := by
    filter_upwards [Ioi_mem_nhds hxPos] with y hy
    exact typeINormalizedKernel_eq_amplitude_mul_cpow σ t hy
  rw [hlocal.iteratedDeriv_eq]
  have hampSmooth : ContDiffAt ℝ n (typeINormalizedAmplitude σ) x :=
    (contDiff_typeINormalizedAmplitude σ).contDiffAt.of_le
      (by exact_mod_cast le_top)
  have hphaseSmooth := contDiffAt_ofReal_cpow_neg_mul_I t n hxPos
  change ‖iteratedDeriv n
      (typeINormalizedAmplitude σ *
        fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ ≤
    C * (1 + |t|) ^ n
  rw [iteratedDeriv_mul hampSmooth hphaseSmooth]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (typeINormalizedAmplitude σ) x *
          iteratedDeriv (n - i)
            (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        ‖(n.choose i : ℂ) * iteratedDeriv i (typeINormalizedAmplitude σ) x *
          iteratedDeriv (n - i)
            (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
            2 ^ n * (n + 1 : ℝ) ^ n) * (1 + |t|) ^ n := by
      pm_4856
      pm_4947 hamp typeINormalizedAmplitudeSchwartz σ typeINormalizedAmplitude norm_iteratedDeriv_ofReal_cpow_neg_mul_I_le typeIMellinDerivativePower_le
      have htwo : (2 : ℝ) ^ (n - i) ≤ 2 ^ n := by
        exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le n i)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      pm_5014 hchoose n.choose i
      have hseminorm :
          0 ≤ SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) :=
        by positivity
      have hcoefficient :
          0 ≤ (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) :=
        mul_nonneg hchoose hseminorm
      have hphaseNonneg :
          0 ≤ ‖iteratedDeriv (n - i)
            (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ := norm_nonneg _
      have hinner :
          (2 : ℝ) ^ (n - i) * (|t| + ((n - i : ℕ) : ℝ)) ^ (n - i) ≤
            2 ^ n * ((n + 1 : ℝ) ^ n * (1 + |t|) ^ n) := by
        pm_149 htwo hpower
      calc
        (n.choose i : ℝ) * ‖iteratedDeriv i (typeINormalizedAmplitude σ) x‖ *
            ‖iteratedDeriv (n - i)
              (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ ≤
          (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
              ‖iteratedDeriv (n - i)
                (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hamp hchoose) hphaseNonneg
        _ ≤ (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
              (2 ^ (n - i) * (|t| + ((n - i : ℕ) : ℝ)) ^ (n - i)) := by
            exact mul_le_mul_of_nonneg_left hphase hcoefficient
        _ ≤ (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
              (2 ^ n * ((n + 1 : ℝ) ^ n * (1 + |t|) ^ n)) := by
            exact mul_le_mul_of_nonneg_left hinner hcoefficient
        _ = ((n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
              2 ^ n * (n + 1 : ℝ) ^ n) * (1 + |t|) ^ n := by ring
    _ = C * (1 + |t|) ^ n := by
      dsimp only [C]
      rw [Finset.sum_mul]

private theorem integral_norm_iteratedFDeriv_typeINormalizedKernel_le (p : ℕ) {D : ℝ}
    (hbound : ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖ ≤
        D * (1 + |t|) ^ p) (t : ℝ) :
    (∫ x : ℝ, ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖) ≤
      (3 / 2 : ℝ) * D * (1 + |t|) ^ p := by
  pm_4991 typeINormalizedKernel σ normalizedSchwartz_coe typeINormalizedKernelSchwartz
  have hsupport : Function.support f ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
    intro x hx
    by_contra hnot
    have hxOutside : x < 1 / 2 ∨ 2 < x := by
      by_cases hxLow : x < 1 / 2
      pm_8188 hxLow hxUpper
    have hzero : typeINormalizedKernel σ t =ᶠ[nhds x] 0 := by
      rcases hxOutside with hxLow | hxHigh
      · filter_upwards [Iio_mem_nhds hxLow] with y hy
        pm_1223 typeIDyadicCutoff_eq_zero_of_le_half
      · filter_upwards [Ioi_mem_nhds hxHigh] with y hy
        pm_1223 typeIDyadicCutoff_eq_zero_of_two_le
    apply hx
    pm_4857
  have hEq : f = Set.indicator (Set.Icc (1 / 2 : ℝ) 2) f := by
    funext x
    by_cases hx : x ∈ Set.Icc (1 / 2 : ℝ) 2
    · exact (Set.indicator_of_mem hx _).symm
    · have : f x = 0 := not_ne_iff.mp fun hne => hx (hsupport hne)
      simp only [Set.indicator, hx, ite_false]
      exact this
  pm_1341 typeINormalizedKernel σ
  calc
    (∫ x : ℝ in Set.Icc (1 / 2) 2, f x) ≤
        ∫ _x : ℝ in Set.Icc (1 / 2) 2, D * (1 + |t|) ^ p := by
      apply MeasureTheory.setIntegral_mono_on
      · exact hfInt.integrableOn
      · exact MeasureTheory.integrableOn_const
          (hs := ne_of_lt
            (measure_Icc_lt_top : volume (Set.Icc (1 / 2 : ℝ) 2) < (⊤ : ENNReal)))
      · exact measurableSet_Icc
      · intro x hx
        exact hbound t x
    _ = (3 / 2 : ℝ) * D * (1 + |t|) ^ p := by
      norm_num [max_eq_left]
      ring

/-- Uniform Fourier decay for the source-faithful normalized Type-I kernel.
The constant is independent of both the ordinate and Fourier frequency. -/
theorem typeINormalizedFourier_uniform_decay (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ,
      |ξ| ^ n * ‖typeINormalizedFourier σ t ξ‖ ≤
        C * (1 + |t|) ^ n := by
  choose D hD hDbound using fun p : ℕ =>
    typeINormalizedKernel_uniform_iteratedFDeriv σ p
  let C : ℝ := 2 ^ n * (3 / 2) * ∑ p ∈ Finset.range (n + 1), D p
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (by positivity) (by norm_num))
      (Finset.sum_nonneg fun p _ => hD p)
  pc_94 typeINormalizedKernel σ normalizedSchwartz_coe typeINormalizedKernelSchwartz contDiff_typeINormalizedKernel typeINormalizedFourier
  calc
    |ξ| ^ n * ‖typeINormalizedFourier σ t ξ‖ ≤
        2 ^ n * ∑ p ∈ Finset.range (n + 1),
          ∫ x : ℝ, ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖ := hFourier'
    _ ≤ 2 ^ n * ∑ p ∈ Finset.range (n + 1),
        ((3 / 2 : ℝ) * D p) * (1 + |t|) ^ n := by
      pm_4859
      have hint := integral_norm_iteratedFDeriv_typeINormalizedKernel_le
        σ p (hDbound p) t
      calc
        (∫ x : ℝ, ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖) ≤
            (3 / 2 : ℝ) * D p * (1 + |t|) ^ p := hint
        _ ≤ (3 / 2 : ℝ) * D p * (1 + |t|) ^ n := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by nlinarith [abs_nonneg t]) hpn)
            (mul_nonneg (by norm_num) (hD p))
    _ = C * (1 + |t|) ^ n := by
      dsimp only [C]
      rw [← Finset.sum_mul]
      rw [← Finset.mul_sum]
      ring
end

/-- The complete scaled Poisson tail outside the symmetric mode window
`|m| ≤ M`.  The physical dilation contributes the factor `Q`. -/
noncomputable def typeINormalizedFarTail
    (σ t : ℝ) (Q M : ℕ) : ℂ :=
  ∑' m : ℤ, if M < m.natAbs then
    (Q : ℂ) * typeINormalizedFourier σ t ((Q : ℝ) * (m : ℝ)) else 0

/-- Arbitrary-order version of `typeINormalizedFarTail_bound`.  Keeping the
order visible is essential in endpoint arguments: the physical cutoff may be
only `T^d` beyond the stationary window, where `d` is chosen after the final
epsilon. -/
theorem typeINormalizedFarTail_bound_order (σ : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (Q M : ℕ),
      0 < Q → 0 < M →
      ‖typeINormalizedFarTail σ t Q M‖ ≤
        K * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n) := by
  obtain ⟨C₀, hC₀, hDecay⟩ :=
    typeINormalizedFourier_uniform_decay σ (n + 2)
  let C : ℝ := C₀ + 1
  pm_4638 hC C
  have hPSeries : Summable (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) := by
    have hNorm : (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) =
        fun m : ℤ => |1 / (m : ℝ) ^ 2| := by
      pm_4787
    rw [hNorm, summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (by norm_num)
  pm_527
  pm_4786
  intro t Q M hQ hM
  pm_456 hQr Q hQ
  pm_456 hMr M hM
  let scale : ℝ := C * (1 + |t|) ^ (n + 2) /
    ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n)
  have hPointwise : ∀ m : ℤ, M < m.natAbs →
      ‖(Q : ℂ) * typeINormalizedFourier σ t
          ((Q : ℝ) * (m : ℝ))‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    pm_5690
    pm_4784 hmReal m hmNe
    pm_4785 hmAbsPos
    pm_444
    have hFreqAbs : |(Q : ℝ) * (m : ℝ)| =
        (Q : ℝ) * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos hQr]
    pm_101 Q typeINormalizedFourier σ
    have hDenSmall : 0 < (Q : ℝ) ^ (n + 1) *
        ((M : ℝ) ^ n * |(m : ℝ)| ^ 2) := by positivity
    have hDenLarge : 0 < (Q : ℝ) ^ (n + 1) *
        |(m : ℝ)| ^ (n + 2) := by positivity
    rw [norm_mul, Complex.norm_natCast, norm_div, norm_one, norm_pow,
      Complex.norm_intCast]
    calc
      (Q : ℝ) *
          ‖typeINormalizedFourier σ t ((Q : ℝ) * (m : ℝ))‖ ≤
        (Q : ℝ) * (C₀ * (1 + |t|) ^ (n + 2) /
          |(Q : ℝ) * (m : ℝ)| ^ (n + 2)) := by gcongr
      _ = C₀ * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * |(m : ℝ)| ^ (n + 2)) := by
        rw [hFreqAbs, mul_pow]
        field_simp [hQr.ne']
        pm_6079
        ring
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * |(m : ℝ)| ^ (n + 2)) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
            (by positivity)) hDenLarge.le
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) *
            ((M : ℝ) ^ n * |(m : ℝ)| ^ 2)) := by
        exact div_le_div_of_nonneg_left (by positivity) hDenSmall
          (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = scale * (1 / |(m : ℝ)| ^ 2) := by
        dsimp only [scale]
        field_simp [hQr.ne', hMr.ne', hmAbsPos.ne']
  have hComparison : ∀ m : ℤ,
      ‖if M < m.natAbs then
          (Q : ℂ) * typeINormalizedFourier σ t
            ((Q : ℝ) * (m : ℝ)) else 0‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    pm_370
  have hScaledSummable : Summable
      (fun m : ℤ => scale * ‖1 / (m : ℂ) ^ 2‖) :=
    hPSeries.mul_left scale
  pm_126 hBound tsum_of_norm_bounded hScaledSummable.hasSum hComparison tsum_mul_left
  change ‖typeINormalizedFarTail σ t Q M‖ ≤ scale * B at hBound
  have hDen : 0 < (Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n := by positivity
  calc
    ‖typeINormalizedFarTail σ t Q M‖ ≤ scale * B := hBound
    _ ≤ (C * B + 1) * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n) := by
      pm_500

/-! ## Exact scaled Poisson assembly -/

/-- The `typeINormalizedScaledKernel` definition used by the source-facing construction in `TypeIReflection`. -/
noncomputable def typeINormalizedScaledKernel
    (σ t Q x : ℝ) : ℂ :=
  typeINormalizedKernel σ t (x / Q)

theorem contDiff_typeINormalizedScaledKernel
    (σ t Q : ℝ) :
    ContDiff ℝ ∞ (typeINormalizedScaledKernel σ t Q) := by
  unfold typeINormalizedScaledKernel
  exact (contDiff_typeINormalizedKernel σ t).comp
    (contDiff_id.div_const Q)

theorem hasCompactSupport_typeINormalizedScaledKernel
    (σ t Q : ℝ) (hQ : 0 < Q) :
    HasCompactSupport (typeINormalizedScaledKernel σ t Q) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (Q / 2) (2 * Q)))
  intro x hx
  have hOutside : x / Q ∉ Set.Icc (1 / 2 : ℝ) 2 := by
    pm_7862
    · have := (le_div_iff₀ hQ).mp hScaled.1
      linarith
    · exact (div_le_iff₀ hQ).mp hScaled.2
  have hcut : typeIDyadicCutoff (x / Q) = 0 := by
    by_cases hhalf : x / Q ≤ 1 / 2
    · exact typeIDyadicCutoff_eq_zero_of_le_half hhalf
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      exact le_of_not_ge fun htwo => hOutside ⟨le_of_not_ge hhalf, htwo⟩
  simp [typeINormalizedScaledKernel, typeINormalizedKernel,
    typeINormalizedAmplitude, hcut]

/-- The `typeINormalizedScaledKernelSchwartz` definition used by the source-facing construction in `TypeIReflection`. -/
noncomputable def typeINormalizedScaledKernelSchwartz
    (σ t Q : ℝ) (hQ : 0 < Q) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeINormalizedScaledKernel σ t Q hQ).toSchwartzMap
    (contDiff_typeINormalizedScaledKernel σ t Q)

@[simp]
theorem typeINormalizedScaledKernelSchwartz_apply
    (σ t Q x : ℝ) (hQ : 0 < Q) :
    typeINormalizedScaledKernelSchwartz σ t Q hQ x =
      typeINormalizedKernel σ t (x / Q) := rfl

theorem typeINormalizedScaledKernel_fourier
    (σ t Q ξ : ℝ) (hQ : 0 < Q) :
    𝓕 (typeINormalizedScaledKernelSchwartz σ t Q hQ) ξ =
      (Q : ℂ) * typeINormalizedFourier σ t (Q * ξ) := by
  pm_1454 Q typeINormalizedKernel σ hQ typeINormalizedFourier
  simp only [Real.inner_apply, typeINormalizedScaledKernelSchwartz_apply,
    typeINormalizedKernelSchwartz_apply, smul_eq_mul]
  calc
    (∫ x : ℝ,
        Complex.exp (((-2 * Real.pi * (x * ξ) : ℝ) : ℂ) * I) *
          typeINormalizedKernel σ t (x / Q)) =
        ∫ x : ℝ, g (x / Q) := by
      pm_593 Q hQ.ne'
    _ = Q • ∫ y : ℝ, g y := hChange
    _ = (Q : ℂ) * ∫ y : ℝ,
        Complex.exp (((-2 * Real.pi * (y * (Q * ξ)) : ℝ) : ℂ) * I) *
          typeINormalizedKernel σ t y := by
      pm_5369 Q
      congr 2
      push_cast
      ring

/-- Poisson summation for the normalized medium Type-I kernel at physical
scale `Q`. -/
theorem typeINormalizedKernel_poisson
    (σ t Q : ℝ) (hQ : 0 < Q) :
    ∑' n : ℤ, typeINormalizedKernel σ t ((n : ℝ) / Q) =
      ∑' m : ℤ,
        (Q : ℂ) * typeINormalizedFourier σ t (Q * (m : ℝ)) := by
  have hPoisson := SchwartzMap.tsum_eq_tsum_fourier
    (typeINormalizedScaledKernelSchwartz σ t Q hQ) 0
  simpa [typeINormalizedScaledKernel_fourier σ t Q _ hQ] using hPoisson

/-- The finite symmetric retained-mode contribution, represented as a
finitely supported integer series. -/
noncomputable def typeINormalizedCentralModes
    (σ t : ℝ) (Q M : ℕ) : ℂ :=
  ∑' m : ℤ, if m.natAbs ≤ M then
    (Q : ℂ) * typeINormalizedFourier σ t
      ((Q : ℝ) * (m : ℝ)) else 0

private theorem typeINormalizedScaledFourier_summable
    (σ t Q : ℝ) (hQ : 0 < Q) :
    Summable (fun m : ℤ =>
      (Q : ℂ) * typeINormalizedFourier σ t (Q * (m : ℝ))) := by
  let F : 𝓢(ℝ, ℂ) :=
    𝓕 (typeINormalizedScaledKernelSchwartz σ t Q hQ)
  have hBigO := F.isBigO_cocompact_rpow (-2)
  have hSummable : Summable (fun m : ℤ => F (m : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hBigO.comp_tendsto Int.tendsto_coe_cofinite)
  simpa [F, typeINormalizedScaledKernel_fourier σ t Q _ hQ] using hSummable

theorem typeINormalizedPoisson_split
    (σ t : ℝ) (Q M : ℕ) (hQ : 0 < Q) :
    (∑' n : ℤ,
        typeINormalizedKernel σ t ((n : ℝ) / (Q : ℝ))) =
      typeINormalizedCentralModes σ t Q M +
        typeINormalizedFarTail σ t Q M := by
  pm_74 hQr Q hQ
  rw [typeINormalizedKernel_poisson σ t (Q : ℝ) hQr]
  let f : ℤ → ℂ := fun m =>
    (Q : ℂ) * typeINormalizedFourier σ t
      ((Q : ℝ) * (m : ℝ))
  have hf : Summable f := by
    simpa only [f, Complex.ofReal_natCast] using typeINormalizedScaledFourier_summable
      σ t (Q : ℝ) hQr
  have hcentral : Summable (fun m : ℤ =>
      if m.natAbs ≤ M then f m else 0) := by
    have hi := hf.indicator {m : ℤ | m.natAbs ≤ M}
    convert hi using 1
    funext m
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hfar : Summable (fun m : ℤ =>
      if M < m.natAbs then f m else 0) := by
    pm_6082
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  change (∑' m : ℤ, f m) =
    (∑' m : ℤ, if m.natAbs ≤ M then f m else 0) +
      ∑' m : ℤ, if M < m.natAbs then f m else 0
  pm_6739
  · simp [hm, Nat.not_lt_of_ge hm, f]
  · have hm' : M < m.natAbs := Nat.lt_of_not_ge hm
    simp [hm, hm', f]

end GuthMaynard.NativeMoment
