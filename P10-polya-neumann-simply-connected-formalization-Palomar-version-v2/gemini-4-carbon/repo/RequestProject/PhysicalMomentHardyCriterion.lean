module

public import RequestProject.Driven
public import RequestProject.ArcLength
public import RequestProject.ExteriorConnected
public import RequestProject.LocalConformalBoundaryLipschitz
public import RequestProject.LocalConformalBoundaryGeometry
public import RequestProject.PhysicalHardySupport
public import RequestProject.BoundaryFourierMultiplier
public import RequestProject.FourierLipschitz
public import RequestProject.CutFourier
public import RequestProject.Unitarity
public import Mathlib.Topology.Piecewise
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Banach FTC, Periodic Fourier IBP, Cauchy Boundary Extension, and Physical Moment Hardy Criterion

Unifies Banach-valued interval-integral absolute continuity and FTC, periodic AC
Fourier integration by parts, exterior vanishing and Jordan Cauchy boundary
extension for `physicalWeightedCauchy`, and the physical antiholomorphic moment
criterion for `L²` (and continuous) boundary densities in conformal coordinates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric AbsolutelyContinuousOnInterval
open scoped ComplexConjugate Topology

local instance physicalMomentCriterionTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-! ## Banach-valued absolute continuity, FTC, and Fourier integration by parts -/

theorem c1_absolutelyContinuousOnInterval {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    AbsolutelyContinuousOnInterval f 0 (2 * Real.pi) := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
  exact (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hK :
    LipschitzOnWith K f _).absolutelyContinuousOnInterval

theorem continuousOn_memLp_boundary {V : Type*} [NormedAddCommGroup V] {f : ℝ → V}
    (hf : ContinuousOn f (Icc 0 (2 * Real.pi))) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Ioc_subset_Icc_self hx))

theorem continuous_mul_memLp_boundary {a f : ℝ → ℂ} (ha : Continuous a)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    MemLp (fun θ => a θ * f θ) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (ha.continuousOn : ContinuousOn a (Icc 0 (2 * Real.pi)))
  refine hf.of_le_mul (c := C) (ha.aestronglyMeasurable.restrict.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  simpa only [Pi.mul_apply, norm_mul] using
    mul_le_mul_of_nonneg_right (hC θ (Ioc_subset_Icc_self hθ)) (norm_nonneg _)

/-- A Banach-valued primitive is genuinely absolutely continuous. -/
theorem absolutelyContinuousOnInterval_intervalIntegral_banach
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f : ℝ → V} {a b c : ℝ} (hf : IntervalIntegrable f volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, f t) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) => ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have hlim : Tendsto (fun i => ∫⁻ x in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero (ne_of_lt (intervalIntegrable_iff.mp hf).hasFiniteIntegral)
      (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  have hlim' := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlim
  refine squeeze_zero' ?_ ?_ hlim'
  · filter_upwards with E
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  simp only [Function.comp_apply, s]
  have hmem : ∀ᶠ E : ℕ × (ℕ → ℝ × ℝ) in totalLengthFilter ⊓ 𝓟 (disjWithin a b),
      E ∈ disjWithin a b := eventually_inf_principal.mpr (by simp)
  filter_upwards [hmem] with E hE
  obtain ⟨_, hE2⟩ := mem_setOf_eq ▸ hE
  rw [← integral_norm_eq_lintegral_enorm (hf.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hE2]
  · refine Finset.sum_le_sum (fun i hi => ?_)
    rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left
      (by apply IntervalIntegrable.mono_set' hf; grind [uIoc, uIcc])
      (by apply IntervalIntegrable.mono_set' hf; grind [uIoc, uIcc]),
      Measure.restrict_restrict_of_subset
        (uIoc_subset_of_mem_disjWithin hE (Finset.mem_range.mp hi))]
    simpa only [uIoc_comm] using
      (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := f)
        (a := (E.2 i).2) (b := (E.2 i).1))
  · intro i hi
    unfold IntegrableOn
    have hsub := uIoc_subset_of_mem_disjWithin hE (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsub]
    exact (IntegrableOn.mono_set hf.def'.norm hsub).integrable

/-- The actual a.e. primitive derivative, localized to a finite interval. -/
theorem ae_hasDerivAt_intervalIntegral_banach
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f : ℝ → V} {L : ℝ} (hL : 0 ≤ L) (hf : IntervalIntegrable f volume 0 L) :
    ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, f t) (f x) x := by
  have hfi : IntegrableOn f (Icc 0 L) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mp hf
  let G := (Icc 0 L).indicator f
  have hGi : Integrable G := hfi.integrable_indicator measurableSet_Icc
  filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable]
    with x hx hmem
  have hxc := Ioo_subset_Icc_self hmem
  have hd := hx 0
  rw [show G x = f x by simp [G, indicator_of_mem hxc]] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with y hy
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hy.1.le] at ht
  have htc : t ∈ Icc 0 L := ⟨ht.1, ht.2.trans hy.2.le⟩
  simp [G, indicator_of_mem htc]

/-- True Banach-valued FTC from absolute continuity and the actual a.e. derivative. -/
theorem eq_add_intervalIntegral_of_ac_ae_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f g : ℝ → V} {L : ℝ} (hL : 0 ≤ L)
    (hf : AbsolutelyContinuousOnInterval f 0 L) (hg : IntegrableOn g (Icc 0 L))
    (hd : ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt f (g x) x) :
    ∀ θ ∈ Icc 0 L, f θ = f 0 + ∫ s in (0 : ℝ)..θ, g s := by
  let G := (Icc 0 L).indicator g
  have hGi : Integrable G := hg.integrable_indicator measurableSet_Icc
  let P : ℝ → V := fun x => ∫ s in (0 : ℝ)..x, G s
  have hP : AbsolutelyContinuousOnInterval P 0 L :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hGi.intervalIntegrable
      (by rw [uIcc_of_le hL]; exact ⟨le_rfl, hL⟩)
  have hPeq (θ : ℝ) (hθ : θ ∈ Icc 0 L) : P θ = ∫ s in (0 : ℝ)..θ, g s :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le hθ.1] at hs
      have hsc : s ∈ Icc 0 L := ⟨hs.1, hs.2.trans hθ.2⟩
      simp [G, indicator_of_mem hsc]
  have hz : ∀ᵐ x, x ∈ uIcc 0 L → HasDerivAt (f - P) 0 x := by
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have h1 : ∀ᵐ x : ℝ, x ≠ L := by simp [ae_iff, measure_singleton]
    filter_upwards [hd, ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable,
      h0, h1] with x hx hxP hx0 hxL hxc
    rw [uIcc_of_le hL] at hxc
    simpa only [P, G, indicator_of_mem hxc, sub_self] using
      (hx ⟨lt_of_le_of_ne hxc.1 (Ne.symm hx0), lt_of_le_of_ne hxc.2 hxL⟩).sub (hxP 0)
  obtain ⟨c, hc⟩ := (hf.sub hP).const_of_ae_hasDerivAt_zero hz
  intro θ hθ
  have hc0 := hc 0 (by rw [uIcc_of_le hL]; exact ⟨le_rfl, hL⟩)
  have hcθ := hc θ (by rw [uIcc_of_le hL]; exact hθ)
  simp only [Pi.sub_apply, P, intervalIntegral.integral_same, sub_zero] at hc0
  change f θ - P θ = c at hcθ
  rw [← hc0, hPeq θ hθ] at hcθ
  exact (by abel : f θ = (f θ - ∫ s in (0 : ℝ)..θ, g s) + ∫ s in (0 : ℝ)..θ, g s).trans
    (by rw [hcθ])

/-- Complex Fourier integration by parts for an AC function and its a.e. `L²` derivative. -/
theorem fourierCoeffOn_of_ac_ae_hasDerivAt
    {f f' : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 (2 * Real.pi))
    (hf' : MemLp f' 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) → HasDerivAt f (f' θ) θ)
    (hp : f 0 = f (2 * Real.pi)) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos f' n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos f n := by
  let e : ℝ → ℂ := fun θ => fourier (-n) (θ : AddCircle (2 * Real.pi))
  let α : ℂ := -(Complex.I * (n : ℂ))
  have hec : Continuous e := (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  have hen (θ : ℝ) : ‖e θ‖ = 1 := norm_fourier_coe (-n) θ
  have he1 : ContDiff ℝ 1 e := by
    dsimp only [e]; simp_rw [fourier_coe_two_pi]
    exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const).cexp
  have heD (θ : ℝ) : HasDerivAt e (α * e θ) θ := by
    have hα : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / ((2 * Real.pi : ℝ) : ℂ) = α := by
      dsimp only [α]; push_cast; field_simp [Real.pi_ne_zero]
    simpa only [hα] using hasDerivAt_fourier_neg (2 * Real.pi) n θ
  have hfC : ContinuousOn f (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf.continuousOn
  have hf'i : IntegrableOn f' (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hf'
  have hfe : IntegrableOn (fun θ => f θ * e θ) (Icc 0 (2 * Real.pi)) :=
    hfC.integrableOn_Icc.mul_bdd hec.aestronglyMeasurable.restrict
      (Eventually.of_forall fun θ => (hen θ).le)
  have hf'e : IntegrableOn (fun θ => f' θ * e θ) (Icc 0 (2 * Real.pi)) :=
    hf'i.mul_bdd hec.aestronglyMeasurable.restrict (Eventually.of_forall fun θ => (hen θ).le)
  have hprodD : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (fun θ => f θ * e θ) (f' θ * e θ + α * (f θ * e θ)) θ := by
    filter_upwards [hd] with θ hθ hmem
    convert (hθ hmem).mul (heD θ) using 1; ring
  have hFTC := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (hf.smul (c1_absolutelyContinuousOnInterval he1)) (hf'e.add (hfe.const_mul α))
    hprodD (2 * Real.pi) ⟨Real.two_pi_pos.le, le_rfl⟩
  have he0 : e 0 = 1 := by
    change fourier (-n) ((0 : ℝ) : AddCircle (2 * Real.pi)) = 1
    rw [AddCircle.coe_zero, fourier_eval_zero]
  have heL : e (2 * Real.pi) = 1 := by
    change fourier (-n) ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = 1
    rw [AddCircle.coe_period, fourier_eval_zero]
  simp only [smul_eq_mul, Pi.mul_apply, Pi.add_apply] at hFTC
  have hi0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), f' θ * e θ + α * (f θ * e θ)) = 0 := by
    rw [he0, heL, mul_one, mul_one, ← hp] at hFTC
    exact add_left_cancel (show f 0 + (∫ θ in (0 : ℝ)..(2 * Real.pi),
      f' θ * e θ + α * (f θ * e θ)) = f 0 + 0 by simpa only [add_zero] using hFTC.symm)
  have hife : IntervalIntegrable (fun θ => f θ * e θ) volume 0 (2 * Real.pi) :=
    IntegrableOn.intervalIntegrable (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hfe)
  have hif'e : IntervalIntegrable (fun θ => f' θ * e θ) volume 0 (2 * Real.pi) :=
    IntegrableOn.intervalIntegrable (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hf'e)
  rw [intervalIntegral.integral_add hif'e (hife.const_mul α),
    intervalIntegral.integral_const_mul] at hi0
  have hi : (∫ θ in (0 : ℝ)..(2 * Real.pi), f' θ * e θ) =
      (Complex.I * (n : ℂ)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * e θ) := by
    dsimp only [α] at hi0
    exact eq_of_sub_eq_zero (by simpa only [neg_mul, ← sub_eq_add_neg] using hi0)
  have hi' : (∫ θ in (0 : ℝ)..(2 * Real.pi), e θ * f' θ) =
      (Complex.I * (n : ℂ)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), e θ * f θ) := by
    simpa only [mul_comm] using hi
  simp only [e, fourier_coe_apply] at hi'
  simp only [fourierCoeffOn_eq_integral, smul_eq_mul, Complex.real_smul, fourier_coe_apply, sub_zero]
  rw [hi']; ring

theorem isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    {f f' : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 (2 * Real.pi))
    (hf' : MemLp f' 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) → HasDerivAt f (f' θ) θ)
    (hp : f 0 = f (2 * Real.pi)) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos f) := by
  have hfC : ContinuousOn f (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf.continuousOn
  have hs := (hasSum_sq_fourierCoeffOn Real.two_pi_pos (continuousOn_memLp_boundary hfC)).summable
  have hs' := (hasSum_sq_fourierCoeffOn Real.two_pi_pos hf').summable
  change Summable (fun n : ℤ => (sobWeight n ^ (1 : ℝ) * ‖fourierCoeffOn Real.two_pi_pos f n‖) ^ 2)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((hs.mul_left 2).add (hs'.mul_left 2))
  have hdn : ‖fourierCoeffOn Real.two_pi_pos f' n‖ ^ 2 =
      (n : ℝ) ^ 2 * ‖fourierCoeffOn Real.two_pi_pos f n‖ ^ 2 := by
    rw [fourierCoeffOn_of_ac_ae_hasDerivAt hf hf' hd hp n]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, mul_pow, sq_abs]
  rw [hdn]
  simp only [sobWeight, Real.rpow_one]
  have hsq := sq_nonneg ((|(n : ℝ)| - 1) * ‖fourierCoeffOn Real.two_pi_pos f n‖)
  rw [← sq_abs (n : ℝ)]
  nlinarith [norm_nonneg (fourierCoeffOn Real.two_pi_pos f n), abs_nonneg (n : ℝ)]

/-! ## Physical moment primitive and weighted Cauchy transform -/

/-- The physical interval primitive, normalized at the supplied boundary origin. -/
def physicalMomentPrimitive (γ H : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..θ, conj (deriv γ s) * H s

@[simp] theorem physicalMomentPrimitive_zero (γ H : ℝ → ℂ) :
    physicalMomentPrimitive γ H 0 = 0 := by
  simp only [physicalMomentPrimitive, intervalIntegral.integral_same]

theorem physicalMomentPrimitive_endpoint (γ H : ℝ → ℂ)
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    physicalMomentPrimitive γ H (2 * Real.pi) = 0 := hmom0

theorem contDiff_physicalMomentPrimitive (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ) (hH : Continuous H) :
    ContDiff ℝ 1 (physicalMomentPrimitive γ H) := by
  have hd (θ : ℝ) : HasDerivAt (physicalMomentPrimitive γ H) (conj (deriv γ θ) * H θ) θ :=
    (((Complex.continuous_conj.comp hγ.continuous_deriv_one).mul hH).integral_hasStrictDerivAt
      0 θ).hasDerivAt
  refine contDiff_one_iff_deriv.mpr ⟨fun θ => (hd θ).differentiableAt, ?_⟩
  rw [show deriv (physicalMomentPrimitive γ H) = fun θ => conj (deriv γ θ) * H θ from
    funext fun θ => (hd θ).deriv]
  exact (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul hH

theorem physicalMomentPrimitive_periodic (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (hpH : Function.Periodic H (2 * Real.pi))
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    Function.Periodic (physicalMomentPrimitive γ H) (2 * Real.pi) := by
  let g : ℝ → ℂ := fun θ => conj (deriv γ θ) * H θ
  have hg : Continuous g := (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul hH
  have hgp : Function.Periodic g (2 * Real.pi) := fun θ => by
    simp only [g, deriv_periodic hpγ θ, hpH θ]
  intro θ
  change (∫ s in (0 : ℝ)..(θ + 2 * Real.pi), g s) = ∫ s in (0 : ℝ)..θ, g s
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 θ)
    (hg.intervalIntegrable θ _), ← hgp.intervalIntegral_add_eq 0 θ, zero_add, hmom0, add_zero]

/-- Integration by parts transfers all centered antiholomorphic moments from any `L²`
input `H` to `physicalMomentPrimitive γ H`. -/
theorem physicalMomentPrimitive_moments_of_memLp (γ H : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0) (m : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv γ θ) * physicalMomentPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) = 0 := by
  have hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0 := by
    simpa only [pow_zero, mul_one] using hmom 0
  let a : ℝ → ℂ := fun θ => conj (deriv γ θ)
  let z : ℝ → ℂ := fun θ => conj (γ θ) - conj (γ 0)
  let K := physicalMomentPrimitive γ H
  let ν : ℝ → ℂ := fun θ => a θ * H θ
  let c : ℂ := (m + 1 : ℕ)
  have ha : Continuous a := Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hz : ContDiff ℝ 1 z := (Complex.conjCLE.contDiff.comp hγ).sub contDiff_const
  have hν_mem : MemLp ν 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    continuous_mul_memLp_boundary ha hH
  have hνI : IntegrableOn ν (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]; exact hν_mem.integrable (by norm_num)
  have hν_int : IntervalIntegrable ν volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
      (hν_mem.integrable (by norm_num))
  have hKAC : AbsolutelyContinuousOnInterval K 0 (2 * Real.pi) :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hν_int
      (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hKC : ContinuousOn K (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hKAC.continuousOn
  have hfirst : IntegrableOn (fun θ => ν θ * z θ ^ (m + 1)) (Icc 0 (2 * Real.pi)) :=
    hνI.mul_continuousOn (hz.continuous.pow (m + 1)).continuousOn isCompact_Icc
  have hsecond : IntegrableOn (fun θ => (a θ * K θ) * z θ ^ m) (Icc 0 (2 * Real.pi)) :=
    ((ha.continuousOn.mul hKC).mul (hz.continuous.pow m).continuousOn).integrableOn_Icc
  have hprodD : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (fun θ => K θ * z θ ^ (m + 1))
        (ν θ * z θ ^ (m + 1) + c * ((a θ * K θ) * z θ ^ m)) θ := by
    filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hν_int]
      with θ hθ hmem
    have dz : HasDerivAt z (a θ) θ := by
      simpa only [Complex.star_def] using ((hγ.differentiable_one θ).hasDerivAt.star).sub_const _
    convert (hθ hmem).mul (dz.pow (m + 1)) using 1
    · funext x; simp only [Pi.mul_apply, Pi.pow_apply]; dsimp [ν, a, K, physicalMomentPrimitive]
    · dsimp [ν, a, K, c, physicalMomentPrimitive]; push_cast; ring
  have hFTC := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (hKAC.smul (c1_absolutelyContinuousOnInterval (hz.pow (m + 1))))
    (hfirst.add (hsecond.const_mul c)) hprodD (2 * Real.pi) ⟨Real.two_pi_pos.le, le_rfl⟩
  simp only [smul_eq_mul, Pi.mul_apply, Pi.add_apply] at hFTC
  rw [show K 0 = 0 from physicalMomentPrimitive_zero γ H,
    show K (2 * Real.pi) = 0 from physicalMomentPrimitive_endpoint γ H hmom0,
    zero_mul, zero_mul, zero_add] at hFTC
  have hi₁ : IntervalIntegrable (fun θ => ν θ * z θ ^ (m + 1)) volume 0 (2 * Real.pi) :=
    IntegrableOn.intervalIntegrable (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hfirst)
  have hi₂ : IntervalIntegrable (fun θ => (a θ * K θ) * z θ ^ m) volume 0 (2 * Real.pi) :=
    IntegrableOn.intervalIntegrable (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hsecond)
  change 0 = ∫ θ in (0 : ℝ)..(2 * Real.pi), (ν θ * z θ ^ (m + 1) + c * ((a θ * K θ) * z θ ^ m)) at hFTC
  rw [intervalIntegral.integral_add hi₁ (hi₂.const_mul c),
    intervalIntegral.integral_const_mul, hmom (m + 1), zero_add] at hFTC
  exact (mul_eq_zero.mp hFTC.symm).resolve_left
    (by dsimp [c]; exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))

/-- The weighted Cauchy integral with the winding-number denominator sign. -/
def physicalWeightedCauchy (γ K : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv γ θ * K θ) / (γ θ - z)

/-- Differentiation of `physicalWeightedCauchy` away from the curve. -/
theorem physicalWeightedCauchy_hasDerivAt
    (γ K : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hK : Continuous K) {w₀ : ℂ}
    (havoid : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), γ θ ≠ w₀) :
    HasDerivAt (physicalWeightedCauchy γ K)
      (∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv γ θ * K θ) / (γ θ - w₀) ^ 2) w₀ := by
  let g : ℝ → ℂ := fun θ => deriv γ θ * K θ
  have hg : Continuous g := hγ.continuous_deriv_one.mul hK
  obtain ⟨d, hd, hdθ⟩ := exists_pos_le_norm_sub hγ.continuous havoid
  have hsep (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi))
      (w : ℂ) (hw : w ∈ Metric.ball w₀ (d / 2)) : d / 2 ≤ ‖γ θ - w‖ := by
    have hw' : ‖w - w₀‖ < d / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hlower : d ≤ ‖γ θ - w₀‖ := hdθ θ hθ
    have htri : ‖γ θ - w₀‖ ≤ ‖γ θ - w‖ + ‖w - w₀‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (γ θ - w) (w - w₀)
    linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * Real.pi)) hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hFi : IntervalIntegrable (fun θ => g θ / (γ θ - w₀)) volume 0 (2 * Real.pi) :=
    ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
      (hg.continuousOn.div (hγ.continuous.sub continuous_const).continuousOn
        fun θ hθ => sub_ne_zero.mpr (havoid θ hθ))
  have hbint : Integrable (fun _ : ℝ => M / (d / 2) ^ 2)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => M / (d / 2) ^ 2) volume 0 (2 * Real.pi)).1
  have hb : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      ∀ w ∈ Metric.ball w₀ (d / 2), ‖g θ / (γ θ - w) ^ 2‖ ≤ M / (d / 2) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ w hw
    rw [norm_div, norm_pow]
    exact div_le_div₀ hM0 (hM θ ⟨hθ.1.le, hθ.2⟩) (sq_pos_of_pos (half_pos hd))
      ((sq_le_sq₀ (half_pos hd).le (norm_nonneg _)).mpr (hsep θ ⟨hθ.1.le, hθ.2⟩ w hw))
  have hdif : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      ∀ w ∈ Metric.ball w₀ (d / 2),
        HasDerivAt (fun v : ℂ => g θ / (γ θ - v)) (g θ / (γ θ - w) ^ 2) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ w hw
    have hne : γ θ - w ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (half_pos hd) (hsep θ ⟨hθ.1.le, hθ.2⟩ w hw))
    convert (hasDerivAt_const w (g θ)).div
      ((hasDerivAt_const w (γ θ)).sub (hasDerivAt_id w)) hne using 1
    · funext v; simp [div_eq_mul_inv]
    · simp
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
    (F := fun w θ => g θ / (γ θ - w))
    (F' := fun w θ => g θ / (γ θ - w) ^ 2) (x₀ := w₀)
    (Metric.ball_mem_nhds w₀ (half_pos hd))
    (Eventually.of_forall fun _ =>
      (hg.measurable.div (hγ.continuous.measurable.sub measurable_const)).aestronglyMeasurable)
    hFi.1
    (hg.measurable.div
      ((hγ.continuous.measurable.sub measurable_const).pow_const 2)).aestronglyMeasurable
    hb hbint hdif
  change HasDerivAt
    (fun w : ℂ => ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (γ θ - w))
    (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (γ θ - w₀) ^ 2) w₀
  simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le] using hdiff.2

/-- Centered physical antiholomorphic moments force `physicalWeightedCauchy γ (conj ∘ H)`
to vanish throughout the connected exterior `(closure Ω)ᶜ`. -/
theorem physicalWeightedCauchy_conj_eq_zero_on_exterior_of_moments
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hfc : IsPreconnected (frontier Ω))
    (γ H : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (him : γ '' Icc (0 : ℝ) (2 * Real.pi) = frontier Ω)
    (hmom : ∀ m : ℕ,
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0) :
    ∀ w : ℂ, w ∉ closure Ω → physicalWeightedCauchy γ (fun θ => conj (H θ)) w = 0 := by
  let g : ℝ → ℂ := fun θ => deriv γ θ * conj (H θ)
  let z : ℝ → ℂ := fun θ => γ θ - γ 0
  have hg : Continuous g := hγ.continuous_deriv_one.mul (Complex.continuous_conj.comp hH)
  have hz : Continuous z := hγ.continuous.sub continuous_const
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * Real.pi)) hz.continuousOn
  have hR0 : 0 ≤ R := by simpa only [z, sub_self, norm_zero] using hR 0 ⟨le_rfl, Real.two_pi_pos.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * Real.pi)) hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hfar : ∀ w : ℂ, R < ‖w - γ 0‖ →
      physicalWeightedCauchy γ (fun θ => conj (H θ)) w = 0 := fun w hw => by
    let ξ : ℂ := w - γ 0
    have hξpos : 0 < ‖ξ‖ := lt_of_le_of_lt hR0 hw
    have hξ : ξ ≠ 0 := norm_pos_iff.mp hξpos
    let q : ℝ := R / ‖ξ‖
    have hq1 : q < 1 := (div_lt_one hξpos).mpr hw
    have hqsum : Summable (fun m : ℕ => (M / ‖ξ‖) * q ^ m) :=
      (summable_geometric_of_lt_one (div_nonneg hR0 hξpos.le) hq1).mul_left (M / ‖ξ‖)
    have hi : HasSum (fun m : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (-g θ / ξ) * (z θ / ξ) ^ m)
        (physicalWeightedCauchy γ (fun θ => conj (H θ)) w) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence
        (fun m _ => (M / ‖ξ‖) * q ^ m)
        (fun m => ((hg.neg.div_const ξ).mul ((hz.div_const ξ).pow m)).aestronglyMeasurable)
        (fun m => Eventually.of_forall fun θ hθ => ?_)
        (Eventually.of_forall fun _ _ => hqsum) intervalIntegrable_const
        (Eventually.of_forall fun θ hθ => ?_)
      · rw [uIoc_of_le Real.two_pi_pos.le] at hθ
        rw [norm_mul, norm_div, norm_neg, norm_pow, norm_div]
        dsimp only [q]; gcongr
        · exact hM θ ⟨hθ.1.le, hθ.2⟩
        · exact hR θ ⟨hθ.1.le, hθ.2⟩
      · rw [uIoc_of_le Real.two_pi_pos.le] at hθ
        have hratio : ‖z θ / ξ‖ < 1 := by
          rw [norm_div]
          exact lt_of_le_of_lt (div_le_div_of_nonneg_right (hR θ ⟨hθ.1.le, hθ.2⟩) hξpos.le) hq1
        have hs := (hasSum_geometric_of_norm_lt_one hratio).mul_left (-g θ / ξ)
        have hkernel : (-g θ / ξ) * (1 - z θ / ξ)⁻¹ = g θ / (γ θ - w) := by
          have hden : ξ * (1 - z θ / ξ) = -(γ θ - w) := by
            rw [show ξ * (1 - z θ / ξ) = ξ - z θ by field_simp [hξ]]
            dsimp only [ξ, z]; ring
          rw [← div_eq_mul_inv, div_div, hden, div_neg, neg_div, neg_neg]
        simpa only [hkernel] using hs
    have hint (m : ℕ) : (∫ θ in (0 : ℝ)..(2 * Real.pi), (-g θ / ξ) * (z θ / ξ) ^ m) = 0 := by
      rw [show (fun θ => (-g θ / ξ) * (z θ / ξ) ^ m) =
        fun θ => -(ξ⁻¹ * (ξ⁻¹) ^ m) * conj ((conj (deriv γ θ) * H θ) *
          (conj (γ θ) - conj (γ 0)) ^ m) from funext fun θ => by
            dsimp only [g, z]
            simp only [div_eq_mul_inv, mul_pow, map_mul, map_pow, map_sub, Complex.conj_conj]
            ring,
        intervalIntegral.integral_const_mul, intervalIntegral_conj, hmom m, map_zero, mul_zero]
    simpa only [hint, tsum_zero] using hi.tsum_eq.symm
  have hdiff : DifferentiableOn ℂ (physicalWeightedCauchy γ (fun θ => conj (H θ))) (closure Ω)ᶜ :=
    fun w hw => (physicalWeightedCauchy_hasDerivAt γ _ hγ (Complex.continuous_conj.comp hH)
      fun θ hθ heq => by
        have hγθ : γ θ ∈ frontier Ω := by rw [← him]; exact ⟨θ, hθ, rfl⟩
        exact hw (heq ▸ frontier_subset_closure hγθ)).differentiableAt.differentiableWithinAt
  have hana := hdiff.analyticOnNhd isClosed_closure.isOpen_compl
  obtain ⟨B, hB⟩ := hb.closure.subset_ball (γ 0)
  let T : ℝ := max B R + 1
  let w₀ : ℂ := γ 0 + (T : ℂ)
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right B R]
  have hw₀norm : ‖w₀ - γ 0‖ = T := by
    dsimp [w₀]; rw [add_sub_cancel_left, Complex.norm_of_nonneg hT.le]
  have hw₀R : R < ‖w₀ - γ 0‖ := by rw [hw₀norm]; dsimp [T]; linarith [le_max_right B R]
  have hw₀E : w₀ ∈ (closure Ω)ᶜ := fun hw₀ => by
    have hnorm : ‖w₀ - γ 0‖ < B := by simpa only [Metric.mem_ball, dist_eq_norm] using hB hw₀
    rw [hw₀norm] at hnorm; dsimp [T] at hnorm; linarith [le_max_left B R]
  have hevent : physicalWeightedCauchy γ (fun θ => conj (H θ)) =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [(isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).mem_nhds hw₀R] with w hw
    exact hfar w hw
  exact fun _ hw => hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isConnected_compl_closure_of_frontier hb hL hfc).isPreconnected hw₀E hevent hw

/-! ## All-approach Jordan Cauchy boundary extension -/

theorem exists_nearestPhysicalBoundaryParam (γ : ℝ → ℂ) (hγ : Continuous γ) (w : ℂ) :
    ∃ τ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), ‖γ τ - w‖ ≤ ‖γ θ - w‖ :=
  isCompact_Icc.exists_isMinOn ⟨0, le_rfl, Real.two_pi_pos.le⟩
    (hγ.sub continuous_const).norm.continuousOn

def nearestPhysicalBoundaryParam (γ : ℝ → ℂ) (hγ : Continuous γ) (w : ℂ) : ℝ :=
  Classical.choose (exists_nearestPhysicalBoundaryParam γ hγ w)

theorem nearestPhysicalBoundaryParam_chord_le (γ : ℝ → ℂ) (hγ : Continuous γ)
    (w : ℂ) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    ‖γ θ - γ (nearestPhysicalBoundaryParam γ hγ w)‖ ≤ 2 * ‖γ θ - w‖ := by
  have hm : ‖γ (nearestPhysicalBoundaryParam γ hγ w) - w‖ ≤ ‖γ θ - w‖ :=
    (Classical.choose_spec (exists_nearestPhysicalBoundaryParam γ hγ w)).2 θ hθ
  calc
    _ = ‖(γ θ - w) + (w - γ (nearestPhysicalBoundaryParam γ hγ w))‖ := by congr 1; ring
    _ ≤ ‖γ θ - w‖ + ‖γ (nearestPhysicalBoundaryParam γ hγ w) - w‖ := by
      simpa only [norm_sub_rev w] using norm_add_le (γ θ - w)
        (w - γ (nearestPhysicalBoundaryParam γ hγ w))
    _ ≤ _ := by linarith

def nearestPhysicalBoundaryDensity (γ : ℝ → ℂ) (hγ : Continuous γ)
    (K : ℝ → ℂ) (w : ℂ) : ℂ := K (nearestPhysicalBoundaryParam γ hγ w)

theorem nearestPhysicalBoundaryDensity_norm_sub_le
    (γ : ℝ → ℂ) (hγ : Continuous γ) (K : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (w : ℂ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    ‖nearestPhysicalBoundaryDensity γ hγ K w - K t‖ ≤ (2 * L) * ‖w - γ t‖ := by
  rw [nearestPhysicalBoundaryDensity, norm_sub_rev, norm_sub_rev w]
  exact (hchord _ _).trans ((mul_le_mul_of_nonneg_left
    (nearestPhysicalBoundaryParam_chord_le γ hγ w t ht) hL).trans_eq (by ring))

theorem nearestPhysicalBoundaryDensity_tendsto
    (γ : ℝ → ℂ) (hγ : Continuous γ) (K : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    Tendsto (nearestPhysicalBoundaryDensity γ hγ K) (𝓝 (γ t)) (𝓝 (K t)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr <|
    squeeze_zero (fun _ => norm_nonneg _)
      (fun w => nearestPhysicalBoundaryDensity_norm_sub_le γ hγ K hL hchord w t ht) ?_
  have hn : Tendsto (fun w : ℂ => ‖w - γ t‖) (𝓝 (γ t)) (𝓝 0) :=
    (continuous_id.sub continuous_const).norm.tendsto' (γ t) 0 (by simp)
  simpa only [mul_zero] using (tendsto_const_nhds.mul hn :
    Tendsto (fun w : ℂ => (2 * L) * ‖w - γ t‖) (𝓝 (γ t)) (𝓝 ((2 * L) * 0)))

def physicalNearestCauchyCommutator (γ : ℝ → ℂ) (hγ : Continuous γ)
    (K : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (deriv γ θ * (K θ - nearestPhysicalBoundaryDensity γ hγ K w)) / (γ θ - w)

theorem physicalNearestCauchyCommutator_tendsto
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (K : ℝ → ℂ) (hK : Continuous K)
    {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (hinj : InjOn γ (Ico (0 : ℝ) (2 * Real.pi)))
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    Tendsto (physicalNearestCauchyCommutator γ hγ.continuous K) (𝓝 (γ t))
      (𝓝 (∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv γ θ * (K θ - K t)) / (γ θ - γ t))) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * Real.pi)) hγ.continuous_deriv_one.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (deriv γ 0)).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hN := nearestPhysicalBoundaryDensity_tendsto γ hγ.continuous K hL hchord
    t (Ico_subset_Icc_self ht)
  unfold physicalNearestCauchyCommutator
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (bound := fun _ : ℝ => M * (2 * L)) ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun _ =>
      ((hγ.continuous_deriv_one.measurable.mul (hK.measurable.sub measurable_const)).div
        (hγ.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · refine Eventually.of_forall fun w => Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ
    by_cases hd : γ θ - w = 0
    · rw [hd, div_zero, norm_zero]; positivity
    · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hd), norm_mul]
      have hKθ : ‖K θ - nearestPhysicalBoundaryDensity γ hγ.continuous K w‖ ≤
          (2 * L) * ‖γ θ - w‖ := by
        simpa only [norm_sub_rev, norm_sub_rev (γ θ)] using
          nearestPhysicalBoundaryDensity_norm_sub_le γ hγ.continuous K hL hchord w θ ⟨hθ.1.le, hθ.2⟩
      exact ((mul_le_mul_of_nonneg_right (hM θ ⟨hθ.1.le, hθ.2⟩) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hKθ hM0)).trans_eq (by ring)
  · filter_upwards [volume.ae_ne t, volume.ae_ne (2 * Real.pi)] with θ hθt hθL hθ
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ
    exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub hN)).div
      ((continuous_const.sub continuous_id).tendsto (γ t))
      (sub_ne_zero.mpr fun he => hθt (hinj ⟨hθ.1.le, lt_of_le_of_ne hθ.2 hθL⟩ ht he))

theorem physicalWeightedCauchy_eq_nearestCommutator_add_winding
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (K : ℝ → ℂ) (hK : Continuous K)
    (w : ℂ) (havoid : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), γ θ ≠ w) :
    physicalWeightedCauchy γ K w = physicalNearestCauchyCommutator γ hγ.continuous K w +
      (2 * Real.pi * Complex.I) * nearestPhysicalBoundaryDensity γ hγ.continuous K w *
        windingNumber γ w := by
  let c := nearestPhysicalBoundaryDensity γ hγ.continuous K w
  let f : ℝ → ℂ := fun θ => (deriv γ θ * (K θ - c)) / (γ θ - w)
  let q : ℝ → ℂ := fun θ => deriv γ θ / (γ θ - w)
  have hf : IntervalIntegrable f volume 0 (2 * Real.pi) :=
    ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le <|
      (hγ.continuous_deriv_one.mul (hK.sub continuous_const)).continuousOn.div
        (hγ.continuous.sub continuous_const).continuousOn fun θ hθ => sub_ne_zero.mpr (havoid θ hθ)
  have hq : IntervalIntegrable q volume 0 (2 * Real.pi) :=
    ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le <|
      hγ.continuous_deriv_one.continuousOn.div
        (hγ.continuous.sub continuous_const).continuousOn fun θ hθ => sub_ne_zero.mpr (havoid θ hθ)
  have ha : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hconst : (2 * Real.pi * Complex.I) * c * windingNumber γ w =
      c * ∫ θ in (0 : ℝ)..(2 * Real.pi), q θ := by
    rw [windingNumber]
    change (2 * Real.pi * Complex.I) * c *
      ((2 * Real.pi * Complex.I)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) = _
    field_simp [ha]
  rw [hconst, physicalWeightedCauchy,
    show (fun θ => (deriv γ θ * K θ) / (γ θ - w)) = fun θ => f θ + c * q θ from
      funext fun _ => by dsimp [f, q]; ring,
    intervalIntegral.integral_add hf (hq.const_mul c), intervalIntegral.integral_const_mul]
  rfl

theorem exists_physicalCauchy_boundary_extension
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    (hfc : IsPreconnected (frontier Ω))
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico (0 : ℝ) (2 * Real.pi)))
    (him : γ '' Icc (0 : ℝ) (2 * Real.pi) = frontier Ω)
    (K : ℝ → ℂ) (hK : Continuous K) {L : ℝ} (hL : 0 ≤ L)
    (hchord : ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖γ θ - γ τ‖)
    (hzero : ∀ w : ℂ, w ∉ closure Ω → physicalWeightedCauchy γ K w = 0) :
    ∃ G : ℂ → ℂ, DiffContOnCl ℂ G Ω ∧
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), G (γ θ) = K θ := by
  classical
  obtain ⟨_, hLip⟩ := exists_periodic_C1_density_lipschitz γ hγ hpγ
  obtain ⟨σ, hσ, hinside, houtside⟩ := windingNumber_pm_one_of_jordan hb hΩ hLip hpγ
    hinj him (isConnected_compl_closure_of_frontier hb hΩ hfc)
  have hσC : (σ : ℂ) ≠ 0 := by rcases hσ with hσ | hσ <;> simp [hσ]
  have hA : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  let a : ℂ := (2 * Real.pi * Complex.I) * (σ : ℂ)
  let N : ℂ → ℂ := nearestPhysicalBoundaryDensity γ hγ.continuous K
  let R : ℂ → ℂ := physicalNearestCauchyCommutator γ hγ.continuous K
  let G : ℂ → ℂ := fun w => if w ∈ Ω then physicalWeightedCauchy γ K w / a else N w
  have hΩo : IsOpen Ω := hΩ.1.1
  have hav_not_front {w : ℂ} (hw : w ∉ frontier Ω) :
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), γ θ ≠ w :=
    fun θ hθ heq => hw (him ▸ heq ▸ mem_image_of_mem γ hθ)
  have hav (w : ℂ) (hw : w ∈ Ω) : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), γ θ ≠ w :=
    hav_not_front fun hfront => (hΩo.frontier_eq ▸ hfront).2 hw
  have hdiff (w : ℂ) (hw : w ∈ Ω) : DifferentiableAt ℂ G w := by
    refine ((physicalWeightedCauchy_hasDerivAt γ K hγ hK (hav w hw)).differentiableAt.div_const
      a).congr_of_eventuallyEq ?_
    filter_upwards [hΩo.mem_nhds hw] with z hz
    simp only [G, if_pos hz]
  have htrace (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi)) : G (γ θ) = K θ := by
    have hp : γ θ ∈ frontier Ω := him ▸ mem_image_of_mem γ hθ
    simp only [G, if_neg ((hΩo.frontier_eq ▸ hp).2)]
    refine sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _)))
    simpa only [sub_self, norm_zero, mul_zero] using
      nearestPhysicalBoundaryDensity_norm_sub_le γ hγ.continuous K hL hchord (γ θ) θ hθ
  refine ⟨G, ⟨fun w hw => (hdiff w hw).differentiableWithinAt, ?_⟩, htrace⟩
  intro p hpcl
  by_cases hpΩ : p ∈ Ω
  · exact (hdiff p hpΩ).continuousAt.continuousWithinAt
  · have hpfront : p ∈ frontier Ω := hΩo.frontier_eq.symm ▸ ⟨hpcl, hpΩ⟩
    obtain ⟨t, ht, rfl⟩ : ∃ t ∈ Ico (0 : ℝ) (2 * Real.pi), γ t = p := by
      obtain ⟨t, ht, heq⟩ := him ▸ hpfront
      by_cases htL : t = 2 * Real.pi
      · exact ⟨0, ⟨le_rfl, Real.two_pi_pos⟩, by rw [← heq, htL]; simpa using (hpγ 0).symm⟩
      · exact ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 htL⟩, heq⟩
    have hN := nearestPhysicalBoundaryDensity_tendsto γ hγ.continuous K hL hchord
      t (Ico_subset_Icc_self ht)
    have hR : Tendsto R (𝓝 (γ t)) (𝓝 0) := by
      obtain ⟨V, B, _, hpV, _, hBE, _, hcl⟩ := exists_exterior_box hΩ hpfront
      haveI : (𝓝[(closure Ω)ᶜ] (γ t)).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (closure_mono hBE (hcl (γ t) ⟨hpfront, hpV⟩))
      have hlim := physicalNearestCauchyCommutator_tendsto γ hγ K hK hL hchord hinj t ht
      have hout : Tendsto R (𝓝[(closure Ω)ᶜ] (γ t)) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with w hw
        have heq := physicalWeightedCauchy_eq_nearestCommutator_add_winding γ hγ K hK w
          (hav_not_front fun hf => hw (frontier_subset_closure hf))
        rw [hzero w hw, houtside w hw, mul_zero, add_zero] at heq
        exact heq
      rwa [tendsto_nhds_unique (hlim.mono_left nhdsWithin_le_nhds) hout] at hlim
    have haux : Tendsto (fun w : ℂ => R w / a + N w) (𝓝 (γ t)) (𝓝 (K t)) := by
      simpa only [zero_div, zero_add] using (hR.div_const a).add hN
    have hf : Tendsto (fun w : ℂ => physicalWeightedCauchy γ K w / a)
        (𝓝[closure Ω ∩ Ω] (γ t)) (𝓝 (K t)) := by
      refine Tendsto.congr' ?_ (haux.mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [physicalWeightedCauchy_eq_nearestCommutator_add_winding γ hγ K hK w (hav w hw.2),
        hinside w hw.2]
      dsimp only [R, N, a]; field_simp [hA, hσC]
    change Tendsto G (𝓝[closure Ω] (γ t)) (𝓝 (G (γ t)))
    rw [htrace t (Ico_subset_Icc_self ht)]
    exact hf.if_nhdsWithin (p := fun w => w ∈ Ω) (hN.mono_left nhdsWithin_le_nhds)

/-! ## Physical moment Hardy criterion for `L²` and continuous densities -/

private theorem fourierCoeffOn_congr_Icc {f g : ℝ → ℂ}
    (h : EqOn f g (Icc 0 (2 * Real.pi))) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos f n = fourierCoeffOn Real.two_pi_pos g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le Real.two_pi_pos.le] at hθ
  simp only [h hθ]

private theorem fourierCoeffOn_conj_eq (f : ℝ → ℂ) (m : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ => conj (f θ)) m =
      conj (fourierCoeffOn Real.two_pi_pos f (-m)) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1; rw [← intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [smul_eq_mul, map_mul, neg_neg]; congr 1
  simpa only [fourier_coe_apply, sub_zero] using
    (fourier_neg (n := m) (x := (θ : AddCircle (2 * Real.pi))))

private theorem strictNegative_conj_deriv_mul_of_primitive_nonpositive
    {γ g : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * g θ) = 0)
    (hK : IsNonpositiveFourierSupport
      (fourierCoeffOn Real.two_pi_pos (physicalMomentPrimitive γ g))) :
    IsStrictNegativeFourierSupport
      (fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv γ θ) * g θ)) := fun n hn => by
  have hν_mem : MemLp (fun θ => conj (deriv γ θ) * g θ) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    continuous_mul_memLp_boundary (Complex.continuous_conj.comp hγ.continuous_deriv_one) hg
  have hν_int : IntervalIntegrable (fun θ => conj (deriv γ θ) * g θ) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
      (hν_mem.integrable (by norm_num))
  have hKAC : AbsolutelyContinuousOnInterval (physicalMomentPrimitive γ g) 0 (2 * Real.pi) :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hν_int
      (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  rw [fourierCoeffOn_of_ac_ae_hasDerivAt hKAC hν_mem
    (ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hν_int)
    (by rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ g hmom0]) n]
  by_cases hn0 : n = 0
  · subst n; simp
  · rw [hK n (by omega), mul_zero]

private theorem nonpositive_of_strictNegative_conj_deriv_mul
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    {g : ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hneg : IsStrictNegativeFourierSupport (fourierCoeffOn Real.two_pi_pos
      (fun θ => conj (deriv (physicalCircleTrace F) θ) * g θ))) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos g) := by
  let q : ℂ → ℂ := fun z => (fderiv ℝ F z 1)⁻¹
  have hq_cd : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ (⊤ : ℕ∞) q z := fun z hz =>
    ((((hFs.fderiv_of_isOpen isOpen_ball (by simp)).clm_apply contDiffOn_const).contDiffAt
      (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).inv (hnz z hz))
  have hq_hol : DifferentiableOn ℂ q (ball (0 : ℂ) 1) := by
    have hdF : DifferentiableOn ℂ (fun z => fderiv ℝ F z 1) (ball (0 : ℂ) 1) :=
      (hhol.deriv isOpen_ball).congr fun z hz => by
        rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
        change fderiv ℂ F z 1 = _
        rw [fderiv_eq_deriv_mul, mul_one]
    exact hdF.inv fun z hz => hnz z (ball_subset_closedBall hz)
  have hq : DiffContOnCl ℂ q (ball (0 : ℂ) 1) :=
    DiffContOnCl.mk_ball hq_hol fun z hz => (hq_cd z hz).continuousAt.continuousWithinAt
  let recCoeff : ℝ → ℂ := fun θ => Complex.I * (circleMap 0 1 θ * conj (q (circleMap 0 1 θ)))
  have hrec_per : Function.Periodic recCoeff (2 * Real.pi) := fun θ => by
    dsimp only [recCoeff]; rw [(periodic_circleMap 0 1) θ]
  have hrec_cd : ContDiff ℝ 1 recCoeff := by
    have hqc : ContDiff ℝ 1 (fun θ => q (circleMap 0 1 θ)) :=
      contDiff_iff_contDiffAt.mpr fun θ =>
        ((hq_cd _ (circleMap_mem_closedBall 0 (by norm_num) θ)).of_le
          (WithTop.coe_le_coe.mpr le_top)).comp θ (contDiff_circleMap 0 1).contDiffAt
    exact contDiff_const.mul ((contDiff_circleMap 0 1).mul (Complex.conjCLE.contDiff.comp hqc))
  let A : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIoc (2 * Real.pi) 0 recCoeff,
      AddCircle.liftIoc_zero_continuous
        (by simpa only [zero_add] using (hrec_per 0).symm) hrec_cd.continuous.continuousOn⟩
  have hA_four : fourierCoeff A = fourierCoeffOn Real.two_pi_pos recCoeff :=
    funext fun n => by simp only [A, ContinuousMap.coe_mk, fourierCoeff_liftIoc_eq, zero_add]
  have hsA : Summable (fourierCoeff A) := by
    rw [hA_four]
    have hreg := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
      (c1_absolutelyContinuousOnInterval hrec_cd)
      (continuousOn_memLp_boundary hrec_cd.continuous_deriv_one.continuousOn)
      (Eventually.of_forall fun θ _ => (hrec_cd.differentiable_one θ).hasDerivAt)
      (by simpa only [zero_add] using (hrec_per 0).symm)
    exact Summable.of_norm ((sq_tsum_norm_le (s := 0) (by norm_num)
      (by simpa only [zero_add] using hreg)).1)
  have hA_hi : ∀ k : ℤ, 1 < k → fourierCoeff A k = 0 := fun k hk => by
    rw [congrFun hA_four k]
    have hcmul (f : ℝ → ℂ) (m : ℤ) :
        fourierCoeffOn Real.two_pi_pos (fun θ => circleMap 0 1 θ * f θ) m =
          fourierCoeffOn Real.two_pi_pos f (m - 1) := by
      rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
      simp only [sub_zero, Complex.real_smul, smul_eq_mul]
      refine congrArg _ (intervalIntegral.integral_congr fun θ _ => ?_)
      have h1 : fourier (T := 2 * Real.pi - 0) 1 (θ : AddCircle (2 * Real.pi - 0)) =
          circleMap 0 1 θ := by
        rw [fourier_coe_apply, circleMap_zero]; norm_num [Real.pi_ne_zero]
        congr 1; field_simp [Real.pi_ne_zero]
      change fourier (T := 2 * Real.pi - 0) (-m) (θ : AddCircle (2 * Real.pi - 0)) *
          (circleMap 0 1 θ * f θ) =
        fourier (T := 2 * Real.pi - 0) (-(m - 1)) (θ : AddCircle (2 * Real.pi - 0)) * f θ
      rw [← h1, ← mul_assoc, ← fourier_add, show -m + 1 = -(m - 1) by omega]
    dsimp only [recCoeff]
    rw [fourierCoeffOn.const_mul, hcmul, fourierCoeffOn_conj_eq]
    change Complex.I * conj (fourierCoeffOn Real.two_pi_pos (physicalCircleTrace q) (-(k - 1))) = 0
    rw [physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg q hq (by omega), map_zero, mul_zero]
  let γ := physicalCircleTrace F
  have hγ : ContDiff ℝ 1 γ :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hν_mem : MemLp (fun θ => conj (deriv γ θ) * g θ) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    continuous_mul_memLp_boundary (Complex.continuous_conj.comp hγ.continuous_deriv_one) hg
  let v : BoundaryL2 := hν_mem.toLp (fun θ => conj (deriv γ θ) * g θ)
  have hrecover : boundaryContinuousMultiplier A v = hg.toLp g := Lp.ext <| by
    filter_upwards [boundaryContinuousMultiplier_ae A v, hν_mem.coeFn_toLp, hg.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with θ hmul hv hgθ hθ
    rw [hmul, hv, hgθ, show A (θ : AddCircle (2 * Real.pi)) = recCoeff θ by
      dsimp [A]; exact AddCircle.liftIoc_zero_coe_apply hθ]
    let z := circleMap 0 1 θ
    let D := fderiv ℝ F z 1
    have hcD : conj D ≠ 0 := star_ne_zero.mpr (hnz z (circleMap_mem_closedBall 0 (by norm_num) θ))
    have hz : z * conj z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, show ‖z‖ = 1 by simp [z, norm_circleMap_zero]]
      norm_num
    dsimp only [γ, recCoeff, q]
    rw [localConformal_circleTrace_deriv hR F hFs hhol]
    change (Complex.I * (z * conj D⁻¹)) * (conj (D * (z * Complex.I)) * g θ) = g θ
    simp only [map_inv₀, map_mul, Complex.conj_I]
    calc _ = ((Complex.I * -Complex.I) * (z * conj z) * (conj D * (conj D)⁻¹)) * g θ := by ring
      _ = g θ := by rw [hz, mul_inv_cancel₀ hcD]; simp
  intro n hn
  have hnBF : boundaryFourier (hg.toLp g) n = 0 := by
    rw [← hrecover, boundaryFourier_continuousMultiplier A hsA]
    unfold seqConv
    refine (tsum_congr fun k => ?_).trans tsum_zero
    by_cases hk : 1 < k
    · rw [hA_hi k hk, zero_mul]
    · rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hν_mem.coeFn_toLp,
        hneg (n - k) (by omega), mul_zero, mul_zero]
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hg.coeFn_toLp] at hnBF
  exact (mul_eq_zero.mp hnBF).resolve_left
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.two_pi_pos).ne')

/-- All centered physical antiholomorphic moments of an `L²` boundary density `H`
force `fourierCoeffOn Real.two_pi_pos H` to have nonpositive support. -/
theorem localConformal_physicalMoments_nonpositive_of_memLp
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball (0 : ℂ) 1 = Ω)
    (H : ℝ → ℂ) (hH : MemLp H 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  let γ := physicalCircleTrace F
  have hγ : ContDiff ℝ 1 γ :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpγ : Function.Periodic γ (2 * Real.pi) := physicalCircleTrace_periodic F
  have hmom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0 := by
    simpa only [pow_zero, mul_one] using hmom 0
  have hν_mem : MemLp (fun θ => conj (deriv γ θ) * H θ) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    continuous_mul_memLp_boundary (Complex.continuous_conj.comp hγ.continuous_deriv_one) hH
  have hK1_ac : AbsolutelyContinuousOnInterval (physicalMomentPrimitive γ H) 0 (2 * Real.pi) :=
    absolutelyContinuousOnInterval_intervalIntegral_banach
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
        (hν_mem.integrable (by norm_num)))
      (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  let Kp : ℝ → ℂ := fun θ =>
    AddCircle.liftIco (2 * Real.pi) 0 (physicalMomentPrimitive γ H) (θ : AddCircle (2 * Real.pi))
  have hKp_eqOn : EqOn Kp (physicalMomentPrimitive γ H) (Icc 0 (2 * Real.pi)) := fun θ hθ => by
    by_cases hθL : θ = 2 * Real.pi
    · subst θ
      have hlift : AddCircle.liftIco (2 * Real.pi) 0 (physicalMomentPrimitive γ H)
          (0 : AddCircle (2 * Real.pi)) = physicalMomentPrimitive γ H 0 :=
        AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
      dsimp only [Kp]
      rw [AddCircle.coe_period, hlift, physicalMomentPrimitive_zero,
        physicalMomentPrimitive_endpoint γ H hmom0]
    · exact AddCircle.liftIco_zero_coe_apply ⟨hθ.1, lt_of_le_of_ne hθ.2 hθL⟩
  have hKp_cont : Continuous Kp :=
    (AddCircle.liftIco_zero_continuous (f := physicalMomentPrimitive γ H)
      (by rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ H hmom0])
      (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hK1_ac.continuousOn)).comp
      (AddCircle.continuous_mk' _)
  have hKp_per : Function.Periodic Kp (2 * Real.pi) := fun θ => by
    dsimp only [Kp]; rw [AddCircle.coe_add_period]
  have hKp_mom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv γ θ) * Kp θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0 := fun m => by
    refine (intervalIntegral.integral_congr fun θ hθ => ?_).trans
      (physicalMomentPrimitive_moments_of_memLp γ H hγ hH hmom m)
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    simp only [hKp_eqOn hθ]
  let K₂ := physicalMomentPrimitive γ Kp
  have hK₂ : ContDiff ℝ 1 K₂ := contDiff_physicalMomentPrimitive γ Kp hγ hKp_cont
  have hKp_mom0 : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * Kp θ) = 0 := by
    simpa only [pow_zero, mul_one] using hKp_mom 0
  have hpK₂ : Function.Periodic K₂ (2 * Real.pi) :=
    physicalMomentPrimitive_periodic γ Kp hγ hKp_cont hpγ hKp_per hKp_mom0
  have him : γ '' Icc (0 : ℝ) (2 * Real.pi) = frontier Ω := by
    simpa only [himage] using
      localConformal_circleTrace_image_frontier hR F hFs hinj (himage.symm ▸ hΩ.1.1)
  have hfc : IsPreconnected (frontier Ω) :=
    him ▸ isPreconnected_Icc.image γ hγ.continuous.continuousOn
  obtain ⟨L, hL, hchord⟩ :=
    exists_localConformal_boundaryDensity_chord_bound_of_nonzeroDifferential
      hR F hFs hhol hinj hnz K₂ hK₂ hpK₂
  obtain ⟨G, hG, htrace⟩ := exists_physicalCauchy_boundary_extension hb hΩ hfc γ hγ hpγ
    (physicalCircleTrace_injOn_of_closedDisk_inj F hinj) him
    (fun θ => conj (K₂ θ)) (Complex.continuous_conj.comp hK₂.continuous) hL
    (fun θ τ => by rw [← map_sub, Complex.norm_conj]; exact hchord θ τ)
    (physicalWeightedCauchy_conj_eq_zero_on_exterior_of_moments hb hΩ hfc γ K₂ hγ
      hK₂.continuous him (physicalMomentPrimitive_moments_of_memLp γ Kp hγ
        (continuousOn_memLp_boundary hKp_cont.continuousOn) hKp_mom))
  have hP : DiffContOnCl ℂ (G ∘ F) (ball (0 : ℂ) 1) :=
    hG.comp (DiffContOnCl.mk_ball hhol (hFs.continuousOn.mono (closedBall_subset_ball hR)))
      fun z hz => himage ▸ mem_image_of_mem F hz
  have hK₂_nonpos : IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos K₂) := fun n hn => by
    have hc := fourierCoeffOn_conj_eq K₂ (-n)
    rw [neg_neg] at hc
    have ht : fourierCoeffOn Real.two_pi_pos (fun θ => conj (K₂ θ)) (-n) =
        fourierCoeffOn Real.two_pi_pos (physicalCircleTrace (G ∘ F)) (-n) :=
      fourierCoeffOn_congr_Icc (fun θ hθ => (htrace θ hθ).symm) (-n)
    have hz := congrArg conj (hc.symm.trans (ht.trans
      (physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg (G ∘ F) hP (by omega))))
    simpa only [Complex.conj_conj, map_zero] using hz
  have hKp_nonpos : IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos Kp) :=
    nonpositive_of_strictNegative_conj_deriv_mul hR F hFs hhol hnz
      (continuousOn_memLp_boundary hKp_cont.continuousOn)
      (strictNegative_conj_deriv_mul_of_primitive_nonpositive hγ
        (continuousOn_memLp_boundary hKp_cont.continuousOn) hKp_mom0 hK₂_nonpos)
  have hK₁_nonpos : IsNonpositiveFourierSupport
      (fourierCoeffOn Real.two_pi_pos (physicalMomentPrimitive γ H)) := fun n hn => by
    rw [← fourierCoeffOn_congr_Icc hKp_eqOn n]
    exact hKp_nonpos n hn
  exact nonpositive_of_strictNegative_conj_deriv_mul hR F hFs hhol hnz hH
    (strictNegative_conj_deriv_mul_of_primitive_nonpositive hγ hH hmom0 hK₁_nonpos)

/-- Continuous periodic specialization of `localConformal_physicalMoments_nonpositive_of_memLp`. -/
theorem localConformal_physicalMoments_nonpositive
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball (0 : ℂ) 1 = Ω)
    (H : ℝ → ℂ) (hH : Continuous H)
    (_hpH : Function.Periodic H (2 * Real.pi))
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) :=
  localConformal_physicalMoments_nonpositive_of_memLp hb hΩ hR F hFs hhol hinj hnz himage
    H (continuousOn_memLp_boundary hH.continuousOn) hmom

end PolyaNeumann

end
