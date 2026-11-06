module

public import RequestProject.PlanarTypes
public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.NeumannRegularSolutionAtReference
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import RequestProject.NeumannTraceInjective
public import RequestProject.NeumannResonanceDimension
public import RequestProject.NeumannConstantTrace
public import RequestProject.NeumannHerglotzBoundary
public import Mathlib.Tactic.Ring
public import RequestProject.LocalConformalHerglotz
public import RequestProject.HerglotzReduction
public import RequestProject.ObservationLp
public import RequestProject.PhysicalHardySupport
public import RequestProject.KernelFourierAction
public import RequestProject.NormalizedPeriodicRegular
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Genuine regular Herglotz and observation identities at resonance

The regular resolvent is the original Neumann complement resolvent. On
an actual Herglotz conormal its trace is the Herglotz trace with exactly
the original resonant projection removed. The actual corrected periodic
expression is consequently an observation of a vector orthogonal to the
cut, minus twice that resonant trace. Compatibility and projected
observation nullity therefore annihilate this expression.

The ordinary boundary identity below uses the supplied physical boundary
parameter. The conformal identity uses the proved Jacobian load, rather
than identifying a variable-speed circle parameter with an arclength
parameter. No density of Herglotz conormals is assumed or asserted here.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Metric Real Filter
open scoped Real InnerProductSpace



/-- The actual corrected initial Herglotz vector. Both the initial jet
and the finite cut correction retain their original normalizations. -/
def regularHerglotzObservationVector {γ : ComplexCurve} (E : ℝ)
    (W : ℝ → ComplexEnd Ell2) {a : ComplexCurve} (ha : IsDirDensity a) : Ell2 :=
  (Real.sqrt 2 : ℂ) •
      (herglotzVec ha (Real.sqrt E) (γ 0) +
        ContinuousLinearMap.adjoint (W circlePeriod)
          (herglotzVec ha (Real.sqrt E) (γ 0))) +
    cutBE W (observationAdj W (herglotzConormal (Real.sqrt E) a γ))

section
variable {γ } {K } (hK : LipschitzWith K γ) (hclosed : γ circlePeriod = γ 0) {E } {W } (hW : IsTransport γ E W)
include γ K hK hclosed E W hW

/-- The corrected expression of a genuine wave is its actual corrected
observation, before the genuine resonant trace is removed. -/
theorem periodicP_herglotz_eq_regularObservation
     (ha : IsDirDensity a)  (hθ : θ ∈ boundaryInterval) :
    periodicP W (fun s => herglotzWave (Real.sqrt E) a (γ s))
        (herglotzConormal (Real.sqrt E) a γ) θ =
      observation W (regularHerglotzObservationVector (γ := γ) E W ha) θ := by
  rw [periodicP, periodicA_herglotz_eq_observation hK hclosed hW ha hθ]
  simp  [regularHerglotzObservationVector, cutBE, observation, inner_add_right]

/-- The true endpoint cancellation places the corrected Herglotz vector
in the orthogonal complement of the actual cut direction. -/
theorem regularHerglotzObservationVector_inner_cut_eq_zero
    (hc : cutC (W circlePeriod) (basisVec 0) ≠ 0)
     (ha : IsDirDensity a) :
    ⟪cutC (W circlePeriod) (basisVec 0),
      regularHerglotzObservationVector (γ := γ) E W ha⟫_ℂ = 0 := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  have hn : (fun s => herglotzWave (Real.sqrt E) a (γ s)) circlePeriod =
      (fun s => herglotzWave (Real.sqrt E) a (γ s)) 0 := by
    simp_all
  have hp := periodicP_periodic (n := fun s => herglotzWave (Real.sqrt E) a (γ s))
    hK hW hc hn hgm hgB
  rw [periodicP_herglotz_eq_regularObservation hK hclosed hW ha
        ⟨two_pi_pos.le, le_rfl⟩,
    periodicP_herglotz_eq_regularObservation hK hclosed hW ha
        ⟨le_rfl, two_pi_pos.le⟩] at hp
  rw [← observation_jump hW]
  exact sub_eq_zero.mpr hp

theorem regularHerglotzObservationVector_cutProj
    (hc : cutC (W circlePeriod) (basisVec 0) ≠ 0)
     (ha : IsDirDensity a) :
    cutProj (cutC (W circlePeriod) (basisVec 0))
        (regularHerglotzObservationVector (γ := γ) E W ha) =
      regularHerglotzObservationVector (γ := γ) E W ha := by
  rw [cutProj_eq_starProjection, Submodule.starProjection_eq_self_iff,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact regularHerglotzObservationVector_inner_cut_eq_zero hK hclosed hW hc ha

end


private theorem regular_boundary_sub_ae (u v : BoundaryL2) 
    (hf : (u : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f) :
    ((u - v : BoundaryL2) : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval]
      fun θ => f θ - v θ := by
  filter_upwards [Lp.coeFn_sub u v, hf] with θ hs hw
  rw [hs, Pi.sub_apply, hw]

private theorem regular_observation_sub_ae {γ : ComplexCurve} {K : NNReal}
    (hK : LipschitzWith K γ) {E : ℝ} {W : ℝ → ComplexEnd Ell2}
    (hW : IsTransport γ E W) (z : Ell2) (r : BoundaryL2)
    (hz : cutProj (cutC (W circlePeriod) (basisVec 0)) z = z) :
    ((projectedObservationBoundary hK hW z - (2 : ℂ) • r : BoundaryL2) : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        fun θ => observation W z θ - 2 * r θ := by
  filter_upwards [Lp.coeFn_sub (projectedObservationBoundary hK hW z) ((2 : ℂ) • r),
    Lp.coeFn_smul (2 : ℂ) r, projectedObservationBoundary_coe hK hW z]
      with θ hs h2 ho
  rw [hs, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, ho,
    ← observation_cutProj_eq, hz]

private theorem regular_boundary_toLp_eq 
    (hf : MemLp f 2 (volume.restrict boundaryHalfOpenInterval)) (u : BoundaryL2)
    (hu : (u : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f) :
    hf.toLp f = u := by
  apply Lp.ext
  exact hf.coeFn_toLp.trans hu.symm


/-- The positive Jacobian makes the supplied trace reparametrization
preserve null sets on the actual cut. This is proved by change of
variables, even for a property with no chosen measurable representative. -/
theorem isC1TraceReparam_ae_comp  
    (hτ : IsC1TraceReparam τ c) {p : ℝ → Prop}
    (hp : ∀ᵐ s ∂volume.restrict boundaryHalfOpenInterval, p s) :
    ∀ᵐ θ ∂volume.restrict boundaryHalfOpenInterval, p (τ θ) := by
  classical
  let q : RealMap := fun s => if p s then 0 else 1
  have hqzero : q =ᵐ[volume.restrict boundaryHalfOpenInterval] 0 := by
    filter_upwards [hp] with s hs
    simp  [q, if_pos hs]
  have hq  :=
    (MeasureTheory.integrable_zero ℝ ℝ (volume.restrict boundaryHalfOpenInterval)).congr hqzero.symm
  have himage : τ '' boundaryInterval = boundaryInterval := by
    simpa only [hτ.zero, hτ.endpoint] using
      hτ.continuous.continuousOn.image_Icc_of_monotoneOn two_pi_pos.le
        (hτ.monotone.monotoneOn _)
  have hq'  :=
    (integrableOn_Icc_iff_integrableOn_Ioc (f := q) (by finiteness)).mpr hq
  have hj  :=
    (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Icc
      (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
      (hτ.monotone.monotoneOn boundaryInterval) q).mp
        (by simpa only [himage] using hq')
  have hj' : IntegrableOn (fun θ => deriv τ θ * q (τ θ)) boundaryHalfOpenInterval := by
    simpa only [smul_eq_mul] using
      (integrableOn_Icc_iff_integrableOn_Ioc
        (f := fun θ => deriv τ θ • q (τ θ)) (by finiteness)).mp hj
  have hchange := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Icc
    (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
    (hτ.monotone.monotoneOn boundaryInterval) q
  have hz : (∫ θ in boundaryHalfOpenInterval, deriv τ θ * q (τ θ)) = 0 := by
    have heq : (∫ θ in boundaryHalfOpenInterval, deriv τ θ * q (τ θ)) =
        ∫ s in boundaryHalfOpenInterval, q s := by
      simpa only [himage, integral_Icc_eq_integral_Ioc, smul_eq_mul] using hchange.symm
    rw [heq, integral_congr_ae hqzero]
    simp only [Pi.zero_apply, integral_zero]
  have hnonneg : 0 ≤ᵐ[volume.restrict boundaryHalfOpenInterval]
      (fun θ => deriv τ θ * q (τ θ)) := Eventually.of_forall fun θ =>
    mul_nonneg hτ.monotone.deriv_nonneg (by simp only [q]; split_ifs <;> norm_num)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hj').mp hz
  have hlo := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hτ.lower_ae
  filter_upwards [hae, hlo] with θ hzero hlower
  by_contra hbad
  have hd  := hτ.lower_pos.trans_le hlower
  measurability

/-- The actual conormal derivative obeys the Jacobian law a.e. for the
supplied C1 change of parameter. The original boundary curve only needs
to be Lipschitz; Rademacher and the true null-set transport supply its
derivative at the composed points. -/
theorem herglotzConormal_traceReparam_ae  
    (hK : LipschitzWith K γ)  
    (hτ : IsC1TraceReparam τ c)  (ha : IsDirDensity a) k :
    herglotzConormal k a (γ ∘ τ)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        (fun θ => deriv τ θ • herglotzConormal k a γ (τ θ)) := by
  have hdiff := isC1TraceReparam_ae_comp hτ
    (ae_restrict_of_ae (hK.ae_differentiableAt (μ := volume)))
  filter_upwards [hdiff] with θ hγdiff
  have hd := hγdiff.hasDerivAt.scomp θ (hτ.contDiff.differentiable_one θ).hasDerivAt
  rw [herglotzConormal_eq ha.intervalIntegrable, hd.deriv,
    herglotzConormal_eq ha.intervalIntegrable]
  simp  
  ring

/-- Actual variable-speed coordinate conormal, as an ordinary L2 class. -/
def localConformalHerglotzCoordinateLoad F {L }
    (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {a } ha k  :=
  (memLp_herglotzConormal ha k hΓLip).toLp
    (herglotzConormal k a (physicalCircleTrace F))

theorem localConformalHerglotzCoordinateLoad_ae F 
    (hΓLip : LipschitzWith L (physicalCircleTrace F))
     (ha : IsDirDensity a) k :
    (localConformalHerglotzCoordinateLoad F hΓLip ha k : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        herglotzConormal k a (physicalCircleTrace F) :=
  (memLp_herglotzConormal ha k hΓLip).coeFn_toLp

section ConformalCoordinates

variable {R C } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    {γ } (hγ : IsBoundaryParam (F '' unitDisk) γ)
    {τ } {c } (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCircleMap θ) = γ (τ θ))

local notation "ΩF" => F '' unitDisk
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "TF" => localConformalDiskH1Trace hR F hFs hL

include hhol hinj hC hcoord

section
variable {E₀ : ℝ} (hE₀ : 0 ≤ E₀) {a } (ha : IsDirDensity a)
include E₀ hE₀ a ha

/-- The actual H1 regular solution itself is the wave minus its true
resonant component. This is stronger than a Fourier trace equality. -/
theorem localConformal_regularHerglotzH1_eq_sub_resonant :
    h1RegularResolvent ΩF E₀ E₀
        (ContinuousLinearMap.adjoint QF
          (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀)))) =
      herglotzWaveH1 hb ha (Real.sqrt E₀) -
        (h1ResonantSpace ΩF E₀).starProjection (herglotzWaveH1 hb ha (Real.sqrt E₀)) := by
  have hu := (isNormalizedNeumannSolution_iff QF E₀ _ _).mp
    (localConformalHerglotz_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj
      hC hγ hτ hcoord hE₀ ha)
  rw [← hu, h1RegularResolvent_form_at_reference hb hL hE₀,
    Submodule.starProjection_orthogonal_val]

/-- The ordinary conformal trace retains the same exact removed
resonant component, with no extra square-root Fourier scale. -/
theorem localConformal_regularHerglotz_coordinate_trace_eq :
    TF (h1RegularResolvent ΩF E₀ E₀
      (ContinuousLinearMap.adjoint QF
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))))) =
      TF (herglotzWaveH1 hb ha (Real.sqrt E₀)) -
        TF ((h1ResonantSpace ΩF E₀).starProjection (herglotzWaveH1 hb ha (Real.sqrt E₀))) := by
  rw [localConformal_regularHerglotzH1_eq_sub_resonant hR F hFs hb hL hhol hinj
    hC hγ hτ hcoord hE₀ ha, map_sub]

end


include hγ hτ in
/-- The genuine Herglotz H1 vector has its actual variable-speed circle
trace. A true smooth cutoff and the proved trace identity establish it. -/
theorem localConformalHerglotz_coordinate_trace_ae
     (ha : IsDirDensity a) k :
    (TF (herglotzWaveH1 hb ha k) : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        (fun θ => herglotzWave k a (physicalCircleTrace F θ)) := by
  obtain ⟨f, hfu, hfγ⟩ := exists_smoothTraceTest_herglotz hb hL hγ ha k
  rw [← hfu]
  filter_upwards [localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f,
    ae_restrict_mem measurableSet_Ioc] with θ ht hθ
  rw [ht, hcoord, hfγ _ (hτ.mapsTo (Ioc_subset_Icc_self hθ))]
  simpa  [physicalCircleTrace, hcoord] using (herglotzWave_eq k a (γ (τ θ))).symm

omit hhol hinj hC in
/-- The constructed physical Jacobian load equals the actual conormal
on the genuine variable-speed conformal circle. No load equality is an
input to this theorem. -/
theorem localConformalHerglotz_traceReparamConormal_eq_coordinateLoad
     (hΓLip : LipschitzWith L (physicalCircleTrace F))
     (ha : IsDirDensity a) k :
    traceReparamConormalL2 hτ (herglotzConormalL2 hγ ha k) =
      localConformalHerglotzCoordinateLoad F hΓLip ha k := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hΓ : physicalCircleTrace F = γ ∘ τ := by
    funext θ
    exact hcoord θ
  have hrep := isC1TraceReparam_ae_comp hτ (herglotzConormalL2_ae hγ ha k)
  have hc := herglotzConormal_traceReparam_ae hKγ hτ ha k
  rw [← hΓ] at hc
  apply Lp.ext
  filter_upwards [traceReparamConormalL2_ae hτ (herglotzConormalL2 hγ ha k), hrep, hc,
    localConformalHerglotzCoordinateLoad_ae F hΓLip ha k] with θ ht hr hc hg
  rw [ht, hr, hg]
  exact hc.symm

omit hhol hinj hC in
/-- In particular the normalized weak load is exactly half smoothing of
the actual coordinate conormal's unitary Fourier coefficients. -/
theorem localConformalHerglotzBoundaryLoad_eq_coordinateLoad
     (hΓLip : LipschitzWith L (physicalCircleTrace F))
     (ha : IsDirDensity a) k :
    localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha k) =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
        (boundaryFourier (localConformalHerglotzCoordinateLoad F hΓLip ha k)) := by
  unfold localConformalBoundaryLoad
  rw [localConformalHerglotz_traceReparamConormal_eq_coordinateLoad F hγ hτ hcoord hΓLip ha k]

/-- The actual regular coordinate trace is used with the true
variable-speed Herglotz conormal. The variational input is explicitly the
proved Jacobian transform of the physical load. -/
def localConformalRegularPeriodicHerglotzExpression (E₀ : ℝ)
    (W : ℝ → ComplexEnd Ell2) {a : ComplexCurve} (ha : IsDirDensity a) : ComplexCurve :=
  periodicP W
    (TF (h1RegularResolvent ΩF E₀ E₀
      (ContinuousLinearMap.adjoint QF
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))))) : ComplexCurve)
    (herglotzConormal (Real.sqrt E₀) a (physicalCircleTrace F))

/-- Exact regular periodic identity in the genuine conformal circle.
Its variable speed does not enter an IsBoundaryParam assumption. -/
theorem localConformalRegularPeriodicHerglotzExpression_ae
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : ℝ → ComplexEnd Ell2} (hW : IsTransport (physicalCircleTrace F) E₀ W)
    {a : ComplexCurve} (ha : IsDirDensity a) :
    localConformalRegularPeriodicHerglotzExpression hR F hFs hL hγ hτ E₀ W ha
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        (fun θ => observation W
            (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha) θ -
          2 * TF ((h1ResonantSpace ΩF E₀).starProjection
            (herglotzWaveH1 hb ha (Real.sqrt E₀))) θ) := by
  have hn :
      (TF (h1RegularResolvent ΩF E₀ E₀
        (ContinuousLinearMap.adjoint QF
          (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))))) : ComplexCurve)
        =ᵐ[volume.restrict boundaryHalfOpenInterval]
          (fun θ => herglotzWave (Real.sqrt E₀) a (physicalCircleTrace F θ) -
            TF ((h1ResonantSpace ΩF E₀).starProjection
              (herglotzWaveH1 hb ha (Real.sqrt E₀))) θ) := by
    rw [localConformal_regularHerglotz_coordinate_trace_eq hR F hFs hb hL hhol hinj
      hC hγ hτ hcoord hE₀ ha]
    exact regular_boundary_sub_ae _ _
      (localConformalHerglotz_coordinate_trace_ae hR F hFs hb hL hhol hinj hC hγ hτ
        hcoord ha (Real.sqrt E₀))
  have hclosed : physicalCircleTrace F circlePeriod = physicalCircleTrace F 0 := by
    simpa only [zero_add] using physicalCircleTrace_periodic F 0
  filter_upwards [hn, ae_restrict_mem measurableSet_Ioc] with θ hn hθ
  have hp := periodicP_herglotz_eq_regularObservation hΓLip hclosed hW ha
    (Ioc_subset_Icc_self hθ)
  simp  [localConformalRegularPeriodicHerglotzExpression, periodicP, periodicA, hn]
    at hp ⊢
  linear_combination hp

omit hhol hinj hC hcoord in
/-- The corrected observation vector in the conformal identity is
orthogonal to its true boundary-origin cut. -/
theorem localConformalRegularHerglotzObservationVector_cutProj
     (hΓLip : LipschitzWith L (physicalCircleTrace F))
     
    (hW : IsTransport (physicalCircleTrace F) E₀ W)
    (hc : cutC (W circlePeriod) (basisVec 0) ≠ 0)
     (ha : IsDirDensity a) :
    cutProj (cutC (W circlePeriod) (basisVec 0))
        (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha) =
      regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha := by
  exact regularHerglotzObservationVector_cutProj hΓLip
    (by simpa   using physicalCircleTrace_periodic F 0) hW hc ha

section CoordinatePairing

variable {L } (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {E₀ } (hE₀ : 0 ≤ E₀)
    {W } (hW : IsTransport (physicalCircleTrace F) E₀ W)
    (hc : cutC (W circlePeriod) (basisVec 0) ≠ 0)
    {a } (ha : IsDirDensity a)

local notation "zΓ" => regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha
local notation "rΓ" => TF (Submodule.starProjection (h1ResonantSpace ΩF E₀)
  (herglotzWaveH1 hb ha (Real.sqrt E₀)))

include hb hΓLip hE₀ hW hc in
theorem localConformalRegularPeriodicHerglotzExpression_memLp :
    MemLp (localConformalRegularPeriodicHerglotzExpression hR F hFs hL hγ hτ E₀ W ha)
      2 (volume.restrict boundaryHalfOpenInterval) := by
  have hz := localConformalRegularHerglotzObservationVector_cutProj F hΓLip hW hc ha
  have heq := regular_observation_sub_ae hΓLip hW zΓ rΓ hz
  exact (Lp.memLp (projectedObservationBoundary hΓLip hW zΓ - 2 • rΓ)).ae_eq
    (heq.trans (localConformalRegularPeriodicHerglotzExpression_ae hR F hFs hb hL hhol
      hinj hC hγ hτ hcoord hΓLip hE₀ hW ha).symm)

/-- The ordinary-coordinate L2 class of the actual regular periodic
expression on the genuine variable-speed circle. -/
def localConformalRegularPeriodicHerglotzBoundary  :=
  (localConformalRegularPeriodicHerglotzExpression_memLp hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord hΓLip hE₀ hW hc ha).toLp
    (localConformalRegularPeriodicHerglotzExpression hR F hFs hL hγ hτ E₀ W ha)

theorem localConformalRegularPeriodicHerglotzBoundary_eq :
    localConformalRegularPeriodicHerglotzBoundary hR F hFs hb hL hhol hinj hC
      hγ hτ hcoord hΓLip hE₀ hW hc ha =
        projectedObservationBoundary hΓLip hW zΓ - (2 : ℂ) • rΓ := by
  unfold localConformalRegularPeriodicHerglotzBoundary
  have hz := localConformalRegularHerglotzObservationVector_cutProj F hΓLip hW hc ha
  exact regular_boundary_toLp_eq _ _
    ((regular_observation_sub_ae hΓLip hW zΓ rΓ hz).trans
      (localConformalRegularPeriodicHerglotzExpression_ae hR F hFs hb hL hhol hinj hC
        hγ hτ hcoord hΓLip hE₀ hW ha).symm)

end CoordinatePairing

end ConformalCoordinates

/-! The following computation is on genuine coordinate integrals, with
ordinary measure. In particular it proves the zero Fourier row as well
as every nonzero row, for arbitrary integrable inputs. -/

private theorem regular_sawtooth_measurable :
    Measurable (Function.uncurry sawtoothKernel) := by
  unfold sawtoothKernel Function.uncurry
  fun_prop

private theorem regular_sawtooth_norm_le 
    (hθ : θ ∈ boundaryInterval) (hs : s ∈ boundaryInterval) :
    ‖sawtoothKernel θ s‖ ≤ 3 := by
  have hd : |θ - s| ≤ 2 * π := abs_le.mpr ⟨by linarith [hθ.1, hs.2],
    by linarith [hθ.2, hs.1]⟩
  have hdiv : |(θ - s) / π| ≤ 2 := by
    rw [abs_div, abs_of_pos pi_pos]
    exact (div_le_iff₀ pi_pos).mpr (by linarith)
  calc
    ‖sawtoothKernel θ s‖ ≤
        ‖Complex.I * (Real.sign (θ - s))‖ +
          ‖Complex.I * (((θ - s) / π : ℝ))‖ := by
      simpa  [sawtoothKernel] using
        (norm_sub_le (Complex.I * (Real.sign (θ - s)))
          (Complex.I * (((θ - s) / π))))
    _ = |Real.sign (θ - s)| + |(θ - s) / π| := by
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    _ ≤ 3 := by linarith [abs_real_sign_le (θ - s)]

private theorem regular_sawtooth_swap θ s :
    sawtoothKernel θ s = -sawtoothKernel s θ := by
  have hs : Real.sign (θ - s) = -Real.sign (s - θ) := by
    rw [← Real.sign_neg, neg_sub]
  simp  [sawtoothKernel, hs]
  ring

private theorem regular_kernel_mode_norm n θ :
    ‖kernelFourierMode n θ‖ = 1 := by
  rw [← fourier_two_pi_eq_kernelFourierMode]
  rw [fourier_apply]
  exact Circle.norm_coe _

private theorem regular_sawtooth_outer_mode n 
    (hs : s ∈ boundaryInterval) :
    (∫ θ in (0 : ℝ)..circlePeriod, kernelFourierMode (-n) θ * sawtoothKernel θ s) =
      (2 / (n : ℂ)) * kernelFourierMode (-n) s := by
  have heq : (fun θ => kernelFourierMode (-n) θ * sawtoothKernel θ s) =
      fun θ => -(sawtoothKernel s θ * kernelFourierMode (-n) θ) := by
    funext θ
    rw [regular_sawtooth_swap]
    ring
  rw [heq, intervalIntegral.integral_neg]
  by_cases hn : n = 0
  · subst n
    simp only [neg_zero, kernelFourierMode, Int.cast_zero, Complex.exp_zero, mul_one, div_zero, zero_mul]
    rw [integral_sawtoothKernel hs, neg_zero]
  · rw [show (∫ θ in (0 : ℝ)..circlePeriod,
        sawtoothKernel s θ * kernelFourierMode (-n) θ) =
        2 / ((-n : ℤ) : ℂ) * kernelFourierMode (-n) s from
        integral_sawtoothKernel_mul_exp hs (neg_ne_zero.mpr hn)]
    grind

section
variable {f : ComplexCurve} (hf : Integrable f (volume.restrict boundaryHalfOpenInterval))
include f hf

/-- The genuine sawtooth integral has multiplier `2/n` on every
Fourier coefficient of an arbitrary L1 input. At `n=0` the result is
exactly zero; the normalization remains `1/(2π)`. -/
theorem fourierCoeffOn_sawtoothAction n :
    fourierCoeffOn two_pi_pos
      (fun θ => ∫ s in (0 : ℝ)..circlePeriod, sawtoothKernel θ s * f s) n =
        (2 / (n : ℂ)) * fourierCoeffOn two_pi_pos f n := by
  let μ  := volume.restrict boundaryHalfOpenInterval
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      kernelFourierMode (-n) p.1 * sawtoothKernel p.1 p.2 * f p.2) (μ.prod μ) := by
    exact (((show Continuous (fun p : ℝ × ℝ => kernelFourierMode (-n) p.1) by
      unfold kernelFourierMode; fun_prop).measurable.aestronglyMeasurable.mul
      regular_sawtooth_measurable.aestronglyMeasurable).mul
      hf.aestronglyMeasurable.comp_snd)
  have hint : Integrable (fun p : ℝ × ℝ =>
      kernelFourierMode (-n) p.1 * sawtoothKernel p.1 p.2 * f p.2) (μ.prod μ) := by
    refine ((hf.norm.comp_snd μ).const_mul 3).mono' hm ?_
    have hae : ∀ᵐ p ∂μ.prod μ,
        p ∈ boundaryHalfOpenInterval ×ˢ boundaryHalfOpenInterval := by
      dsimp [μ]
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hae] with p hp
    simp  [regular_kernel_mode_norm]
    exact mul_le_mul_of_nonneg_right
      (regular_sawtooth_norm_le (Ioc_subset_Icc_self hp.1)
        (Ioc_subset_Icc_self hp.2)) (norm_nonneg _)
  have hmode (θ : ℝ) :
      Complex.exp (2 * π * Complex.I * (-n : ℤ) * θ / ((2 * π : ℝ) : ℂ)) =
        kernelFourierMode (-n) θ := by
    simpa only [fourier_coe_apply] using fourier_two_pi_eq_kernelFourierMode (-n) θ
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp_rw [fourier_coe_apply]
  simp only [sub_zero, Complex.real_smul, smul_eq_mul]
  simp_rw [hmode]
  push_cast
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  change (1 / circlePeriod) *
      (∫ θ, kernelFourierMode (-n) θ *
        (∫ s, sawtoothKernel θ s * f s ∂μ) ∂μ) = _
  have hsplit : (fun θ => kernelFourierMode (-n) θ *
      (∫ s, sawtoothKernel θ s * f s ∂μ)) =
      fun θ => ∫ s, kernelFourierMode (-n) θ * sawtoothKernel θ s * f s ∂μ := by
    funext θ
    rw [← integral_const_mul]
    congr 1
    funext s
    ring
  rw [hsplit, integral_integral_swap hint]
  have heq : (fun s => ∫ θ,
      kernelFourierMode (-n) θ * sawtoothKernel θ s * f s ∂μ) =ᵐ[μ]
      fun s => (2 / (n : ℂ)) * (kernelFourierMode (-n) s * f s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [integral_mul_const]
    have hmode := regular_sawtooth_outer_mode n (Ioc_subset_Icc_self hs)
    rw [intervalIntegral.integral_of_le two_pi_pos.le] at hmode
    grind
  rw [integral_congr_ae heq, integral_const_mul]
  ring

/-- The genuine sawtooth action of any L1 input is L2 on the finite
parameter interval. This follows from its actual integral bound. -/
theorem memLp_sawtoothAction :
    MemLp (fun θ => ∫ s in (0 : ℝ)..circlePeriod, sawtoothKernel θ s * f s) 2
      (volume.restrict boundaryHalfOpenInterval) := by
  let μ  := volume.restrict boundaryHalfOpenInterval
  have hmeas : AEStronglyMeasurable
      (fun θ => ∫ s, sawtoothKernel θ s * f s ∂μ) μ :=
    (regular_sawtooth_measurable.aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound hmeas (3 * ∫ s, ‖f s‖ ∂μ) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc
    ‖∫ s, sawtoothKernel θ s * f s ∂μ‖ ≤ ∫ s, 3 * ‖f s‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul 3)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (regular_sawtooth_norm_le (Ioc_subset_Icc_self hθ)
          (Ioc_subset_Icc_self hs)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

end


/-- The actual sawtooth boundary vector for an arbitrary L2 input. -/
def sawtoothBoundaryAction (f : BoundaryL2)  :=
  (memLp_sawtoothAction ((Lp.memLp f).integrable (by norm_num))).toLp _

theorem sawtoothBoundaryAction_fourier f n :
    boundaryFourier (sawtoothBoundaryAction f) n =
      (2 / (n : ℂ)) * boundaryFourier f n := by
  rw [boundaryFourier_apply, boundaryFourier_apply]
  have hf := (Lp.memLp f).integrable (by norm_num)
  have hact : (sawtoothBoundaryAction f : ComplexCurve) =ᵐ[
      volume.restrict boundaryHalfOpenInterval]
      (fun θ => ∫ s in (0 : ℝ)..circlePeriod, sawtoothKernel θ s * f s) := by
    exact MemLp.coeFn_toLp (memLp_sawtoothAction hf)
  rw [fourierCoeffOn_congr_ae two_pi_pos hact]
  rw [fourierCoeffOn_sawtoothAction hf]
  ring

private theorem regular_half_weight_square n :
    ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (sobWeight n : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Real.rpow_add (sobWeight_pos n)]
  norm_num
  rw [Real.rpow_neg_one, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (sobWeight_pos n).ne', Complex.ofReal_one]

/-- This actual bounded composition is the raw inverse derivative.
Its equality with the sawtooth integral is proved below, on all L2. -/
def regularRawInverseDerivative : L2Z →L[ℂ] L2Z :=
  (sobolevSmoothing (1 / 2) (by norm_num)).comp
    ((principalNormalized - (2 : ℂ) • normalizedInverseAbsOperator).comp
      (sobolevSmoothing (1 / 2) (by norm_num)))

theorem regularRawInverseDerivative_apply f n :
    regularRawInverseDerivative f n = (2 / (n : ℂ)) * f n := by
  simp only [regularRawInverseDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    principalNormalized, normalizedInverseAbsOperator_apply, sobolevSmoothing, diagOp_apply]
  by_cases hn : n = 0
  · simp_all [principalSymbol, normalizedInverseAbsSymbol]
  · have hsymbol : principalSymbol n - 2 * normalizedInverseAbsSymbol n =
        (sobWeight n : ℂ) * (2 / (n : ℂ)) := by
      simp  [principalSymbol, normalizedInverseAbsSymbol, if_neg hn]
      push_cast
      ring
    grind only [sobWeight, principalSymbol, normalizedInverseAbsSymbol, regular_half_weight_square]

private theorem regular_half_sqrt_cancel n :
    ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (Real.sqrt (sobWeight n) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, Real.sqrt_eq_rpow,
    ← Real.rpow_add (sobWeight_pos n)]
  norm_num

theorem common_regular_halfSmoothing_injective :
    Function.Injective (sobolevSmoothing (1 / 2) (by norm_num) : L2Z →L[ℂ] L2Z) := by
  intro f g h
  apply lp.ext
  funext n
  have hn := congrArg (fun v : L2Z => v n) h
  simp only [sobolevSmoothing, diagOp_apply] at hn
  have hw : (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) _).ne'
  exact mul_left_cancel₀ hw hn

section
variable {γ } {K } {E } {W } (hK : LipschitzWith K γ) (hW : IsTransport γ E W)

include γ K E W hK hW in
/-- Half smoothing of the actual normalized projected-observation
adjoint is exactly the ordinary unitary Fourier observation trace. -/
theorem halfSmoothing_adjoint_projObsDual (z : Ell2) :
    sobolevSmoothing (1 / 2) (by norm_num)
      ((√circlePeriod : ℂ) • ContinuousLinearMap.adjoint (projObsDual W) z) =
        boundaryFourier (projectedObservationBoundary hK hW z) := by
  rw [projObsDual_eq hK hW, rowSynth, ContinuousLinearMap.adjoint_adjoint]
  apply lp.ext
  funext n
  simp only [sobolevSmoothing, diagOp_apply, lp.coeFn_smul, Pi.smul_apply, rowAnalysis_apply, normProjObsRow, inner_smul_left, Complex.conj_ofReal, boundaryFourier_projectedObservation]
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ)) *
    ((√circlePeriod) * ((Real.sqrt (sobWeight n)) * ⟪projObsCoeffVec W n, z⟫_ℂ)) = _
  calc
    _ = (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ)) *
      (Real.sqrt (sobWeight n))) *
      ((√circlePeriod) * ⟪projObsCoeffVec W n, z⟫_ℂ) := by ring
    _ = _ := by rw [regular_half_sqrt_cancel, one_mul]

/-- The bounded boundary operator obtained from the genuine raw Fourier
multiplier. It equals the original coordinate sawtooth integral on all L2. -/
def sawtoothBoundaryOperator : ComplexEnd BoundaryL2 :=
  boundaryFourier.symm.toLinearIsometry.toContinuousLinearMap.comp
    (regularRawInverseDerivative.comp boundaryFourier.toLinearIsometry.toContinuousLinearMap)

theorem sawtoothBoundaryOperator_eq_action f :
    sawtoothBoundaryOperator f = sawtoothBoundaryAction f := by
  apply boundaryFourier.injective
  apply lp.ext
  funext n
  change boundaryFourier (boundaryFourier.symm
    (regularRawInverseDerivative (boundaryFourier f))) n = _
  simp_all [regularRawInverseDerivative_apply, sawtoothBoundaryAction_fourier]

/-- The corrected integral operator on ordinary boundary L2, transported
through the actual unitary circle lift. Both maps use their true measures. -/
def regularCorrectedBoundaryOperator {γ : ComplexCurve} {K : NNReal} {E : ℝ}
    {W : ℝ → ComplexEnd Ell2} (hK : LipschitzWith K γ)
    (hW : IsTransport γ E W) (hc : cutC (W circlePeriod) (basisVec 0) ≠ 0) :
    ComplexEnd BoundaryL2 :=
  boundaryCircleUnitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((correctedKernelL2Op hK hW hc).comp
      boundaryCircleUnitary.toLinearIsometry.toContinuousLinearMap)

include γ K E W hK hW in
theorem regularCorrectedBoundaryOperator_fourier
    hc
    hr
    f :
    boundaryFourier (regularCorrectedBoundaryOperator hK hW hc f) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr (boundaryFourier f) := by
  change (fourierBasis (T := 2 * π)).repr
    (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hK hW hc (boundaryCircleUnitary f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,
    correctedKernelL2Op_fourier_action hK hW hc hr]
  rfl

/-- Raw square summability follows from the genuine normalized matrix
bound, without an arclength hypothesis on the conformal parameter. -/
theorem summable_regularKernelIntegralMatrix W
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) hbase
  have hm : 1 ≤ (sobWeight p.1) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (one_le_sobWeight p.1) (by norm_num)
  have hn : 1 ≤ (sobWeight p.2) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (one_le_sobWeight p.2) (by norm_num)
  have hweight := one_le_mul_of_one_le_of_one_le hm hn
  have heq : correctedRemainderMatrix W 0 0 p =
      (((sobWeight p.1) ^ (1 / 2 : ℝ) *
        (sobWeight p.2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        kernelIntegralMatrix (r := correctedKernel W) p := by
    simp  [correctedRemainderMatrix, kernelIntegralMatrix, sobWeight]
    push_cast
    ring
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  simpa   using mul_le_mul_of_nonneg_right hweight (norm_nonneg _)

section
include γ K E W hK hW

theorem memLp_regularCorrectedAction 
    (hf : Integrable f (volume.restrict boundaryHalfOpenInterval)) :
    MemLp (fun θ => ∫ s in (0 : ℝ)..circlePeriod, correctedKernel W θ s * f s) 2
      (volume.restrict boundaryHalfOpenInterval) := by
  let μ  := volume.restrict boundaryHalfOpenInterval
  have hmeas  :=
    ((aestronglyMeasurable_correctedKernel hW).mul
      hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound hmeas ((4 + ‖cutBE W‖) * ∫ s, ‖f s‖ ∂μ) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc
    ‖∫ s, correctedKernel W θ s * f s ∂μ‖ ≤
        ∫ s, (4 + ‖cutBE W‖) * ‖f s‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul (4 + ‖cutBE W‖))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_correctedKernel_le hK hW (Ioc_subset_Icc_self hθ)
          (Ioc_subset_Icc_self hs)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- On every bounded measurable representative the genuine corrected
boundary CLM has the Fourier coefficients of the original physical
kernel integral. The factor sqrt(2π) converts the probability-Haar basis. -/
theorem regularCorrectedBoundaryOperator_toLp_fourier
    hc
    (g : BoundaryL2)  (hf : Measurable f) 
    (hfB : ∀ s, ‖f s‖ ≤ B)
    (hgf : (g : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f) n :
    boundaryFourier (regularCorrectedBoundaryOperator hK hW hc g) n =
      (√circlePeriod : ℂ) * fourierCoeffOn two_pi_pos
        (fun θ => ∫ s in (0 : ℝ)..circlePeriod, correctedKernel W θ s * f s) n := by
  let fC  := (memLp_liftIco_two_pi hf hfB).toLp _
  have hcircle : boundaryCircleLift g = fC := by
    apply Lp.ext
    exact (boundaryCircleLift_coe g).trans
      (((boundary_liftIoc_congr_ae hgf).trans
        (boundary_liftIoc_eq_liftIco_ae f)).trans
          (MemLp.coeFn_toLp (memLp_liftIco_two_pi hf hfB)).symm)
  change (fourierBasis (T := 2 * π)).repr
    (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hK hW hc (boundaryCircleUnitary g)))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (fourierBasis (T := 2 * π)).repr
    (correctedKernelL2Op hK hW hc ((√circlePeriod : ℂ) • boundaryCircleLift g)) n = _
  rw [hcircle, map_smul, map_smul]
  change (√circlePeriod) *
    (fourierBasis (T := 2 * π)).repr (correctedKernelL2Op hK hW hc fC) n = _
  rw [correctedKernelL2Op_toLp_fourier hK hW hc hf hfB]

end


private theorem regular_boundary_ae_of_eq (u v : BoundaryL2) 
    (huv : u = v)
    (hv : (v : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f) :
    (u : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f := by
  subst u
  exact hv

private theorem regular_boundary_eq_of_periodic_load_eq
    (T : L2Z →L[ℂ] BoundaryL2) (W : ℝ → ComplexEnd Ell2)
    (b d : L2Z) (hbd : b = d) (f : ComplexCurve) (u v : BoundaryL2)
    (hu : (u : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval]
      periodicP W (T b : ComplexCurve) f)
    (hv : (v : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval]
      periodicP W (T d : ComplexCurve) f) : u = v := by
  subst b
  exact Lp.ext (hu.trans hv.symm)

private theorem regular_boundary_smoothing_difference
    (S : L2Z →L[ℂ] L2Z) (x q : L2Z) (p r : BoundaryL2)
    (hx : S x = boundaryFourier p) (hq : S q = boundaryFourier r) :
    S (x - (2 : ℂ) • q) = boundaryFourier (p - (2 : ℂ) • r) := by
  rw [map_sub, map_smul, map_sub, map_smul, hx, hq]

include γ K E W hK hW in
private theorem regular_boundary_periodic_sum_ae
    hc
    (t g : BoundaryL2)  (hf : Continuous f) 
    (hfB : ∀ s, ‖f s‖ ≤ B)
    (hgf : (g : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f) :
    (((2 : ℂ) • t + sawtoothBoundaryOperator g +
      regularCorrectedBoundaryOperator hK hW hc g : BoundaryL2) : ComplexCurve) =ᵐ[
        volume.restrict boundaryHalfOpenInterval] periodicP W (t : ComplexCurve) f := by
  have hfLp  := (Lp.memLp g).ae_eq hgf
  have hfI := hfLp.integrable (by norm_num)
  let k  := (memLp_regularCorrectedAction hK hW hfI).toLp _
  have hk : regularCorrectedBoundaryOperator hK hW hc g = k := by
    apply boundaryFourier.injective
    apply lp.ext
    funext n
    rw [regularCorrectedBoundaryOperator_toLp_fourier hK hW hc g hf.measurable hfB hgf,
      boundaryFourier_apply]
    congr 1
    exact (congrFun (fourierCoeffOn_congr_ae two_pi_pos
      (MemLp.coeFn_toLp (memLp_regularCorrectedAction hK hW hfI))) n).symm
  have hsaw (θ : ℝ) :
      (∫ s in (0 : ℝ)..circlePeriod, sawtoothKernel θ s * g s) =
        ∫ s in (0 : ℝ)..circlePeriod, sawtoothKernel θ s * f s := by
    simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
    apply integral_congr_ae
    filter_upwards [hgf] with s hs
    rw [hs]
  rw [sawtoothBoundaryOperator_eq_action, hk]
  filter_upwards [Lp.coeFn_add ((2 : ℂ) • t + sawtoothBoundaryAction g) k,
    Lp.coeFn_add ((2 : ℂ) • t) (sawtoothBoundaryAction g), Lp.coeFn_smul (2 : ℂ) t,
    MemLp.coeFn_toLp (memLp_sawtoothAction
      ((Lp.memLp g).integrable (by norm_num))),
    MemLp.coeFn_toLp (memLp_regularCorrectedAction hK hW hfI),
    ae_restrict_mem measurableSet_Ioc] with θ ha hb hc' hs hk' hθ
  rw [ha, Pi.add_apply, hb, Pi.add_apply, hc', Pi.smul_apply, smul_eq_mul]
  dsimp only [sawtoothBoundaryAction]
  rw [hs, hk', hsaw]
  exact (periodicP_eq_doubleTrace_add_kernel_integrals hW.1 t
    hf hfB (Ioc_subset_Icc_self hθ)).symm

end


section ActualPeriodicOperator

variable {R } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hL : IsLipschitzDomain (F '' unitDisk))

local notation "ΩP" => F '' unitDisk
local notation "QP" => localConformalDiskHalfTrace hR F hFs hL
local notation "TP" => localConformalDiskH1Trace hR F hFs hL

theorem localConformal_halfSmoothing_halfTrace u :
    sobolevSmoothing (1 / 2) (by norm_num) (QP u) = boundaryFourier (TP u) := by
  apply lp.ext
  funext n
  simp only [sobolevSmoothing, diagOp_apply, localConformalDiskHalfTrace_apply]
  have hw : sobWeight n ^ (-(1 / 2 : ℝ)) * Real.sqrt (sobWeight n) = 1 := by
    rw [Real.sqrt_eq_rpow, mul_comm, sobWeight_rpow_mul_neg]
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ)) *
    ((Real.sqrt (sobWeight n)) * boundaryFourier (TP u) n) = _
  rw [← mul_assoc, ← Complex.ofReal_mul, hw, Complex.ofReal_one, one_mul]

/-- The genuine regular trace, the original sawtooth integral, and the
actual corrected boundary kernel form this bounded coordinate operator.
The normalization identity is proved next, rather than used to define it. -/
def localConformalRegularPeriodicOperator (E₀ E : ℝ)
    {γ : ComplexCurve} {K : NNReal} {W : ℝ → ComplexEnd Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W circlePeriod) (basisVec 0) ≠ 0) : ComplexEnd BoundaryL2 :=
  (2 : ℂ) • ((localConformalDiskH1Trace hR F hFs hL).comp
    ((h1RegularResolvent ΩP E₀ E).comp
    ((ContinuousLinearMap.adjoint QP).comp
      ((sobolevSmoothing (1 / 2) (by norm_num)).comp
        boundaryFourier.toLinearIsometry.toContinuousLinearMap)))) +
    sawtoothBoundaryOperator + regularCorrectedBoundaryOperator hK hW hc

section
variable (E₀ E : ℝ) {γ } {K } {W } (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (hc : cutC (W circlePeriod) (basisVec 0) ≠ 0)
local notation "regularPeriodicOperatorFixed" => localConformalRegularPeriodicOperator hR F hFs hL E₀ E hK hW hc

include E₀ E γ K W hK hW hc

/-- The actual bounded operator agrees with the assembled normalized
regular Fourier operator on every L2 load, including its constant mode. -/
theorem localConformalRegularPeriodicOperator_fourier
    hbase
    f :
    boundaryFourier (regularPeriodicOperatorFixed f) =
      sobolevSmoothing (1 / 2) (by norm_num)
        (normalizedPeriodicRegularOperator QP E₀ E W hbase
          (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier f))) := by
  let S  := sobolevSmoothing (1 / 2) (by norm_num)
  let b  := S (boundaryFourier f)
  let u  :=
    h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP b)
  let hr := summable_regularKernelIntegralMatrix W hbase
  have hN : S (normalizedNeumannRegular QP E₀ E b) = boundaryFourier (TP u) := by
    exact localConformal_halfSmoothing_halfTrace hR F hFs hL u
  have hS : boundaryFourier (sawtoothBoundaryOperator f) =
      regularRawInverseDerivative (boundaryFourier f) := by
    change boundaryFourier (boundaryFourier.symm
      (regularRawInverseDerivative (boundaryFourier f))) = _
    norm_num
  have hKern := regularCorrectedBoundaryOperator_fourier hK hW hc hr f
  have hraw : regularRawInverseDerivative (boundaryFourier f) =
      S (principalNormalized b) - (2 : ℂ) • S (normalizedInverseAbsOperator b) := by
    simp only [regularRawInverseDerivative, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul]
    rfl
  have hHS : S (hsMatrixOp (correctedRemainderMatrix W 0 0) hbase b) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr (boundaryFourier f) :=
    correctedRemainderOp_half_smoothing W hbase hr (boundaryFourier f)
  change boundaryFourier ((2 : ℂ) • TP u + sawtoothBoundaryOperator f +
    regularCorrectedBoundaryOperator hK hW hc f) =
    S (normalizedPeriodicRegularOperator QP E₀ E W hbase b)
  rw [map_add, map_add, map_smul, hS, hKern, hraw]
  simp  [normalizedPeriodicRegularOperator, 
     
    map_add, map_smul, map_sub, smul_sub, hN, hHS]
  abel

/-- The bounded operator's output is the actual pointwise periodic
expression on every continuous bounded coordinate load. Its trace input
is the original regular Neumann solution, rather than a stipulated form. -/
theorem localConformalRegularPeriodicOperator_apply_ae
    (g : BoundaryL2) {f : ComplexCurve} (hf : Continuous f) {B : ℝ}
    (hfB : ∀ s, ‖f s‖ ≤ B)
    (hgf : (g : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f) :
    (regularPeriodicOperatorFixed g : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        periodicP W
          (TP (h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP
            (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)))) : ComplexCurve) f := by
  let t  := TP (h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP
    (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g))))
  have hop : regularPeriodicOperatorFixed g =
      (2 : ℂ) • t + sawtoothBoundaryOperator g +
        regularCorrectedBoundaryOperator hK hW hc g := by
    rfl
  exact regular_boundary_ae_of_eq _ _ hop
    (regular_boundary_periodic_sum_ae hK hW hc t g hf hfB hgf)

end


end ActualPeriodicOperator

section ActualHerglotzMatching

variable {R C } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    {γ } (hγ : IsBoundaryParam (F '' unitDisk) γ)
    {τ } {c } (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCircleMap θ) = γ (τ θ))
    {K } (hΓLip : LipschitzWith K (physicalCircleTrace F))
    {E₀ } (hE₀ : 0 ≤ E₀) {W }
    (hW : IsTransport (physicalCircleTrace F) E₀ W)
    (hc : cutC (W circlePeriod) (basisVec 0) ≠ 0)
    {a } (ha : IsDirDensity a)
local notation "regularPeriodicHerglotzBoundaryFixed" => localConformalRegularPeriodicHerglotzBoundary hR F hFs hb hL hhol hinj hC hγ hτ hcoord hΓLip hE₀ hW hc ha


include hR hFs ha in
private theorem regular_continuous_coordinateConormal k :
    Continuous (herglotzConormal k a (physicalCircleTrace F)) := by
  have hΓ := contDiff_physicalCircleTrace_of_neighborhood hR F
    (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have heq  :=
    funext (herglotzConormal_eq ha.intervalIntegrable k (physicalCircleTrace F))
  rw [heq]
  exact continuous_const.mul
    (((Complex.continuous_conj.comp hΓ.continuous_deriv_one).mul
      ((continuous_herglotzCoeff ha.intervalIntegrable k (-1)).comp hΓ.continuous)).sub
    (hΓ.continuous_deriv_one.mul
      ((continuous_herglotzCoeff ha.intervalIntegrable k 1).comp hΓ.continuous)))

include hγ hτ hhol hinj hC hcoord hΓLip hE₀ hW hc in
/-- Applying the genuine bounded coordinate operator to the actual
Herglotz conormal gives exactly the previously derived physical regular
periodic expression. The resonant subtraction is therefore preserved. -/
theorem localConformalRegularPeriodicOperator_herglotz :
    localConformalRegularPeriodicOperator hR F hFs hL E₀ E₀ hΓLip hW hc
      (localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E₀)) =
        regularPeriodicHerglotzBoundaryFixed := by
  obtain ⟨_, B, hfB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E₀) hΓLip
  have hop := localConformalRegularPeriodicOperator_apply_ae hR F hFs hL E₀ E₀ hΓLip hW hc
    (localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E₀))
    (regular_continuous_coordinateConormal hR F hFs ha (Real.sqrt E₀)) hfB
    (localConformalHerglotzCoordinateLoad_ae F hΓLip ha (Real.sqrt E₀))
  have hload := localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord
    hΓLip ha (Real.sqrt E₀)
  let T  :=
    (localConformalDiskH1Trace hR F hFs hL).comp
      ((h1RegularResolvent (F '' ball 0 1) E₀ E₀).comp
        (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL)))
  have hbdy  :=
    MemLp.coeFn_toLp (localConformalRegularPeriodicHerglotzExpression_memLp
      hR F hFs hb hL hhol hinj hC hγ hτ hcoord hΓLip hE₀ hW hc ha)
  have hopT : (localConformalRegularPeriodicOperator hR F hFs hL E₀ E₀
      hΓLip hW hc (localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E₀)) : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        periodicP W
          (T (sobolevSmoothing (1 / 2) (by norm_num)
            (boundaryFourier (localConformalHerglotzCoordinateLoad F hΓLip ha
              (Real.sqrt E₀)))) : ComplexCurve)
          (herglotzConormal (Real.sqrt E₀) a (physicalCircleTrace F)) := by
    assumption
  have hbdyT : (regularPeriodicHerglotzBoundaryFixed : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        periodicP W
          (T (localConformalBoundaryLoad hτ
            (herglotzConormalL2 hγ ha (Real.sqrt E₀))) : ComplexCurve)
          (herglotzConormal (Real.sqrt E₀) a (physicalCircleTrace F)) := by
    assumption
  exact regular_boundary_eq_of_periodic_load_eq T W _ _ hload.symm
    (herglotzConormal (Real.sqrt E₀) a (physicalCircleTrace F)) _ _ hopT hbdyT

section
variable (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
include hbase

section
include hhol hinj hC hcoord hΓLip hE₀ hW hc

include hb in
/-- The assembled normalized operator is now matched to the actual
regular periodic Herglotz expression, with ordinary boundary Fourier
normalization sqrt(2π). There is no discarded zero Fourier coefficient. -/
theorem normalizedPeriodicRegularOperator_herglotz_fourier :
    sobolevSmoothing (1 / 2) (by norm_num)
      (normalizedPeriodicRegularOperator (localConformalDiskHalfTrace hR F hFs hL)
        E₀ E₀ W hbase (localConformalBoundaryLoad hτ
          (herglotzConormalL2 hγ ha (Real.sqrt E₀)))) =
      boundaryFourier regularPeriodicHerglotzBoundaryFixed := by
  rw [localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha]
  rw [← localConformalRegularPeriodicOperator_fourier hR F hFs hL E₀ E₀ hΓLip hW hc hbase,
    localConformalRegularPeriodicOperator_herglotz hR F hFs hb hL hhol hinj hC
      hγ hτ hcoord hΓLip hE₀ hW hc ha]

/-- The full normalized regular expression on genuine Herglotz data is
the true projected-observation adjoint minus twice the original resonant
half-trace. Half smoothing is canceled using its genuine injectivity. -/
theorem normalizedPeriodicRegularOperator_herglotz_eq :
    normalizedPeriodicRegularOperator (localConformalDiskHalfTrace hR F hFs hL)
        E₀ E₀ W hbase (localConformalBoundaryLoad hτ
          (herglotzConormalL2 hγ ha (Real.sqrt E₀))) =
      (√circlePeriod : ℂ) • ContinuousLinearMap.adjoint (projObsDual W)
        (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha) -
      (2 : ℂ) • localConformalDiskHalfTrace hR F hFs hL
        ((h1ResonantSpace (F '' unitDisk) E₀).starProjection
          (herglotzWaveH1 hb ha (Real.sqrt E₀))) := by
  apply common_regular_halfSmoothing_injective
  have hfour := normalizedPeriodicRegularOperator_herglotz_fourier
    hR F hFs hb hL hhol hinj hC hγ hτ hcoord hΓLip hE₀ hW hc ha hbase
  have hbdy := localConformalRegularPeriodicHerglotzBoundary_eq
    hR F hFs hb hL hhol hinj hC hγ hτ hcoord hΓLip hE₀ hW hc ha
  have hsm := regular_boundary_smoothing_difference
    (sobolevSmoothing (1 / 2) (by norm_num)) _ _ _ _
    (halfSmoothing_adjoint_projObsDual hΓLip hW
      (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha))
    (localConformal_halfSmoothing_halfTrace hR F hFs hL
      ((h1ResonantSpace (F '' ball 0 1) E₀).starProjection
        (herglotzWaveH1 hb ha (Real.sqrt E₀))))
  exact hfour.trans ((congrArg boundaryFourier hbdy).trans hsm.symm)

end


end


end ActualHerglotzMatching

end PolyaNeumann

end
