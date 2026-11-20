module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

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
public import RequestProject.PlanarNotation

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

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set MeasureTheory Metric Real Filter
open scoped Real InnerProductSpace ComplexConjugate

/-- The actual corrected initial Herglotz vector. Both the initial jet
and the finite cut correction retain their original normalizations. -/
def regularHerglotzObservationVector {γ : ℝ → ℂ} (E : ℝ)
    (W : TransportPath) {a : ℝ → ℂ} (ha : IsDirDensity a) : Ell2 :=
  vacuumWeight •
      (herglotzVec ha (Real.sqrt E) (γ 0) +
        ContinuousLinearMap.adjoint (W anglePeriod)
          (herglotzVec ha (Real.sqrt E) (γ 0))) +
    cutBE W (observationAdj W (herglotzConormal (Real.sqrt E) a γ))

/-- The corrected expression of a genuine wave is its actual corrected
observation, before the genuine resonant trace is removed. -/
theorem periodicP_herglotz_eq_regularObservation {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ anglePeriod = γ 0) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) {θ : ℝ} (hθ : θ ∈ angleInterval) :
    periodicP W (fun s => herglotzWave (Real.sqrt E) a (γ s))
        (herglotzConormal (Real.sqrt E) a γ) θ =
      observation W (regularHerglotzObservationVector (γ := γ) E W ha) θ := by
  rw [periodicP, periodicA_herglotz_eq_observation hK hclosed hW ha hθ]
  simp [regularHerglotzObservationVector, cutBE, observation, inner_add_right]

/-- The true endpoint cancellation places the corrected Herglotz vector
in the orthogonal complement of the actual cut direction. -/
theorem regularHerglotzObservationVector_inner_cut_eq_zero
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ anglePeriod = γ 0) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (hc : cutVector W ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    ⟪cutVector W,
      regularHerglotzObservationVector (γ := γ) E W ha⟫_ℂ = 0 := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  
  have hp := periodicP_periodic (n := fun s => herglotzWave (Real.sqrt E) a (γ s))
    hK hW hc (by
      
      rw [hclosed]) hgm hgB
  rw [periodicP_herglotz_eq_regularObservation hK hclosed hW ha
        ⟨two_pi_pos.le, le_rfl⟩,
    periodicP_herglotz_eq_regularObservation hK hclosed hW ha
        ⟨le_rfl, two_pi_pos.le⟩] at hp
  rw [← observation_jump hW]
  exact sub_eq_zero.mpr hp

theorem regularHerglotzObservationVector_cutProj
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ anglePeriod = γ 0) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (hc : cutVector W ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    cutProj (cutVector W)
        (regularHerglotzObservationVector (γ := γ) E W ha) =
      regularHerglotzObservationVector (γ := γ) E W ha := by
  rw [cutProj_eq_starProjection, Submodule.starProjection_eq_self_iff,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact regularHerglotzObservationVector_inner_cut_eq_zero hK hclosed hW hc ha

private theorem regular_boundary_sub_ae (u v : BoundaryL2) {f : ℝ → ℂ}
    (hf : (u : ℝ → ℂ) =ᵐ[angleMeasure] f) :
    ((u - v : BoundaryL2) : ℝ → ℂ) =ᵐ[angleMeasure]
      fun θ => f θ - v θ := by
  filter_upwards [Lp.coeFn_sub u v, hf] with θ hs hw
  rw [hs, Pi.sub_apply, hw]

private theorem regular_observation_sub_ae {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) {E : ℝ} {W : TransportPath}
    (hW : IsTransport γ E W) (z : Ell2) (r : BoundaryL2)
    (hz : cutProj (cutVector W) z = z) :
    ((projectedObservationBoundary hK hW z - (2 : ℂ) • r : BoundaryL2) : ℝ → ℂ)
      =ᵐ[angleMeasure]
        fun θ => observation W z θ - 2 * r θ := by
  filter_upwards [Lp.coeFn_sub (projectedObservationBoundary hK hW z) ((2 : ℂ) • r),
    Lp.coeFn_smul (2 : ℂ) r, projectedObservationBoundary_coe hK hW z]
      with θ hs h2 ho
  rw [hs, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, ho,
    ← observation_cutProj_eq, hz]

private theorem regular_boundary_toLp_eq {f : ℝ → ℂ}
    (hf : MemLp f 2 angleMeasure) (u : BoundaryL2)
    (hu : (u : ℝ → ℂ) =ᵐ[angleMeasure] f) :
    hf.toLp f = u := by
  apply Lp.ext
  exact hf.coeFn_toLp.trans hu.symm

/-- The periodic expression uses the actual pole-subtracted Neumann
trace, not an independently supplied solution trace. Its forcing is the
actual Herglotz conormal function. -/
def neumannRegularPeriodicHerglotzExpression {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E₀ : ℝ)
    (W : TransportPath) {a : ℝ → ℂ} (ha : IsDirDensity a) : ℝ → ℂ :=
  periodicP W
    (neumannBoundaryRegular hb hL hγ E₀ E₀
      (herglotzConormalL2 hγ ha (Real.sqrt E₀)) : ℝ → ℂ)
    (herglotzConormal (Real.sqrt E₀) a γ)

section OrdinaryBoundary

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {K : NNReal} (hK : LipschitzWith K γ)
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : TransportPath} (hW : IsTransport γ E₀ W)
    (hc : cutVector W ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a)

local notation "uA" => herglotzWaveH1 hb ha (Real.sqrt E₀)
local notation "gA" => herglotzConormal (Real.sqrt E₀) a γ
local notation "gAL2" => herglotzConormalL2 hγ ha (Real.sqrt E₀)
local notation "rA" => h1BoundaryTrace hL hγ
  (Submodule.starProjection (h1ResonantSpace Ω E₀) uA)
local notation "zA" => regularHerglotzObservationVector (γ := γ) E₀ W ha

end OrdinaryBoundary

/-- The positive Jacobian makes the supplied trace reparametrization
preserve null sets on the actual cut. This is proved by change of
variables, even for a property with no chosen measurable representative. -/
theorem isC1TraceReparam_ae_comp {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) {p : ℝ → Prop}
    (hp : ∀ᵐ s ∂angleMeasure, p s) :
    ∀ᵐ θ ∂angleMeasure, p (τ θ) := by
  classical
  let q : ℝ → ℝ := fun s => if p s then 0 else 1
  have hqzero : q =ᵐ[angleMeasure] 0 := by
    filter_upwards [hp] with s hs
    simp [q, if_pos hs]
  
  have himage := hτ.continuous.continuousOn.image_Icc_of_monotoneOn two_pi_pos.le
        (hτ.monotone.monotoneOn _)
  simp only [hτ.zero, hτ.endpoint] at himage
  
  have hj  :=
    (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Icc
      (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
      (hτ.monotone.monotoneOn angleInterval) q).mp
        (by simpa only [himage] using ((integrableOn_Icc_iff_integrableOn_Ioc (f := q) (by finiteness)).mpr ((MeasureTheory.integrable_zero ℝ ℝ angleMeasure).congr hqzero.symm)))
  have hj' := (integrableOn_Icc_iff_integrableOn_Ioc
         (by finiteness)).mp hj
  have hchange := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Icc
    (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
    (hτ.monotone.monotoneOn angleInterval) q
  have hz : (∫ θ in angleIoc, deriv τ θ * q (τ θ)) = 0 := by
    have heq : (∫ θ in angleIoc, deriv τ θ * q (τ θ)) =
        ∫ s in angleIoc, q s := by
      simpa only [himage, integral_Icc_eq_integral_Ioc, smul_eq_mul] using hchange.symm
    rw [heq, integral_congr_ae hqzero]
    simp
  
  
  
  filter_upwards [((integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun θ =>
    mul_nonneg hτ.monotone.deriv_nonneg (by simp only [q]; split_ifs <;> norm_num)) hj').mp hz), (ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hτ.lower_ae)] with θ hzero hlower
  by_contra hbad
  
  
  apply (hτ.lower_pos.trans_le hlower).ne'
  simpa only [q, if_neg hbad, mul_one, Pi.zero_apply] using hzero

/-- The actual conormal derivative obeys the Jacobian law a.e. for the
supplied C1 change of parameter. The original boundary curve only needs
to be Lipschitz; Rademacher and the true null-set transport supply its
derivative at the composed points. -/
theorem herglotzConormal_traceReparam_ae {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    herglotzConormal k a (γ ∘ τ)
      =ᵐ[angleMeasure]
        (fun θ => deriv τ θ • herglotzConormal k a γ (τ θ)) := by
  
  filter_upwards [(isC1TraceReparam_ae_comp hτ
    (ae_restrict_of_ae (hK.ae_differentiableAt )))] with θ hγdiff
  
  rw [herglotzConormal_eq ha.intervalIntegrable, (hγdiff.hasDerivAt.scomp θ (hτ.contDiff.differentiable_one θ).hasDerivAt).deriv,
    herglotzConormal_eq ha.intervalIntegrable]
  simp
  ring

section

variable (F : ℂ → ℂ)

/-- Actual variable-speed coordinate conormal, as an ordinary L2 class. -/
def localConformalHerglotzCoordinateLoad {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) : BoundaryL2 :=
  (memLp_herglotzConormal ha k hΓLip).toLp
    (herglotzConormal k a (physicalCircleTrace F))

theorem localConformalHerglotzCoordinateLoad_ae {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    (localConformalHerglotzCoordinateLoad F hΓLip ha k : ℝ → ℂ)
      =ᵐ[angleMeasure]
        herglotzConormal k a (physicalCircleTrace F) :=
  (memLp_herglotzConormal ha k hΓLip).coeFn_toLp

end

section ConformalCoordinates

section

variable (Φ : ConformalDiskMap) (F : ℂ → ℂ)

/-- The actual H1 regular solution itself is the wave minus its true
resonant component. This is stronger than a Fourier trace equality. -/
theorem localConformal_regularHerglotzH1_eq_sub_resonant {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {E₀ : ℝ} (hE₀ : 0 ≤ E₀) {a : ℝ → ℂ}
    (ha : IsDirDensity a) :
    h1RegularResolvent Φ.domain E₀ E₀
        (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace Φ.lipschitzDomain)
          (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀)))) =
      herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀) -
        (h1ResonantSpace Φ.domain E₀).starProjection (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀)) := by
  
  rw [← ((isNormalizedNeumannSolution_iff (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ _ _).mp
    (localConformalHerglotz_isNormalizedNeumannSolution Φ hγ hτ hcoord hE₀ ha)), h1RegularResolvent_form_at_reference Φ.bounded Φ.lipschitzDomain hE₀,
    Submodule.starProjection_orthogonal_val]

/-- The ordinary conformal trace retains the same exact removed
resonant component, with no extra square-root Fourier scale. -/
theorem localConformal_regularHerglotz_coordinate_trace_eq {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {E₀ : ℝ} (hE₀ : 0 ≤ E₀) {a : ℝ → ℂ}
    (ha : IsDirDensity a) :
    (Φ.pulledBackTrace Φ.lipschitzDomain) (h1RegularResolvent Φ.domain E₀ E₀
      (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace Φ.lipschitzDomain)
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))))) =
      (Φ.pulledBackTrace Φ.lipschitzDomain) (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀)) -
        (Φ.pulledBackTrace Φ.lipschitzDomain) ((h1ResonantSpace Φ.domain E₀).starProjection (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀))) := by
  rw [localConformal_regularHerglotzH1_eq_sub_resonant Φ hγ hτ hcoord hE₀ ha, map_sub]

/-- The genuine Herglotz H1 vector has its actual variable-speed circle
trace. A true smooth cutoff and the proved trace identity establish it. -/
theorem localConformalHerglotz_coordinate_trace_ae {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (herglotzWaveH1 Φ.bounded ha k) : ℝ → ℂ)
      =ᵐ[angleMeasure]
        (fun θ => herglotzWave k a (Φ.boundary θ)) := by
  obtain ⟨f, hfu, hfγ⟩ := exists_smoothTraceTest_herglotz Φ.bounded Φ.lipschitzDomain hγ ha k
  rw [← hfu]
  filter_upwards [localConformalDiskH1Trace_smooth_ae Φ f,
    ae_restrict_mem measurableSet_Ioc] with θ ht hθ
  rw [ht, hcoord, hfγ _ (hτ.mapsTo (Ioc_subset_Icc_self hθ))]
  simpa [physicalCircleTrace, hcoord] using (herglotzWave_eq k a (γ (τ θ))).symm

/-- The constructed physical Jacobian load equals the actual conormal
on the genuine variable-speed conformal circle. No load equality is an
input to this theorem. -/
theorem localConformalHerglotz_traceReparamConormal_eq_coordinateLoad {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam (F '' unitDisk) γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    traceReparamConormalL2 hτ (herglotzConormalL2 hγ ha k) =
      localConformalHerglotzCoordinateLoad F hΓLip ha k := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hΓ : physicalCircleTrace F = γ ∘ τ := by
    funext θ
    exact hcoord θ
  
  have hc := herglotzConormal_traceReparam_ae hKγ hτ ha k
  rw [← hΓ] at hc
  apply Lp.ext
  filter_upwards [traceReparamConormalL2_ae hτ _, (isC1TraceReparam_ae_comp hτ (herglotzConormalL2_ae hγ ha k)), hc,
    localConformalHerglotzCoordinateLoad_ae F hΓLip ha k] with θ ht hr hc hg
  rw [ht, hr, hg]
  exact hc.symm

/-- In particular the normalized weak load is exactly half smoothing of
the actual coordinate conormal's unitary Fourier coefficients. -/
theorem localConformalHerglotzBoundaryLoad_eq_coordinateLoad {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam (F '' unitDisk) γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha k) =
      sobolevSmoothing halfOrder (by norm_num)
        (boundaryFourier (localConformalHerglotzCoordinateLoad F hΓLip ha k)) := by
  unfold localConformalBoundaryLoad
  rw [localConformalHerglotz_traceReparamConormal_eq_coordinateLoad F hγ hτ hcoord hΓLip ha k]

/-- The actual regular coordinate trace is used with the true
variable-speed Herglotz conormal. The variational input is explicitly the
proved Jacobian transform of the physical load. -/
def SmoothDiskMap.regularPeriodicHerglotzExpression (Φ : SmoothDiskMap)
    (hL : IsLipschitzDomain Φ.domain) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ}
    {c : ℝ} (hτ : IsC1TraceReparam τ c) (E₀ : ℝ) (W : TransportPath) {a : ℝ → ℂ}
    (ha : IsDirDensity a) : ℝ → ℂ :=
  periodicP W
    ((Φ.pulledBackTrace hL) (h1RegularResolvent Φ.domain E₀ E₀
      (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL)
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))))) : ℝ → ℂ)
    (herglotzConormal (Real.sqrt E₀) a Φ.boundary)

/-- Exact regular periodic identity in the genuine conformal circle.
Its variable speed does not enter an IsBoundaryParam assumption. -/
theorem localConformalRegularPeriodicHerglotzExpression_ae {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : TransportPath} (hW : IsTransport Φ.boundary E₀ W) {a : ℝ → ℂ}
    (ha : IsDirDensity a) :
    Φ.regularPeriodicHerglotzExpression Φ.lipschitzDomain hγ hτ E₀ W ha
      =ᵐ[angleMeasure]
        (fun θ => observation W
            (regularHerglotzObservationVector (γ := Φ.boundary) E₀ W ha) θ -
          2 * (Φ.pulledBackTrace Φ.lipschitzDomain) ((h1ResonantSpace Φ.domain E₀).starProjection
            (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀))) θ) := by
  have hn :
      ((Φ.pulledBackTrace Φ.lipschitzDomain) (h1RegularResolvent Φ.domain E₀ E₀
        (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace Φ.lipschitzDomain)
          (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))))))
        =ᵐ[angleMeasure]
          (fun θ => herglotzWave (Real.sqrt E₀) a (Φ.boundary θ) -
            (Φ.pulledBackTrace Φ.lipschitzDomain) ((h1ResonantSpace Φ.domain E₀).starProjection
              (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀))) θ) := by
    rw [localConformal_regularHerglotz_coordinate_trace_eq Φ hγ hτ hcoord hE₀ ha]
    exact regular_boundary_sub_ae _ _
      (localConformalHerglotz_coordinate_trace_ae Φ hγ hτ
        hcoord ha (Real.sqrt E₀))
  
  filter_upwards [hn, ae_restrict_mem measurableSet_Ioc] with θ hn hθ
  have hp := periodicP_herglotz_eq_regularObservation hΓLip (by
      simpa only [zero_add] using Φ.periodic_boundary 0) hW ha
    (Ioc_subset_Icc_self hθ)
  simp only [SmoothDiskMap.regularPeriodicHerglotzExpression, periodicP, periodicA, hn]
    at hp ⊢
  linear_combination hp

/-- The corrected observation vector in the conformal identity is
orthogonal to its true boundary-origin cut. -/
theorem localConformalRegularHerglotzObservationVector_cutProj {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) {E₀ : ℝ} {W : TransportPath}
    (hW : IsTransport (physicalCircleTrace F) E₀ W) (hc : cutVector W ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    cutProj (cutVector W)
        (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha) =
      regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha := regularHerglotzObservationVector_cutProj hΓLip
    (by simpa only [zero_add] using physicalCircleTrace_periodic F 0) hW hc ha

end

section CoordinatePairing

section

variable (Φ : ConformalDiskMap)

theorem localConformalRegularPeriodicHerglotzExpression_memLp {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : TransportPath} (hW : IsTransport Φ.boundary E₀ W)
    (hc : cutVector W ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    MemLp (Φ.regularPeriodicHerglotzExpression Φ.lipschitzDomain hγ hτ E₀ W ha)
      2 angleMeasure := by
  
  let Φ₁ := (Φ.pulledBackTrace Φ.lipschitzDomain) (Submodule.starProjection (h1ResonantSpace Φ.domain E₀) (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀)))
  have heq := regular_observation_sub_ae hΓLip hW (regularHerglotzObservationVector  E₀ W ha) (Φ₁) (localConformalRegularHerglotzObservationVector_cutProj Φ.map hΓLip hW hc ha)
  exact (Lp.memLp (projectedObservationBoundary hΓLip hW (regularHerglotzObservationVector  E₀ W ha) - 2 • (Φ₁))).ae_eq
    (heq.trans (localConformalRegularPeriodicHerglotzExpression_ae Φ hγ hτ hcoord hΓLip hE₀ hW ha).symm)

/-- The ordinary-coordinate L2 class of the actual regular periodic
expression on the genuine variable-speed circle. -/
def ConformalDiskMap.regularPeriodicHerglotzBoundary {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : TransportPath} (hW : IsTransport Φ.boundary E₀ W)
    (hc : cutVector W ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a) : BoundaryL2 :=
  (localConformalRegularPeriodicHerglotzExpression_memLp Φ hγ hτ hcoord hΓLip hE₀ hW hc ha).toLp
    (Φ.regularPeriodicHerglotzExpression Φ.lipschitzDomain hγ hτ E₀ W ha)

theorem localConformalRegularPeriodicHerglotzBoundary_eq {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : TransportPath} (hW : IsTransport Φ.boundary E₀ W)
    (hc : cutVector W ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    Φ.regularPeriodicHerglotzBoundary hγ hτ hcoord hΓLip hE₀ hW hc ha =
        projectedObservationBoundary hΓLip hW (regularHerglotzObservationVector (γ := Φ.boundary) E₀ W ha) - (2 : ℂ) • ((Φ.pulledBackTrace Φ.lipschitzDomain) (Submodule.starProjection (h1ResonantSpace Φ.domain E₀)
  (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀)))) := by
  
  have hz := localConformalRegularHerglotzObservationVector_cutProj Φ.map hΓLip hW hc ha
  exact regular_boundary_toLp_eq _ _
    ((regular_observation_sub_ae hΓLip hW _ ((Φ.pulledBackTrace Φ.lipschitzDomain) (Submodule.starProjection (h1ResonantSpace Φ.domain E₀)
  (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀)))) hz).trans
      (localConformalRegularPeriodicHerglotzExpression_ae Φ hγ hτ hcoord hΓLip hE₀ hW ha).symm)

end

end CoordinatePairing

end ConformalCoordinates

/-! The following computation is on genuine coordinate integrals, with
ordinary measure. In particular it proves the zero Fourier row as well
as every nonzero row, for arbitrary integrable inputs. -/

private theorem regular_sawtooth_measurable :
    Measurable (Function.uncurry sawtoothKernel) := by
  
  exact (measurable_const.mul (Complex.measurable_ofReal.comp
    (measurable_real_sign.comp (measurable_fst.sub measurable_snd)))).sub
    (measurable_const.mul
      (((Complex.measurable_ofReal.comp measurable_fst).sub
        (Complex.measurable_ofReal.comp measurable_snd)).div_const π))

private theorem regular_sawtooth_norm_le {θ s : ℝ}
    (hθ : θ ∈ angleInterval) (hs : s ∈ angleInterval) :
    ‖sawtoothKernel θ s‖ ≤ 3 := by
  have hd : |θ - s| ≤ anglePeriod := abs_le.mpr ⟨by linarith [hθ.1, hs.2],
    by linarith [hθ.2, hs.1]⟩
  have hdiv : |(θ - s) / π| ≤ 2 := by
    rw [abs_div, abs_of_pos pi_pos]
    exact (div_le_iff₀ pi_pos).mpr (by linarith)
  calc
    _ ≤
        ‖Complex.I * (Real.sign _)‖ +
          ‖Complex.I * ((θ - s) / π : ℝ)‖ := by
      simpa [sawtoothKernel] using
        (norm_sub_le (Complex.I * (Real.sign (θ - s) : ℂ))
          (Complex.I * (((θ - s) / π : ℝ) : ℂ)))
    _ = |Real.sign (θ - s)| + |(θ - s) / π| := by
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    _ ≤ 3 := by linarith [abs_real_sign_le (θ - s)]

section

variable (f : BoundaryL2) (n : ℤ) (θ : ℝ) (T : L2Z →L[ℂ] BoundaryL2) (W : TransportPath)

private theorem regular_sawtooth_swap (s : ℝ) :
    sawtoothKernel θ s = -sawtoothKernel s θ := by
  have hs : Real.sign (θ - s) = -Real.sign (s - θ) := by
    rw [← Real.sign_neg, neg_sub]
  simp only [sawtoothKernel, hs, Complex.ofReal_neg]
  ring

private theorem regular_kernel_mode_norm :
    ‖kernelFourierMode n θ‖ = 1 := by
  rw [← fourier_two_pi_eq_kernelFourierMode]
  exact Circle.norm_coe _

private theorem regular_sawtooth_outer_mode {s : ℝ}
    (hs : s ∈ angleInterval) :
    (∫ₚ θ, kernelFourierMode (-n) θ * sawtoothKernel θ s) =
      (2 / (n : ℂ)) * kernelFourierMode (-n) s := by
  have heq : (fun θ => kernelFourierMode (-n) θ * sawtoothKernel θ s) =
      fun θ => -(sawtoothKernel s θ * kernelFourierMode (-n) θ) := by
    funext θ
    rw [regular_sawtooth_swap]
    ring
  rw [heq, intervalIntegral.integral_neg]
  by_cases hn : n = 0
  · subst n
    simp only [neg_zero, kernelFourierMode, Int.cast_zero, zero_mul,
      Complex.exp_zero, mul_one, div_zero, zero_mul]
    rw [integral_sawtoothKernel hs, neg_zero]
  · rw [show (∫ₚ θ,
        sawtoothKernel s θ * kernelFourierMode (-n) θ) =
        2 / (-n : ℤ) * kernelFourierMode (-n) s from
        integral_sawtoothKernel_mul_exp hs (neg_ne_zero.mpr hn)]
    simp [div_neg]

/-- The genuine sawtooth integral has multiplier `2/n` on every
Fourier coefficient of an arbitrary L1 input. At `n=0` the result is
exactly zero; the normalization remains `1/(2π)`. -/
theorem fourierCoeffOn_sawtoothAction {f : ℝ → ℂ}
    (hf : Integrable f angleMeasure) (n : ℤ) :
    angleCoeff
      (fun θ => ∫ₚ s, sawtoothKernel θ s * f s) n =
        (2 / (n : ℂ)) * angleCoeff f n := by
  let μ  := angleMeasure
  
  have hint : Integrable (fun p : ℝ × ℝ =>
      kernelFourierMode (-n) p.1 * sawtoothKernel p.1 p.2 * f p.2) (μ.prod μ) := by
    refine ((hf.norm.comp_snd μ).const_mul 3).mono' ((((show Continuous (fun p : ℝ × ℝ => kernelFourierMode (-n) p.1) by
        unfold kernelFourierMode; fun_prop).measurable.aestronglyMeasurable.mul
        regular_sawtooth_measurable.aestronglyMeasurable).mul
        hf.aestronglyMeasurable.comp_snd)) ?_
    
    filter_upwards [(by
      
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc))] with p hp
    simp [regular_kernel_mode_norm]
    exact mul_le_mul_of_nonneg_right
      (regular_sawtooth_norm_le (Ioc_subset_Icc_self hp.1)
        (Ioc_subset_Icc_self hp.2)) (norm_nonneg _)
  have hmode (θ : ℝ) :
      Complex.exp (anglePeriod * Complex.I * (-n : ℤ) * θ / (anglePeriod : ℝ)) =
        kernelFourierMode (-n) θ := by
    simpa only [fourier_coe_apply] using fourier_two_pi_eq_kernelFourierMode (-n) θ
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp_rw [fourier_coe_apply]
  simp only [sub_zero, Complex.real_smul, smul_eq_mul]
  simp_rw [hmode]
  push_cast
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  
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
      fun s => (2 / n) * (kernelFourierMode (-n) s * f s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [integral_mul_const]
    have hmode := regular_sawtooth_outer_mode n (Ioc_subset_Icc_self hs)
    rw [intervalIntegral.integral_of_le two_pi_pos.le] at hmode
    
    rw [hmode]
    ring
  rw [integral_congr_ae heq, integral_const_mul]
  ring

/-- The genuine sawtooth action of any L1 input is L2 on the finite
parameter interval. This follows from its actual integral bound. -/
theorem memLp_sawtoothAction {f : ℝ → ℂ}
    (hf : Integrable f angleMeasure) :
    MemLp (fun θ => ∫ₚ s, sawtoothKernel θ s * f s) 2
      angleMeasure := by
  let μ  := angleMeasure
  
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound ((regular_sawtooth_measurable.aestronglyMeasurable.mul
    hf.aestronglyMeasurable.comp_snd).integral_prod_right') (3 * ∫ s, ‖f s‖ ∂μ) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc
    _ ≤ ∫ s, 3 * ‖f s‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul 3)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (regular_sawtooth_norm_le (Ioc_subset_Icc_self hθ)
          (Ioc_subset_Icc_self hs)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

include f in
/-- The actual sawtooth boundary vector for an arbitrary L2 input. -/
def sawtoothBoundaryAction : BoundaryL2 :=
  (memLp_sawtoothAction ((Lp.memLp f).integrable (by norm_num))).toLp _

theorem sawtoothBoundaryAction_fourier :
    boundaryFourier (sawtoothBoundaryAction f) n =
      (2 / (n : ℂ)) * boundaryFourier f n := by
  rw [boundaryFourier_apply, boundaryFourier_apply]
  have hf := (Lp.memLp f).integrable (by norm_num)
  
  rw [fourierCoeffOn_congr_ae two_pi_pos (by
    exact MemLp.coeFn_toLp (memLp_sawtoothAction hf)), fourierCoeffOn_sawtoothAction hf]
  ring

private theorem regular_half_weight_square :
    ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
        ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) * (sobWeight n : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Real.rpow_add (sobWeight_pos n)]
  norm_num
  rw [Real.rpow_neg_one, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (sobWeight_pos n).ne', Complex.ofReal_one]

/-- This actual bounded composition is the raw inverse derivative.
Its equality with the sawtooth integral is proved below, on all L2. -/
def regularRawInverseDerivative : FourierOp :=
  (sobolevSmoothing (1 / 2) (by norm_num)).comp
    ((principalNormalized - (2 : ℂ) • normalizedInverseAbsOperator).comp
      (sobolevSmoothing (1 / 2) (by norm_num)))

theorem regularRawInverseDerivative_apply (f : L2Z) (n : ℤ) :
    regularRawInverseDerivative f n = (2 / (n : ℂ)) * f n := by
  simp only [regularRawInverseDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    principalNormalized, normalizedInverseAbsOperator_apply, sobolevSmoothing, diagOp_apply]
  by_cases hn : n = 0
  · subst n
    simp [principalSymbol, normalizedInverseAbsSymbol]
  · have hsymbol : principalSymbol n - 2 * normalizedInverseAbsSymbol n =
        (sobWeight n) * (2 / n) := by
      simp only [principalSymbol, normalizedInverseAbsSymbol, if_neg hn]
      push_cast
      ring
    calc
      _ = ((sobWeight n ^ (-halfOrder) : ℝ) *
          (sobWeight n ^ (-halfOrder) : ℝ)) *
          (principalSymbol n - 2 * normalizedInverseAbsSymbol n) * f n := by ring
      _ = ((sobWeight n ^ (-halfOrder) : ℝ) *
          (sobWeight n ^ (-halfOrder) : ℝ) * (sobWeight n)) *
          (2 / n) * f n := by rw [hsymbol]; ring
      _ = _ := by rw [regular_half_weight_square, one_mul]

private theorem regular_half_sqrt_cancel :
    ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
      (Real.sqrt (sobWeight n) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, Real.sqrt_eq_rpow,
    ← Real.rpow_add (sobWeight_pos n)]
  norm_num

theorem regular_halfSmoothing_injective :
    Function.Injective (sobolevSmoothing (1 / 2) (by norm_num) : FourierOp) := by
  intro f g h
  ext n
  
  
  have hw : (((sobWeight n ^ (-halfOrder) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) _).ne'
  exact mul_left_cancel₀ hw (congrArg (fun v : L2Z => v n) h)

/-- Half smoothing of the actual normalized projected-observation
adjoint is exactly the ordinary unitary Fourier observation trace. -/
theorem halfSmoothing_adjoint_projObsDual
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : TransportPath}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (z : Ell2) :
    sobolevSmoothing (1 / 2) (by norm_num)
      ((√anglePeriod : ℂ) • ContinuousLinearMap.adjoint (projObsDual W) z) =
        boundaryFourier (projectedObservationBoundary hK hW z) := by
  rw [projObsDual_eq hK hW, rowSynth, ContinuousLinearMap.adjoint_adjoint]
  ext n
  simp only [sobolevSmoothing, diagOp_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, rowAnalysis_apply, normProjObsRow, inner_smul_left,
    Complex.conj_ofReal, boundaryFourier_projectedObservation]
  change (sobWeight n ^ (-halfOrder) : ℝ) *
    (√anglePeriod * ((Real.sqrt (sobWeight n)) * ⟪projObsCoeffVec W n, z⟫_ℂ)) = _
  calc
    _ = ((sobWeight n ^ (-halfOrder) : ℝ) *
      (Real.sqrt (sobWeight n))) *
      (√anglePeriod * ⟪projObsCoeffVec W n, z⟫_ℂ) := by ring
    _ = _ := by rw [regular_half_sqrt_cancel, one_mul]

/-- The bounded boundary operator obtained from the genuine raw Fourier
multiplier. It equals the original coordinate sawtooth integral on all L2. -/
def sawtoothBoundaryOperator : BoundaryL2 →L[ℂ] BoundaryL2 :=
  boundaryFourier.symm.toLinearIsometry.toContinuousLinearMap.comp
    (regularRawInverseDerivative.comp boundaryFourier.toLinearIsometry.toContinuousLinearMap)

theorem sawtoothBoundaryOperator_eq_action :
    sawtoothBoundaryOperator f = sawtoothBoundaryAction f := by
  apply boundaryFourier.injective
  ext n
  change boundaryFourier (boundaryFourier.symm
    (regularRawInverseDerivative (boundaryFourier f))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply, regularRawInverseDerivative_apply,
    sawtoothBoundaryAction_fourier]

/-- The corrected integral operator on ordinary boundary L2, transported
through the actual unitary circle lift. Both maps use their true measures. -/
def regularCorrectedBoundaryOperator {γ : ℝ → ℂ} {K : NNReal} {E : ℝ}
    {W : TransportPath} (hK : LipschitzWith K γ)
    (hW : IsTransport γ E W) (hc : cutVector W ≠ 0) :
    BoundaryL2 →L[ℂ] BoundaryL2 :=
  boundaryCircleUnitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((correctedKernelL2Op hK hW hc).comp
      boundaryCircleUnitary.toLinearIsometry.toContinuousLinearMap)

theorem regularCorrectedBoundaryOperator_fourier
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : TransportPath}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutVector W ≠ 0)
    (hr : Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2)
    (f : BoundaryL2) :
    boundaryFourier (regularCorrectedBoundaryOperator hK hW hc f) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr (boundaryFourier f) := by
  change (fourierBasis (T := anglePeriod)).repr
    (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hK hW hc (boundaryCircleUnitary f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,
    correctedKernelL2Op_fourier_action hK hW hc hr]
  rfl

/-- Raw square summability follows from the genuine normalized matrix
bound, without an arclength hypothesis on the conformal parameter. -/
theorem summable_regularKernelIntegralMatrix
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (by norm_num) (fun p => ?_) hbase
  have hm : 1 ≤ (sobWeight p.1) ^ halfOrder :=
    Real.one_le_rpow (one_le_sobWeight p.1) (by norm_num)
  have hn : 1 ≤ (sobWeight p.2) ^ halfOrder :=
    Real.one_le_rpow (one_le_sobWeight p.2) (by norm_num)
  
  have heq : correctedRemainderMatrix W 0 0 p =
      (((sobWeight p.1) ^ halfOrder *
        (sobWeight p.2) ^ halfOrder : ℝ) : ℂ) *
        kernelIntegralMatrix (r := correctedKernel W) p := by
    simp only [correctedRemainderMatrix, kernelIntegralMatrix, sobWeight,
      mul_zero, add_zero, sub_zero, Complex.ofReal_mul]
    push_cast
    ring
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  simpa using mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hm hn) (norm_nonneg _)

theorem memLp_regularCorrectedAction
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : TransportPath}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {f : ℝ → ℂ}
    (hf : Integrable f angleMeasure) :
    MemLp (fun θ => ∫ₚ s, correctedKernel W θ s * f s) 2
      angleMeasure := by
  let μ  := angleMeasure
  
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound (((aestronglyMeasurable_correctedKernel hW).mul
    hf.aestronglyMeasurable.comp_snd).integral_prod_right') ((4 + ‖cutBE W‖) * ∫ s, ‖f s‖ ∂μ) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc
    _ ≤
        ∫ s, (4 + ‖cutBE W‖) * ‖f s‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul _)
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
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : TransportPath}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutVector W ≠ 0)
    (g : BoundaryL2) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ}
    (hfB : ∀ s, ‖f s‖ ≤ B)
    (hgf : (g : ℝ → ℂ) =ᵐ[angleMeasure] f) (n : ℤ) :
    boundaryFourier (regularCorrectedBoundaryOperator hK hW hc g) n =
      (√anglePeriod : ℂ) * angleCoeff
        (fun θ => ∫ₚ s, correctedKernel W θ s * f s) n := by
  let fC  := (memLp_liftIco_two_pi hf hfB).toLp _
  have hcircle : boundaryCircleLift g = fC := by
    apply Lp.ext
    exact (boundaryCircleLift_coe g).trans
      (((boundary_liftIoc_congr_ae hgf).trans
        (boundary_liftIoc_eq_liftIco_ae f)).trans
          (MemLp.coeFn_toLp (memLp_liftIco_two_pi hf hfB)).symm)
  change (fourierBasis (T := anglePeriod)).repr
    (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hK hW hc (boundaryCircleUnitary g)))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (fourierBasis (T := anglePeriod)).repr
    (correctedKernelL2Op hK hW hc ((√anglePeriod : ℂ) • boundaryCircleLift g)) n = _
  rw [hcircle, map_smul, map_smul]
  change (√anglePeriod : ℂ) *
    (fourierBasis (T := anglePeriod)).repr (correctedKernelL2Op hK hW hc fC) n = _
  rw [correctedKernelL2Op_toLp_fourier hK hW hc hf hfB]

private theorem regular_boundary_operator_sum_apply
    (T A B : BoundaryL2 →L[ℂ] BoundaryL2) (g : BoundaryL2) :
    ((2 : ℂ) • T + A + B) g = (2 : ℂ) • T g + A g + B g := by
  simp

private theorem regular_boundary_ae_of_eq (u v : BoundaryL2) {f : ℝ → ℂ}
    (huv : u = v)
    (hv : (v : ℝ → ℂ) =ᵐ[angleMeasure] f) :
    (u : ℝ → ℂ) =ᵐ[angleMeasure] f := by
  subst u
  exact hv

private theorem regular_boundary_eq_of_periodic_load_eq
    (b d : L2Z) (hbd : b = d) (f : ℝ → ℂ) (u v : BoundaryL2)
    (hu : (u : ℝ → ℂ) =ᵐ[angleMeasure]
      periodicP W (T b : ℝ → ℂ) f)
    (hv : (v : ℝ → ℂ) =ᵐ[angleMeasure]
      periodicP W (T d : ℝ → ℂ) f) : u = v := by
  subst b
  exact Lp.ext (hu.trans hv.symm)

end

private theorem regular_boundary_smoothing_difference
    (S : FourierOp) (x q : L2Z) (p r : BoundaryL2)
    (hx : S x = boundaryFourier p) (hq : S q = boundaryFourier r) :
    S (x - (2 : ℂ) • q) = boundaryFourier (p - (2 : ℂ) • r) := by
  rw [map_sub, map_smul, map_sub, map_smul, hx, hq]

private theorem regular_boundary_periodic_sum_ae
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : TransportPath}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutVector W ≠ 0)
    (t g : BoundaryL2) {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ}
    (hfB : ∀ s, ‖f s‖ ≤ B)
    (hgf : (g : ℝ → ℂ) =ᵐ[angleMeasure] f) :
    (((2 : ℂ) • t + sawtoothBoundaryOperator g +
      regularCorrectedBoundaryOperator hK hW hc g : BoundaryL2) : ℝ → ℂ) =ᵐ[
        angleMeasure] periodicP W (t : ℝ → ℂ) f := by
  
  have hfI := ((Lp.memLp g).ae_eq hgf).integrable (by norm_num)
  let k  := (memLp_regularCorrectedAction hK hW hfI).toLp _
  have hk : regularCorrectedBoundaryOperator hK hW hc g = k := by
    apply boundaryFourier.injective
    ext n
    rw [regularCorrectedBoundaryOperator_toLp_fourier hK hW hc g hf.measurable hfB hgf,
      boundaryFourier_apply]
    congr 1
    exact (congrFun (fourierCoeffOn_congr_ae two_pi_pos
      (MemLp.coeFn_toLp _)) n).symm
  have hsaw (θ : ℝ) :
      (∫ₚ s, sawtoothKernel θ s * g s) =
        ∫ₚ s, sawtoothKernel θ s * f s := by
    simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
    apply integral_congr_ae
    filter_upwards [hgf] with s hs
    rw [hs]
  rw [sawtoothBoundaryOperator_eq_action, hk]
  filter_upwards [Lp.coeFn_add _ k,
    Lp.coeFn_add _ (sawtoothBoundaryAction g), Lp.coeFn_smul (2 : ℂ) t,
    MemLp.coeFn_toLp (memLp_sawtoothAction
      ((Lp.memLp g).integrable (by norm_num))),
    MemLp.coeFn_toLp (memLp_regularCorrectedAction hK hW hfI),
    ae_restrict_mem measurableSet_Ioc] with θ ha hb hc' hs hk' hθ
  rw [ha, Pi.add_apply, hb, Pi.add_apply, hc', Pi.smul_apply, smul_eq_mul]
  dsimp [sawtoothBoundaryAction, k]
  rw [hs, hk', hsaw]
  exact (periodicP_eq_doubleTrace_add_kernel_integrals hW.1 t
    hf hfB (Ioc_subset_Icc_self hθ)).symm

section ActualPeriodicOperator

section

variable (Φ : SmoothDiskMap) (hL : IsLipschitzDomain Φ.domain) (E₀ E : ℝ)
include hL

theorem localConformal_halfSmoothing_halfTrace (u : NeumannH1 Φ.domain) :
    sobolevSmoothing (1 / 2) (by norm_num) ((Φ.pulledBackHalfTrace hL) u) = boundaryFourier ((Φ.pulledBackTrace hL) u) := by
  ext n
  
  have hw : sobWeight n ^ (-halfOrder) * Real.sqrt (sobWeight n) = 1 := by
    rw [Real.sqrt_eq_rpow, mul_comm, sobWeight_rpow_mul_neg]
  change ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
    ((Real.sqrt (sobWeight n) : ℂ) * boundaryFourier ((Φ.pulledBackTrace hL) u) n) = _
  rw [← mul_assoc, ← Complex.ofReal_mul, hw, Complex.ofReal_one, one_mul]

include E₀ in
/-- The genuine regular trace, the original sawtooth integral, and the
actual corrected boundary kernel form this bounded coordinate operator.
The normalization identity is proved next, rather than used to define it. -/
def SmoothDiskMap.regularPeriodicOperator {γ : ℝ → ℂ} {K : NNReal} {W : TransportPath}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (hc : cutVector W ≠ 0) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  (2 : ℂ) • ((Φ.pulledBackTrace hL).comp
    ((h1RegularResolvent Φ.domain E₀ E).comp
    ((ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL)).comp
      ((sobolevSmoothing (1 / 2) (by norm_num)).comp
        boundaryFourier.toLinearIsometry.toContinuousLinearMap)))) +
    sawtoothBoundaryOperator + regularCorrectedBoundaryOperator hK hW hc

/-- The actual bounded operator agrees with the assembled normalized
regular Fourier operator on every L2 load, including its constant mode. -/
theorem localConformalRegularPeriodicOperator_fourier {γ : ℝ → ℂ} {K : NNReal} {W : TransportPath}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (hc : cutVector W ≠ 0)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) (f : BoundaryL2) :
    boundaryFourier (Φ.regularPeriodicOperator hL E₀ E hK hW hc f) =
      sobolevSmoothing (1 / 2) (by norm_num)
        (normalizedPeriodicRegularOperator (Φ.pulledBackHalfTrace hL) E₀ E W hbase
          (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier f))) := by
  let S : FourierOp := sobolevSmoothing (1 / 2) (by norm_num)
  let b : L2Z := S (boundaryFourier f)
  let u : NeumannH1 Φ.domain :=
    h1RegularResolvent Φ.domain E₀ E (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL) b)
  let hr := summable_regularKernelIntegralMatrix W hbase
  have hN : S (normalizedNeumannRegular (Φ.pulledBackHalfTrace hL) E₀ E b) = boundaryFourier ((Φ.pulledBackTrace hL) u) := by
    exact localConformal_halfSmoothing_halfTrace Φ hL u
  have hS : boundaryFourier (sawtoothBoundaryOperator f) =
      regularRawInverseDerivative (boundaryFourier f) := by
    change boundaryFourier (boundaryFourier.symm
      (regularRawInverseDerivative (boundaryFourier f))) = _
    exact LinearIsometryEquiv.apply_symm_apply _ _
  have hKern := regularCorrectedBoundaryOperator_fourier hK hW hc hr f
  have hraw : regularRawInverseDerivative (boundaryFourier f) =
      S (principalNormalized b) - (2 : ℂ) • S (normalizedInverseAbsOperator b) := by
    simp only [regularRawInverseDerivative, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul]
    rfl
  have hHS : S (hsMatrixOp (correctedRemainderMatrix W 0 0) hbase b) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr (boundaryFourier f) :=
    correctedRemainderOp_half_smoothing W hbase hr (boundaryFourier f)
  change boundaryFourier ((2 : ℂ) • (Φ.pulledBackTrace hL) u + sawtoothBoundaryOperator f +
    regularCorrectedBoundaryOperator hK hW hc f) =
    S (normalizedPeriodicRegularOperator (Φ.pulledBackHalfTrace hL) E₀ E W hbase b)
  rw [map_add, map_add, map_smul, hS, hKern, hraw]
  simp only [normalizedPeriodicRegularOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    map_add, map_smul, map_sub, smul_sub, hN, hHS]
  abel

/-- The bounded operator's output is the actual pointwise periodic
expression on every continuous bounded coordinate load. Its trace input
is the original regular Neumann solution, rather than a stipulated form. -/
theorem localConformalRegularPeriodicOperator_apply_ae {γ : ℝ → ℂ} {K : NNReal} {W : TransportPath}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (hc : cutVector W ≠ 0)
    (g : BoundaryL2) {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ} (hfB : ∀ s, ‖f s‖ ≤ B)
    (hgf : (g : ℝ → ℂ) =ᵐ[angleMeasure] f) :
    (Φ.regularPeriodicOperator hL E₀ E hK hW hc g : ℝ → ℂ)
      =ᵐ[angleMeasure]
        periodicP W
          ((Φ.pulledBackTrace hL) (h1RegularResolvent Φ.domain E₀ E (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL)
            (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)))) : ℝ → ℂ) f := by
  let t  := (Φ.pulledBackTrace hL) (h1RegularResolvent Φ.domain E₀ E (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL)
    (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g))))
  have hop : Φ.regularPeriodicOperator hL E₀ E hK hW hc g =
      (2 : ℂ) • t + sawtoothBoundaryOperator g +
        regularCorrectedBoundaryOperator hK hW hc g := by
    have h_simpa := regular_boundary_operator_sum_apply
      ((Φ.pulledBackTrace hL).comp
      ((h1RegularResolvent Φ.domain E₀ E).comp
      ((ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL)).comp
      ((sobolevSmoothing (1 / 2) (by norm_num)).comp
      boundaryFourier.toLinearIsometry.toContinuousLinearMap))))
      sawtoothBoundaryOperator (regularCorrectedBoundaryOperator hK hW hc) g
    
    exact h_simpa
  exact regular_boundary_ae_of_eq _ _ hop
    (regular_boundary_periodic_sum_ae hK hW hc t g hf hfB hgf)

end

end ActualPeriodicOperator

section ActualHerglotzMatching

section

variable (Φ : ConformalDiskMap)

private theorem regular_continuous_coordinateConormal (Φ : SmoothDiskMap) {a : ℝ → ℂ}
    (ha : IsDirDensity a) (k : ℝ) :
    Continuous (herglotzConormal k a Φ.boundary) := by
  have hΓ := Φ.boundaryC1
  
  rw [(funext (herglotzConormal_eq ha.intervalIntegrable k Φ.boundary))]
  exact continuous_const.mul
    (((Complex.continuous_conj.comp hΓ.continuous_deriv_one).mul
      ((continuous_herglotzCoeff ha.intervalIntegrable k (-1)).comp hΓ.continuous)).sub
    (hΓ.continuous_deriv_one.mul
      ((continuous_herglotzCoeff ha.intervalIntegrable k 1).comp hΓ.continuous)))

/-- Applying the genuine bounded coordinate operator to the actual
Herglotz conormal gives exactly the previously derived physical regular
periodic expression. The resonant subtraction is therefore preserved. -/
theorem localConformalRegularPeriodicOperator_herglotz {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {K : NNReal}
    (hΓLip : LipschitzWith K Φ.boundary) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : TransportPath} (hW : IsTransport Φ.boundary E₀ W)
    (hc : cutVector W ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    Φ.regularPeriodicOperator Φ.lipschitzDomain E₀ E₀ hΓLip hW hc
      (localConformalHerglotzCoordinateLoad Φ.map hΓLip ha (Real.sqrt E₀)) =
        Φ.regularPeriodicHerglotzBoundary hγ hτ hcoord hΓLip hE₀ hW hc ha := by
  obtain ⟨_, B, hfB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E₀) hΓLip
  have hop := localConformalRegularPeriodicOperator_apply_ae Φ Φ.lipschitzDomain E₀ E₀ hΓLip hW hc
    _
    (regular_continuous_coordinateConormal Φ ha (Real.sqrt E₀)) hfB
    (localConformalHerglotzCoordinateLoad_ae Φ.map hΓLip ha (Real.sqrt E₀))
  have hload := localConformalHerglotzBoundaryLoad_eq_coordinateLoad Φ.map hγ hτ hcoord
    hΓLip ha (Real.sqrt E₀)
  let T  :=
    (Φ.pulledBackTrace Φ.lipschitzDomain).comp
      ((h1RegularResolvent Φ.domain E₀ E₀).comp
        (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace Φ.lipschitzDomain)))
  have hbdy : (Φ.regularPeriodicHerglotzBoundary hγ hτ hcoord hΓLip hE₀ hW hc ha)
      =ᵐ[angleMeasure]
        Φ.regularPeriodicHerglotzExpression Φ.lipschitzDomain hγ hτ E₀ W ha :=
    MemLp.coeFn_toLp (localConformalRegularPeriodicHerglotzExpression_memLp
      Φ hγ hτ hcoord hΓLip hE₀ hW hc ha)
  have hopT := hop
  have hbdyT := hbdy
  exact regular_boundary_eq_of_periodic_load_eq T W _ _ hload.symm
    _ _ _ hopT hbdyT

/-- The assembled normalized operator is now matched to the actual
regular periodic Herglotz expression, with ordinary boundary Fourier
normalization sqrt(2π). There is no discarded zero Fourier coefficient. -/
theorem normalizedPeriodicRegularOperator_herglotz_fourier {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {K : NNReal}
    (hΓLip : LipschitzWith K Φ.boundary) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : TransportPath} (hW : IsTransport Φ.boundary E₀ W)
    (hc : cutVector W ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    sobolevSmoothing (1 / 2) (by norm_num)
      (normalizedPeriodicRegularOperator (Φ.pulledBackHalfTrace Φ.lipschitzDomain)
        E₀ E₀ W hbase (localConformalBoundaryLoad hτ
          (herglotzConormalL2 hγ ha (Real.sqrt E₀)))) =
      boundaryFourier (Φ.regularPeriodicHerglotzBoundary hγ hτ hcoord hΓLip hE₀ hW hc ha) := by
  rw [localConformalHerglotzBoundaryLoad_eq_coordinateLoad Φ.map hγ hτ hcoord hΓLip ha, ← localConformalRegularPeriodicOperator_fourier Φ Φ.lipschitzDomain E₀ E₀ hΓLip hW hc hbase,
    localConformalRegularPeriodicOperator_herglotz Φ hγ hτ hcoord hΓLip hE₀ hW hc ha]

/-- The full normalized regular expression on genuine Herglotz data is
the true projected-observation adjoint minus twice the original resonant
half-trace. Half smoothing is canceled using its genuine injectivity. -/
theorem normalizedPeriodicRegularOperator_herglotz_eq {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {K : NNReal}
    (hΓLip : LipschitzWith K Φ.boundary) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : TransportPath} (hW : IsTransport Φ.boundary E₀ W)
    (hc : cutVector W ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    normalizedPeriodicRegularOperator (Φ.pulledBackHalfTrace Φ.lipschitzDomain)
        E₀ E₀ W hbase (localConformalBoundaryLoad hτ
          (herglotzConormalL2 hγ ha (Real.sqrt E₀))) =
      (√anglePeriod : ℂ) • ContinuousLinearMap.adjoint (projObsDual W)
        (regularHerglotzObservationVector (γ := Φ.boundary) E₀ W ha) -
      (2 : ℂ) • Φ.pulledBackHalfTrace Φ.lipschitzDomain
        ((h1ResonantSpace Φ.domain E₀).starProjection
          (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀))) := by
  apply regular_halfSmoothing_injective
  
  
  have hsm := regular_boundary_smoothing_difference
    _ _ _ _ _
    (halfSmoothing_adjoint_projObsDual hΓLip hW
      (regularHerglotzObservationVector (γ := Φ.boundary) E₀ W ha))
    (localConformal_halfSmoothing_halfTrace Φ Φ.lipschitzDomain
      ((h1ResonantSpace Φ.domain E₀).starProjection
        (herglotzWaveH1 Φ.bounded ha (Real.sqrt E₀))))
  exact (normalizedPeriodicRegularOperator_herglotz_fourier
    Φ hγ hτ hcoord hΓLip hE₀ hW hc ha hbase).trans ((congrArg (boundaryFourier) (localConformalRegularPeriodicHerglotzBoundary_eq
    Φ hγ hτ hcoord hΓLip hE₀ hW hc ha)).trans hsm.symm)

end

end ActualHerglotzMatching

end PolyaNeumann

end
