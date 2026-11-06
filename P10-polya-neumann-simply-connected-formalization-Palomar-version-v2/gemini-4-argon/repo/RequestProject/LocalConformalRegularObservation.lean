module

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


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Metric Real Filter
open scoped Real InnerProductSpace ComplexConjugate ContDiff

variable {a : ℝ → ℂ} {γ : ℝ → ℂ} {K : NNReal} {L : NNReal} {E : ℝ}

local instance regularObservationTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The actual corrected initial Herglotz vector. Both the initial jet
and the finite cut correction retain their original normalizations. -/
def regularHerglotzObservationVector  (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2)  (ha : IsDirDensity a) : Ell2 :=
  (Real.sqrt 2 : ℂ) •
      (herglotzVec ha (Real.sqrt E) (γ 0) +
        ContinuousLinearMap.adjoint (W (2 * π))
          (herglotzVec ha (Real.sqrt E) (γ 0))) +
    cutBE W (observationAdj W (herglotzConormal (Real.sqrt E) a γ))

/-- The corrected expression of a genuine wave is its actual corrected
observation, before the genuine resonant trace is removed. -/
theorem periodicP_herglotz_eq_regularObservation  
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) 
     (hW : IsTransport γ E W)
     (ha : IsDirDensity a)  (hθ : θ ∈ Icc 0 (2 * π)) :
    periodicP W (fun s => herglotzWave (Real.sqrt E) a (γ s))
        (herglotzConormal (Real.sqrt E) a γ) θ =
      observation W (regularHerglotzObservationVector (γ := γ) E W ha) θ := by
  rw [periodicP, periodicA_herglotz_eq_observation hK hclosed hW ha hθ]
  simp only [regularHerglotzObservationVector, cutBE, observation,
    map_add, inner_add_right]

theorem regularHerglotzObservationVector_cutProj
      (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) 
     (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
     (ha : IsDirDensity a) :
    cutProj (cutC (W (2 * π)) (basisVec 0))
        (regularHerglotzObservationVector (γ := γ) E W ha) =
      regularHerglotzObservationVector (γ := γ) E W ha := by
  rw [cutProj_eq_starProjection, Submodule.starProjection_eq_self_iff,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact (by
    obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
    have hp := periodicP_periodic (n := fun s => herglotzWave (Real.sqrt E) a (γ s))
      hK hW hc (by
        change herglotzWave (Real.sqrt E) a (γ (2 * π)) = _
        rw [hclosed]) hgm hgB
    rw [periodicP_herglotz_eq_regularObservation hK hclosed hW ha
          ⟨two_pi_pos.le, le_rfl⟩,
      periodicP_herglotz_eq_regularObservation hK hclosed hW ha
          ⟨le_rfl, two_pi_pos.le⟩] at hp
    rw [← observation_jump hW]
    exact sub_eq_zero.mpr hp)

local notation "Φ1" => Ioc 0

private theorem regular_boundary_sub_ae (u v : BoundaryL2) {f : ℝ → ℂ}
    (hf : u =ᵐ[volume.restrict (Φ1 (2 * π))] f) :
    ((u - v : BoundaryL2) : ℝ → ℂ) =ᵐ[volume.restrict (Φ1 (2 * π))]
      fun θ => f θ - v θ := by
  filter_upwards [Lp.coeFn_sub u v, hf] with θ hs hw
  rw [hs, Pi.sub_apply, hw]

private theorem regular_observation_sub_ae  
    (hK : LipschitzWith K γ)  {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (z : Ell2) (r : BoundaryL2)
    (hz : cutProj (cutC (W (2 * π)) (basisVec 0)) z = z) :
    ((projectedObservationBoundary hK hW z - (2 : ℂ) • r : BoundaryL2) : ℝ → ℂ)
      =ᵐ[volume.restrict (Φ1 (2 * π))]
        fun θ => observation W z θ - 2 * r θ := by
  filter_upwards [Lp.coeFn_sub (projectedObservationBoundary hK hW z) ((2 : ℂ) • r),
    Lp.coeFn_smul (2 : ℂ) r, projectedObservationBoundary_coe hK hW z]
      with θ hs h2 ho
  rw [hs, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, ho,
    ← observation_cutProj_eq, hz]

private theorem regular_boundary_toLp_eq {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Φ1 (2 * π)))) (u : BoundaryL2)
    (hu : (u : ℝ → ℂ) =ᵐ[volume.restrict (Φ1 (2 * π))] f) :
    hf.toLp f = u := by
  apply Lp.ext
  exact hf.coeFn_toLp.trans hu.symm



/-- The positive Jacobian makes the supplied trace reparametrization
preserve null sets on the actual cut. This is proved by change of
variables, even for a property with no chosen measurable representative. -/
theorem isC1TraceReparam_ae_comp {τ : ℝ → ℝ} 
    (hτ : IsC1TraceReparam τ c) {p : ℝ → Prop}
    (hp : ∀ᵐ s ∂volume.restrict (Φ1 (2 * π)), p s) :
    ∀ᵐ θ ∂volume.restrict (Φ1 (2 * π)), p (τ θ) := by
  classical
  let q : ℝ → ℝ := fun s => if p s then 0 else 1
  have hqzero : q =ᵐ[volume.restrict (Φ1 (2 * π))] 0 := by
    filter_upwards [hp] with s hs
    simp [q, if_pos hs]
  have himage : τ '' Icc (0 : ℝ) (2 * π) = Icc (0 : ℝ) (2 * π) := by
    simpa [hτ.zero, hτ.endpoint] using
      hτ.continuous.continuousOn.image_Icc_of_monotoneOn two_pi_pos.le
        (hτ.monotone.monotoneOn _)
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun θ => mul_nonneg hτ.monotone.deriv_nonneg (by simp [q]; split_ifs <;> norm_num)) (show IntegrableOn (fun θ => deriv τ θ * q (τ θ)) (Φ1 (2 * π)) by
    simpa using
      (integrableOn_Icc_iff_integrableOn_Ioc
        (f := fun θ => deriv τ θ • q (τ θ)) (by finiteness)).mp ((integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Icc (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt) (hτ.monotone.monotoneOn (Icc 0 (2 * π))) q).mp (by simpa [himage] using ((integrableOn_Icc_iff_integrableOn_Ioc (f := q) (by finiteness)).mpr ((MeasureTheory.integrable_zero ℝ ℝ (volume.restrict (Φ1 (2 * π)))).congr hqzero.symm)))))).mp (by
    have heq : (∫ θ in Φ1 (2 * π), deriv τ θ * q (τ θ)) =
        ∫ s in Φ1 (2 * π), q s := by
      simpa [himage, integral_Icc_eq_integral_Ioc] using (integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Icc (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt) (hτ.monotone.monotoneOn (Icc 0 (2 * π))) q).symm
    rw [heq, integral_congr_ae hqzero]
    simp), ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hτ.lower_ae] with θ hzero hlower
  by_contra hbad
  exact (hτ.lower_pos.trans_le hlower).ne' (by
    simpa [q, if_neg hbad] using hzero)

/-- Actual variable-speed coordinate conormal, as an ordinary L2 class. -/
def localConformalHerglotzCoordinateLoad F 
    (hΓLip : LipschitzWith L (physicalCircleTrace F))
     (ha : IsDirDensity a) (k : ℝ) : BoundaryL2 :=
  (memLp_herglotzConormal ha k hΓLip).toLp
    (herglotzConormal k a (physicalCircleTrace F))

theorem localConformalHerglotzCoordinateLoad_ae (F : ℂ → ℂ) 
    (hΓLip : LipschitzWith L (physicalCircleTrace F))
     (ha : IsDirDensity a) (k : ℝ) :
    (localConformalHerglotzCoordinateLoad F hΓLip ha k : ℝ → ℂ)
      =ᵐ[volume.restrict (Φ1 (2 * π))]
        herglotzConormal k a (physicalCircleTrace F) :=
  (memLp_herglotzConormal ha k hΓLip).coeFn_toLp

section ConformalCoordinates

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball 0 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball 0 1
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "TF" => localConformalDiskH1Trace hR F hFs hL

include hhol hinj hC hcoord

/-- The actual H1 regular solution itself is the wave minus its true
resonant component. This is stronger than a Fourier trace equality. -/
theorem localConformal_regularHerglotz_coordinate_trace_eq
     (hE₀ : 0 ≤ E₀)  (ha : IsDirDensity a) :
    TF (h1RegularResolvent ΩF E₀ E₀
      (ContinuousLinearMap.adjoint QF
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))))) =
      TF (herglotzWaveH1 hb ha (Real.sqrt E₀)) -
        TF ((h1ResonantSpace ΩF E₀).starProjection (herglotzWaveH1 hb ha (Real.sqrt E₀))) := by
  have h_inl : h1RegularResolvent ΩF E₀ E₀ (ContinuousLinearMap.adjoint QF (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀)))) = herglotzWaveH1 hb ha (Real.sqrt E₀) - (h1ResonantSpace ΩF E₀).starProjection (herglotzWaveH1 hb ha (Real.sqrt E₀)) := by
    rw [← (isNormalizedNeumannSolution_iff QF E₀ _ _).mp (localConformalHerglotz_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE₀ ha), h1RegularResolvent_form_at_reference hb hL hE₀,
      Submodule.starProjection_orthogonal_val]
  rw [h_inl, map_sub]

include hγ hτ in
/-- The genuine Herglotz H1 vector has its actual variable-speed circle
trace. A true smooth cutoff and the proved trace identity establish it. -/
theorem localConformalHerglotz_coordinate_trace_ae
     (ha : IsDirDensity a) k :
    (TF (herglotzWaveH1 hb ha k) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))]
        (fun θ => herglotzWave k a (physicalCircleTrace F θ)) := by
  obtain ⟨f, hfu, hfγ⟩ := exists_smoothTraceTest_herglotz hb hL hγ ha k
  rw [← hfu]
  filter_upwards [localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f,
    ae_restrict_mem measurableSet_Ioc] with θ ht hθ
  rw [ht, hcoord, hfγ _ (hτ.mapsTo (Ioc_subset_Icc_self hθ))]
  simpa [physicalCircleTrace, hcoord] using (herglotzWave_eq k a (γ (τ θ))).symm

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
  have hc : herglotzConormal k a (γ ∘ τ) =ᵐ[volume.restrict (Ioc 0 (2 * π))] (fun θ => deriv τ θ • herglotzConormal k a γ (τ θ)) := by
    filter_upwards [isC1TraceReparam_ae_comp hτ (ae_restrict_of_ae (hKγ.ae_differentiableAt (μ := volume)))] with θ hγdiff
    rw [herglotzConormal_eq ha.intervalIntegrable, (hγdiff.hasDerivAt.scomp θ (hτ.contDiff.differentiable_one θ).hasDerivAt).deriv,
      herglotzConormal_eq ha.intervalIntegrable]
    simp
    ring
  rw [← (show physicalCircleTrace F = γ ∘ τ by
    funext θ
    exact hcoord θ)] at hc
  apply Lp.ext
  filter_upwards [traceReparamConormalL2_ae hτ (herglotzConormalL2 hγ ha k), isC1TraceReparam_ae_comp hτ (herglotzConormalL2_ae hγ ha k), hc,
    localConformalHerglotzCoordinateLoad_ae F hΓLip ha k] with θ ht hr hc hg
  rw [ht, hr, hg]
  exact hc.symm

omit hhol hinj hC in
/-- In particular the normalized weak load is exactly half smoothing of
the actual coordinate conormal's unitary Fourier coefficients. -/
theorem localConformalHerglotzBoundaryLoad_eq_coordinateLoad
     (hΓLip : LipschitzWith L (physicalCircleTrace F))
     (ha : IsDirDensity a) (k : ℝ) :
    localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha k) =
      sobolevSmoothing (1 / 2) (by norm_num)
        (boundaryFourier (localConformalHerglotzCoordinateLoad F hΓLip ha k)) := by
  unfold localConformalBoundaryLoad
  rw [localConformalHerglotz_traceReparamConormal_eq_coordinateLoad F hγ hτ hcoord hΓLip ha k]

/-- The actual regular coordinate trace is used with the true
variable-speed Herglotz conormal. The variational input is explicitly the
proved Jacobian transform of the physical load. -/
def localConformalRegularPeriodicHerglotzExpression (E₀ : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2)  (ha : IsDirDensity a) : ℝ → ℂ :=
  periodicP W
    (TF (h1RegularResolvent ΩF E₀ E₀
      (ContinuousLinearMap.adjoint QF
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))))) : ℝ → ℂ)
    (herglotzConormal (Real.sqrt E₀) a (physicalCircleTrace F))

/-- Exact regular periodic identity in the genuine conformal circle.
Its variable speed does not enter an IsBoundaryParam assumption. -/
theorem localConformalRegularPeriodicHerglotzExpression_ae
     (hΓLip : LipschitzWith L (physicalCircleTrace F))
     (hE₀ : 0 ≤ E₀)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E₀ W)
     (ha : IsDirDensity a) :
    localConformalRegularPeriodicHerglotzExpression hR F hFs hL hγ hτ E₀ W ha
      =ᵐ[volume.restrict (Ioc 0 (2 * π))]
        (fun θ => observation W
            (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha) θ -
          2 * TF ((h1ResonantSpace ΩF E₀).starProjection
            (herglotzWaveH1 hb ha (Real.sqrt E₀))) θ) := by
  have hn :
      (TF (h1RegularResolvent ΩF E₀ E₀
        (ContinuousLinearMap.adjoint QF
          (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E₀))))) : ℝ → ℂ)
        =ᵐ[volume.restrict (Ioc 0 (2 * π))]
          (fun θ => herglotzWave (Real.sqrt E₀) a (physicalCircleTrace F θ) -
            TF ((h1ResonantSpace ΩF E₀).starProjection
              (herglotzWaveH1 hb ha (Real.sqrt E₀))) θ) := by
    rw [localConformal_regularHerglotz_coordinate_trace_eq hR F hFs hb hL hhol hinj
      hC hγ hτ hcoord hE₀ ha]
    exact regular_boundary_sub_ae _ _
      (localConformalHerglotz_coordinate_trace_ae hR F hFs hb hL hhol hinj hC hγ hτ
        hcoord ha (Real.sqrt E₀))
  filter_upwards [hn, ae_restrict_mem measurableSet_Ioc] with θ hn hθ
  have hp := periodicP_herglotz_eq_regularObservation hΓLip (by
    simpa using physicalCircleTrace_periodic F 0) hW ha
    (Ioc_subset_Icc_self hθ)
  simp [localConformalRegularPeriodicHerglotzExpression, periodicP, periodicA, hn]
    at hp ⊢
  linear_combination hp

omit hhol hinj hC hcoord in
/-- The corrected observation vector in the conformal identity is
orthogonal to its true boundary-origin cut. -/
theorem localConformalRegularHerglotzObservationVector_cutProj
     (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {E₀ : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E₀ W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
     (ha : IsDirDensity a) :
    cutProj (cutC (W (2 * π)) (basisVec 0))
        (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha) =
      regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha := by
  exact regularHerglotzObservationVector_cutProj hΓLip
    (by simpa using physicalCircleTrace_periodic F 0) hW hc ha

section CoordinatePairing

variable {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E₀ W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a)

local notation "zΓ" => regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha
local notation "rΓ" => TF (Submodule.starProjection (h1ResonantSpace ΩF E₀)
  (herglotzWaveH1 hb ha (Real.sqrt E₀)))


local notation "Φ2" => localConformalRegularPeriodicHerglotzExpression_ae hR F hFs hb hL hhol hinj hC hγ hτ hcoord hΓLip hE₀ hW ha
include hb hΓLip hE₀ hW hc in
theorem localConformalRegularPeriodicHerglotzExpression_memLp :
    MemLp (localConformalRegularPeriodicHerglotzExpression hR F hFs hL hγ hτ E₀ W ha)
      2 (volume.restrict (Ioc 0 (2 * π))) := by
  exact (Lp.memLp (projectedObservationBoundary hΓLip hW zΓ - (2 : ℂ) • rΓ)).ae_eq
    ((regular_observation_sub_ae hΓLip hW zΓ rΓ (localConformalRegularHerglotzObservationVector_cutProj F hΓLip hW hc ha)).trans (Φ2).symm)

/-- The ordinary-coordinate L2 class of the actual regular periodic
expression on the genuine variable-speed circle. -/
def localConformalRegularPeriodicHerglotzBoundary : BoundaryL2 :=
  (localConformalRegularPeriodicHerglotzExpression_memLp hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord hΓLip hE₀ hW hc ha).toLp
    (localConformalRegularPeriodicHerglotzExpression hR F hFs hL hγ hτ E₀ W ha)

theorem localConformalRegularPeriodicHerglotzBoundary_eq :
    localConformalRegularPeriodicHerglotzBoundary hR F hFs hb hL hhol hinj hC
      hγ hτ hcoord hΓLip hE₀ hW hc ha =
        projectedObservationBoundary hΓLip hW zΓ - (2 : ℂ) • rΓ := by
  unfold localConformalRegularPeriodicHerglotzBoundary
  exact regular_boundary_toLp_eq _ _
    ((regular_observation_sub_ae hΓLip hW zΓ rΓ (localConformalRegularHerglotzObservationVector_cutProj F hΓLip hW hc ha)).trans
      (Φ2).symm)

end CoordinatePairing

end ConformalCoordinates

/-! The following computation is on genuine coordinate integrals, with
ordinary measure. In particular it proves the zero Fourier row as well
as every nonzero row, for arbitrary integrable inputs. -/

private theorem regular_sawtooth_measurable :
    Measurable (Function.uncurry sawtoothKernel) := by
  unfold sawtoothKernel Function.uncurry
  exact (measurable_const.mul (Complex.measurable_ofReal.comp
    (measurable_real_sign.comp (measurable_fst.sub measurable_snd)))).sub
    (measurable_const.mul
      (((Complex.measurable_ofReal.comp measurable_fst).sub
        (Complex.measurable_ofReal.comp measurable_snd)).div_const (π : ℂ)))

private theorem regular_sawtooth_norm_le 
    (hθ : θ ∈ Icc 0 (2 * π)) (hs : s ∈ Icc 0 (2 * π)) :
    ‖sawtoothKernel θ s‖ ≤ 3 := by
  have hd : |θ - s| ≤ 2 * π := abs_le.mpr ⟨by linarith [hθ.1, hs.2],
    by linarith [hθ.2, hs.1]⟩
  have hdiv : |(θ - s) / π| ≤ 2 := by
    rw [abs_div, abs_of_pos pi_pos]
    exact (div_le_iff₀ pi_pos).mpr (by linarith)
  calc
    _ ≤
        ‖Complex.I * (Real.sign (θ - s))‖ +
          ‖Complex.I * ((θ - s) / π : ℝ)‖ := by
      simpa [sawtoothKernel] using
        (norm_sub_le (Complex.I * (Real.sign (θ - s)))
          (Complex.I * ((θ - s) / π : ℝ)))
    _ = |Real.sign (θ - s)| + |(θ - s) / π| := by
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    _ ≤ 3 := by linarith [abs_real_sign_le (θ - s)]

theorem memLp_sawtoothAction 
    (hf : Integrable f (volume.restrict (Φ1 (2 * π)))) :
    MemLp (fun θ => ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * f s) 2
      (volume.restrict (Φ1 (2 * π))) := by
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound ((regular_sawtooth_measurable.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).integral_prod_right') (3 * ∫ s, ‖f s‖ ∂(volume.restrict (Φ1 (2 * π)))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc
    _ ≤ _ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul 3)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (regular_sawtooth_norm_le (Ioc_subset_Icc_self hθ)
          (Ioc_subset_Icc_self hs)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The actual sawtooth boundary vector for an arbitrary L2 input. -/
def sawtoothBoundaryAction (f : BoundaryL2) : BoundaryL2 :=
  (memLp_sawtoothAction ((Lp.memLp f).integrable (by norm_num))).toLp _

theorem sawtoothBoundaryAction_fourier f n :
    boundaryFourier (sawtoothBoundaryAction f) n =
      2 / (n : ℂ) * boundaryFourier f n := by
  rw [boundaryFourier_apply, boundaryFourier_apply]
  have hf := (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  rw [fourierCoeffOn_congr_ae two_pi_pos (show sawtoothBoundaryAction f =ᵐ[ volume.restrict (Φ1 (2 * π))] (fun θ => ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * f s) from (MemLp.coeFn_toLp (memLp_sawtoothAction hf)))]
  have h_inl n : fourierCoeffOn two_pi_pos (fun θ => ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * f s) n = 2 / (n : ℂ) * fourierCoeffOn two_pi_pos f n := by
    let μ := volume.restrict (Φ1 (2 * π))
    have hmode (θ : ℝ) :
        Complex.exp (2 * π * Complex.I * (-n : ℤ) * θ / (2 * π : ℝ)) =
          kernelFourierMode (-n) θ := by
      simpa only [fourier_coe_apply] using fourier_two_pi_eq_kernelFourierMode (-n) θ
    rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
    simp_rw [fourier_coe_apply]
    simp only [sub_zero, Complex.real_smul, smul_eq_mul]
    simp_rw [hmode]
    push_cast
    simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
    change 1 / (2 * π) *
        (∫ θ, kernelFourierMode (-n) θ *
          (∫ s, sawtoothKernel θ s * f s ∂μ) ∂μ) = _
    rw [show (fun θ => kernelFourierMode (-n) θ * (∫ s, sawtoothKernel θ s * f s ∂μ)) = fun θ => ∫ s, kernelFourierMode (-n) θ * sawtoothKernel θ s * f s ∂μ by
      funext θ
      rw [← integral_const_mul]
      congr 1
      funext s
      ring, integral_integral_swap (show Integrable (fun p : ℝ × ℝ => kernelFourierMode (-n) p.1 * sawtoothKernel p.1 p.2 * f p.2) (μ.prod μ) by
      refine ((hf.norm.comp_snd μ).const_mul 3).mono' (by
        exact (((show Continuous (fun p : ℝ × ℝ => kernelFourierMode (-n) p.1) by
          unfold kernelFourierMode; fun_prop).measurable.aestronglyMeasurable.mul
          regular_sawtooth_measurable.aestronglyMeasurable).mul
          hf.aestronglyMeasurable.comp_snd)) ?_
      filter_upwards [show ∀ᵐ p ∂μ.prod μ, p ∈ Φ1 (2 * π) ×ˢ Φ1 (2 * π) by
        dsimp [μ]
        rw [Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      have h_inl n θ : ‖kernelFourierMode n θ‖ = 1 := by
        rw [← fourier_two_pi_eq_kernelFourierMode, fourier_apply]
        exact Circle.norm_coe _
      simp [h_inl]
      exact mul_le_mul_of_nonneg_right
        (regular_sawtooth_norm_le (Ioc_subset_Icc_self hp.1)
          (Ioc_subset_Icc_self hp.2)) (norm_nonneg _))]
    rw [integral_congr_ae (show (fun s => ∫ θ, kernelFourierMode (-n) θ * sawtoothKernel θ s * f s ∂μ) =ᵐ[μ] fun s => 2 / (n : ℂ) * (kernelFourierMode (-n) s * f s) by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [integral_mul_const]
      have hmode : (∫ θ in (0 : ℝ)..(2 * π), kernelFourierMode (-n) θ * sawtoothKernel θ s) = 2 / (n : ℂ) * kernelFourierMode (-n) s := by
        have heq : (fun θ => kernelFourierMode (-n) θ * sawtoothKernel θ s) =
            fun θ => -(sawtoothKernel s θ * kernelFourierMode (-n) θ) := by
          funext θ
          have h_inl θ s : sawtoothKernel θ s = -sawtoothKernel s θ := by
            simp [sawtoothKernel, show Real.sign (θ - s) = -Real.sign (s - θ) by
              rw [← Real.sign_neg, neg_sub]]
            ring
          rw [h_inl]
          ring
        rw [heq, intervalIntegral.integral_neg]
        by_cases hn : n = 0
        · subst n
          simp only [neg_zero, kernelFourierMode, Int.cast_zero, zero_mul,
            Complex.exp_zero, mul_one, div_zero, zero_mul]
          rw [integral_sawtoothKernel (Ioc_subset_Icc_self hs), neg_zero]
        · rw [show (∫ θ in (0 : ℝ)..(2 * π),
              sawtoothKernel s θ * kernelFourierMode (-n) θ) =
              2 / (-n : ℤ) * kernelFourierMode (-n) s from
              integral_sawtoothKernel_mul_exp (Ioc_subset_Icc_self hs) (neg_ne_zero.mpr hn)]
          simp [div_neg]
      rw [intervalIntegral.integral_of_le two_pi_pos.le] at hmode
      change (∫ θ, kernelFourierMode (-n) θ * sawtoothKernel θ s ∂μ) * f s = _
      rw [hmode]
      ring), integral_const_mul]
    ring
  rw [h_inl]
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
    regularRawInverseDerivative f n = 2 / (n : ℂ) * f n := by
  simp only [regularRawInverseDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    principalNormalized, normalizedInverseAbsOperator_apply, sobolevSmoothing, diagOp_apply]
  by_cases hn : n = 0
  · subst n
    simp [principalSymbol, normalizedInverseAbsSymbol]
  · have hsymbol : principalSymbol n - 2 * normalizedInverseAbsSymbol n =
        sobWeight n * (2 / (n : ℂ)) := by
      simp only [principalSymbol, normalizedInverseAbsSymbol, if_neg hn]
      push_cast
      ring
    calc
      _ = ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) *
          (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ)) *
          (principalSymbol n - 2 * normalizedInverseAbsSymbol n) * f n := by ring
      _ = ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) *
          ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (sobWeight n : ℂ)) *
          (2 / (n : ℂ)) * f n := by rw [hsymbol]; ring
      _ = _ := by rw [regular_half_weight_square, one_mul]

private theorem regular_half_sqrt_cancel n :
    ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (Real.sqrt (sobWeight n) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, Real.sqrt_eq_rpow,
    ← Real.rpow_add (sobWeight_pos n)]
  norm_num

/-- The bounded boundary operator obtained from the genuine raw Fourier
multiplier. It equals the original coordinate sawtooth integral on all L2. -/
def sawtoothBoundaryOperator : BoundaryL2 →L[ℂ] BoundaryL2 :=
  boundaryFourier.symm.toLinearIsometry.toContinuousLinearMap.comp
    (regularRawInverseDerivative.comp boundaryFourier.toLinearIsometry.toContinuousLinearMap)

theorem sawtoothBoundaryOperator_eq_action f :
    sawtoothBoundaryOperator f = sawtoothBoundaryAction f := by
  apply boundaryFourier.injective
  apply lp.ext
  funext n
  change boundaryFourier (boundaryFourier.symm
    (regularRawInverseDerivative (boundaryFourier f))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply, regularRawInverseDerivative_apply,
    sawtoothBoundaryAction_fourier]

/-- The corrected integral operator on ordinary boundary L2, transported
through the actual unitary circle lift. Both maps use their true measures. -/
def regularCorrectedBoundaryOperator   
     (hK : LipschitzWith K γ)
    (hW : IsTransport γ E W) (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) :
    BoundaryL2 →L[ℂ] BoundaryL2 :=
  boundaryCircleUnitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((correctedKernelL2Op hK hW hc).comp
      boundaryCircleUnitary.toLinearIsometry.toContinuousLinearMap)

theorem memLp_regularCorrectedAction
       
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) 
    (hf : Integrable f (volume.restrict (Φ1 (2 * π)))) :
    MemLp (fun θ => ∫ s in (0 : ℝ)..(2 * π), correctedKernel W θ s * f s) 2
      (volume.restrict (Φ1 (2 * π))) := by
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound (((aestronglyMeasurable_correctedKernel hW).mul hf.aestronglyMeasurable.comp_snd).integral_prod_right') ((4 + ‖cutBE W‖) * ∫ s, ‖f s‖ ∂(volume.restrict (Φ1 (2 * π)))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc
    _ ≤ _ := by
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
private theorem regular_boundary_operator_sum_apply
    (T A B : BoundaryL2 →L[ℂ] BoundaryL2) (g : BoundaryL2) :
    ((2 : ℂ) • T + A + B) g = (2 : ℂ) • T g + A g + B g := by
  simp

private theorem regular_boundary_ae_of_eq (u v : BoundaryL2) 
    (huv : u = v)
    (hv : (v : ℝ → ℂ) =ᵐ[volume.restrict (Φ1 (2 * π))] f) :
    (u : ℝ → ℂ) =ᵐ[volume.restrict (Φ1 (2 * π))] f := by
  subst u
  exact hv

private theorem regular_boundary_eq_of_periodic_load_eq
    (T : L2Z →L[ℂ] BoundaryL2) (W : ℝ → Ell2 →L[ℂ] Ell2)
    (b d : L2Z) (hbd : b = d) (f : ℝ → ℂ) (u v : BoundaryL2)
    (hu : (u : ℝ → ℂ) =ᵐ[volume.restrict (Φ1 (2 * π))]
      periodicP W (T b : ℝ → ℂ) f)
    (hv : (v : ℝ → ℂ) =ᵐ[volume.restrict (Φ1 (2 * π))]
      periodicP W (T d : ℝ → ℂ) f) : u = v := by
  subst b
  exact Lp.ext (hu.trans hv.symm)

private theorem regular_boundary_smoothing_difference
    (S : L2Z →L[ℂ] L2Z) x q p r
    (hx : S x = boundaryFourier p) (hq : S q = boundaryFourier r) :
    S (x - (2 : ℂ) • q) = boundaryFourier (p - (2 : ℂ) • r) := by
  rw [map_sub, map_smul, map_sub, map_smul, hx, hq]

section ActualPeriodicOperator

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hL : IsLipschitzDomain (F '' ball 0 1))

local notation "ΩP" => F '' ball 0 1
local notation "QP" => localConformalDiskHalfTrace hR F hFs hL
local notation "TP" => localConformalDiskH1Trace hR F hFs hL

theorem localConformal_halfSmoothing_halfTrace u :
    sobolevSmoothing (1 / 2) (by norm_num) (QP u) = boundaryFourier (TP u) := by
  apply lp.ext
  funext n
  simp only [sobolevSmoothing, diagOp_apply, localConformalDiskHalfTrace_apply]
  change (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) *
    ((Real.sqrt (sobWeight n)) * boundaryFourier (TP u) n) = _
  rw [← mul_assoc, ← Complex.ofReal_mul, show sobWeight n ^ (-(1 / 2 : ℝ)) * Real.sqrt (sobWeight n) = 1 by
    rw [Real.sqrt_eq_rpow, mul_comm, sobWeight_rpow_mul_neg], Complex.ofReal_one, one_mul]

/-- The genuine regular trace, the original sawtooth integral, and the
actual corrected boundary kernel form this bounded coordinate operator.
The normalization identity is proved next, rather than used to define it. -/
def localConformalRegularPeriodicOperator (E₀ E : ℝ)
      
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  (2 : ℂ) • ((TP).comp
    ((h1RegularResolvent ΩP E₀ E).comp
    ((ContinuousLinearMap.adjoint QP).comp
      ((sobolevSmoothing (1 / 2) (by norm_num)).comp
        boundaryFourier.toLinearIsometry.toContinuousLinearMap)))) +
    sawtoothBoundaryOperator + regularCorrectedBoundaryOperator hK hW hc

/-- The actual bounded operator agrees with the assembled normalized
regular Fourier operator on every L2 load, including its constant mode. -/
theorem localConformalRegularPeriodicOperator_fourier (E₀ E : ℝ)
      
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    f :
    boundaryFourier (localConformalRegularPeriodicOperator hR F hFs hL E₀ E hK hW hc f) =
      sobolevSmoothing (1 / 2) (by norm_num)
        (normalizedPeriodicRegularOperator QP E₀ E W hbase
          (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier f))) := by
  let S := sobolevSmoothing (1 / 2) (by norm_num)
  let b := S (boundaryFourier f)
  let u :=
    h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP b)
  let hr := (show Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel W) p‖ ^ 2 by
    refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) hbase
    have hm : 1 ≤ (sobWeight p.1) ^ (1 / 2 : ℝ) :=
      Real.one_le_rpow (one_le_sobWeight p.1) (by norm_num)
    have hn : 1 ≤ (sobWeight p.2) ^ (1 / 2 : ℝ) :=
      Real.one_le_rpow (one_le_sobWeight p.2) (by norm_num)
    have hweight := one_le_mul_of_one_le_of_one_le hm hn
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [show correctedRemainderMatrix W 0 0 p = ((sobWeight p.1) ^ (1 / 2 : ℝ) * (sobWeight p.2) ^ (1 / 2 : ℝ) : ℝ) * kernelIntegralMatrix (r := correctedKernel W) p by
      simp [correctedRemainderMatrix, kernelIntegralMatrix, sobWeight]
      ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    simpa using mul_le_mul_of_nonneg_right hweight (norm_nonneg _))
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
  rw [map_add, map_add, map_smul, show boundaryFourier (sawtoothBoundaryOperator f) = regularRawInverseDerivative (boundaryFourier f) by
    change boundaryFourier (boundaryFourier.symm
      (regularRawInverseDerivative (boundaryFourier f))) = _
    exact LinearIsometryEquiv.apply_symm_apply _ _, show boundaryFourier (regularCorrectedBoundaryOperator hK hW hc f) = hsMatrixOp (kernelIntegralMatrix (r := correctedKernel W)) hr (boundaryFourier f) by
    change (fourierBasis (T := 2 * π)).repr
      (boundaryCircleUnitary (boundaryCircleUnitary.symm
        (correctedKernelL2Op hK hW hc (boundaryCircleUnitary f)))) = _
    rw [LinearIsometryEquiv.apply_symm_apply,
      correctedKernelL2Op_fourier_action hK hW hc hr]
    rfl, hraw]
  simp [normalizedPeriodicRegularOperator, smul_sub, show S (normalizedNeumannRegular QP E₀ E b) = boundaryFourier (TP u) from localConformal_halfSmoothing_halfTrace hR F hFs hL u, hHS]
  abel

/-- The bounded operator's output is the actual pointwise periodic
expression on every continuous bounded coordinate load. Its trace input
is the original regular Neumann solution, rather than a stipulated form. -/
theorem localConformalRegularPeriodicOperator_apply_ae (E₀ E : ℝ)
      {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    (g : BoundaryL2) {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ}
    (hfB : ∀ s, ‖f s‖ ≤ B)
    (hgf : (g : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * π))] f) :
    (localConformalRegularPeriodicOperator hR F hFs hL E₀ E hK hW hc g : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))]
        periodicP W
          (TP (h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP
            (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)))) : ℝ → ℂ) f := by
  let t := TP (h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP
    (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g))))
  exact regular_boundary_ae_of_eq _ _ (by
    have h_simpa := regular_boundary_operator_sum_apply
      ((TP).comp
      ((h1RegularResolvent ΩP E₀ E).comp
      ((ContinuousLinearMap.adjoint QP).comp
      ((sobolevSmoothing (1 / 2) (by norm_num)).comp
      boundaryFourier.toLinearIsometry.toContinuousLinearMap))))
      sawtoothBoundaryOperator (regularCorrectedBoundaryOperator hK hW hc) g
    simp only [localConformalRegularPeriodicOperator, ContinuousLinearMap.comp_apply] at h_simpa ⊢
    exact h_simpa)
    (show ((2 : ℂ) • t + sawtoothBoundaryOperator g + regularCorrectedBoundaryOperator hK hW hc g : BoundaryL2) =ᵐ[ volume.restrict (Ioc 0 (2 * π))] periodicP W (t : ℝ → ℂ) f by
      have hfI := ((Lp.memLp g).ae_eq hgf).integrable (by norm_num : (1 : ENNReal) ≤ 2)
      let k : BoundaryL2 := (memLp_regularCorrectedAction hK hW hfI).toLp _
      have hsaw (θ : ℝ) :
          (∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * g s) =
            ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * f s := by
        simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
        apply integral_congr_ae
        filter_upwards [hgf] with s hs
        rw [hs]
      rw [sawtoothBoundaryOperator_eq_action, show regularCorrectedBoundaryOperator hK hW hc g = k by
        apply boundaryFourier.injective
        apply lp.ext
        funext n
        have h_inl n : boundaryFourier (regularCorrectedBoundaryOperator hK hW hc g) n = (√(2 * π) : ℂ) * fourierCoeffOn two_pi_pos (fun θ => ∫ s in (0 : ℝ)..(2 * π), correctedKernel W θ s * f s) n := by
          let fC := (memLp_liftIco_two_pi hf.measurable hfB).toLp _
          change (fourierBasis (T := 2 * π)).repr
            (boundaryCircleUnitary (boundaryCircleUnitary.symm
              (correctedKernelL2Op hK hW hc (boundaryCircleUnitary g)))) n = _
          rw [LinearIsometryEquiv.apply_symm_apply]
          change (fourierBasis (T := 2 * π)).repr
            (correctedKernelL2Op hK hW hc ((√(2 * π) : ℂ) • boundaryCircleLift g)) n = _
          rw [show boundaryCircleLift g = fC by
            apply Lp.ext
            exact (boundaryCircleLift_coe g).trans
              (((boundary_liftIoc_congr_ae hgf).trans
                (boundary_liftIoc_eq_liftIco_ae f)).trans
                  (MemLp.coeFn_toLp (memLp_liftIco_two_pi hf.measurable hfB)).symm), map_smul, map_smul]
          change (√(2 * π) : ℂ) *
            (fourierBasis (T := 2 * π)).repr (correctedKernelL2Op hK hW hc fC) n = _
          rw [correctedKernelL2Op_toLp_fourier hK hW hc hf.measurable hfB]
        rw [h_inl,
          boundaryFourier_apply]
        congr 1
        exact (congrFun (fourierCoeffOn_congr_ae two_pi_pos
          (MemLp.coeFn_toLp (memLp_regularCorrectedAction hK hW hfI))) n).symm]
      filter_upwards [Lp.coeFn_add ((2 : ℂ) • t + sawtoothBoundaryAction g) k,
        Lp.coeFn_add ((2 : ℂ) • t) (sawtoothBoundaryAction g), Lp.coeFn_smul (2 : ℂ) t,
        MemLp.coeFn_toLp (memLp_sawtoothAction
          ((Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2))),
        MemLp.coeFn_toLp (memLp_regularCorrectedAction hK hW hfI),
        ae_restrict_mem measurableSet_Ioc] with θ ha hb hc' hs hk' hθ
      rw [ha, Pi.add_apply, hb, Pi.add_apply, hc', Pi.smul_apply, smul_eq_mul]
      dsimp only [sawtoothBoundaryAction, k]
      rw [hs, hk', hsaw]
      exact (periodicP_eq_doubleTrace_add_kernel_integrals hW.1 (t : ℝ → ℂ)
        hf hfB (Ioc_subset_Icc_self hθ)).symm)

end ActualPeriodicOperator

section ActualHerglotzMatching

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball 0 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))
    {K : NNReal} (hΓLip : LipschitzWith K (physicalCircleTrace F))
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E₀ W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a)

include hR hFs ha in
private theorem regular_continuous_coordinateConormal (k : ℝ) :
    Continuous (herglotzConormal k a (physicalCircleTrace F)) := by
  have hΓ := contDiff_physicalCircleTrace_of_neighborhood hR F
    (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [funext (herglotzConormal_eq ha.intervalIntegrable k (physicalCircleTrace F))]
  exact continuous_const.mul
    (((Complex.continuous_conj.comp hΓ.continuous_deriv_one).mul
      ((continuous_herglotzCoeff ha.intervalIntegrable k (-1)).comp hΓ.continuous)).sub
    (hΓ.continuous_deriv_one.mul
      ((continuous_herglotzCoeff ha.intervalIntegrable k 1).comp hΓ.continuous)))

include hγ hτ hhol hinj hC hcoord hΓLip hE₀ hW hc in
/-- Applying the genuine bounded coordinate operator to the actual
Herglotz conormal gives exactly the previously derived physical regular
periodic expression. The resonant subtraction is therefore preserved. -/
local notation "Φ0" => localConformalRegularPeriodicHerglotzBoundary hR F hFs hb hL hhol hinj hC hγ hτ hcoord hΓLip hE₀ hW hc ha

local notation "Φ3" => localConformalDiskHalfTrace hR F hFs hL

local notation "Φ5" => Real.sqrt E₀

theorem localConformalRegularPeriodicOperator_herglotz :
    localConformalRegularPeriodicOperator hR F hFs hL E₀ E₀ hΓLip hW hc
      (localConformalHerglotzCoordinateLoad F hΓLip ha (Φ5)) =
        Φ0 := by
  obtain ⟨_, B, hfB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Φ5) hΓLip
  let T : L2Z →L[ℂ] BoundaryL2 :=
    (localConformalDiskH1Trace hR F hFs hL).comp
      ((h1RegularResolvent (F '' ball 0 1) E₀ E₀).comp
        (ContinuousLinearMap.adjoint (Φ3)))
  have hbdy : (Φ0 : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))]
        localConformalRegularPeriodicHerglotzExpression hR F hFs hL hγ hτ E₀ W ha :=
    MemLp.coeFn_toLp (localConformalRegularPeriodicHerglotzExpression_memLp
      hR F hFs hb hL hhol hinj hC hγ hτ hcoord hΓLip hE₀ hW hc ha)
  exact regular_boundary_eq_of_periodic_load_eq T W _ _ (localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha (Φ5)).symm
    (herglotzConormal (Φ5) a (physicalCircleTrace F)) _ _ (by
      simpa [T] using (localConformalRegularPeriodicOperator_apply_ae hR F hFs hL E₀ E₀ hΓLip hW hc (localConformalHerglotzCoordinateLoad F hΓLip ha (Φ5)) (regular_continuous_coordinateConormal hR F hFs ha (Φ5)) hfB (localConformalHerglotzCoordinateLoad_ae F hΓLip ha (Φ5)))) (by
      simpa [localConformalRegularPeriodicHerglotzExpression, T] using hbdy)

include hb hhol hinj hC hcoord hΓLip hE₀ hW hc in
/-- The assembled normalized operator is now matched to the actual
regular periodic Herglotz expression, with ordinary boundary Fourier
normalization sqrt(2π). There is no discarded zero Fourier coefficient. -/
theorem normalizedPeriodicRegularOperator_herglotz_fourier
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    sobolevSmoothing (1 / 2) (by norm_num)
      (normalizedPeriodicRegularOperator (Φ3)
        E₀ E₀ W hbase (localConformalBoundaryLoad hτ
          (herglotzConormalL2 hγ ha (Φ5)))) =
      boundaryFourier (Φ0) := by
  rw [localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha, ← localConformalRegularPeriodicOperator_fourier hR F hFs hL E₀ E₀ hΓLip hW hc hbase,
    localConformalRegularPeriodicOperator_herglotz hR F hFs hb hL hhol hinj hC
      hγ hτ hcoord hΓLip hE₀ hW hc ha]

include hhol hinj hC hcoord hΓLip hE₀ hW hc in
/-- The full normalized regular expression on genuine Herglotz data is
the true projected-observation adjoint minus twice the original resonant
half-trace. Half smoothing is canceled using its genuine injectivity. -/
theorem normalizedPeriodicRegularOperator_herglotz_eq
    hbase :
    normalizedPeriodicRegularOperator (Φ3)
        E₀ E₀ W hbase (localConformalBoundaryLoad hτ
          (herglotzConormalL2 hγ ha (Φ5))) =
      (√(2 * π) : ℂ) • ContinuousLinearMap.adjoint (projObsDual W)
        (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha) -
      (2 : ℂ) • Φ3
        ((h1ResonantSpace (F '' ball 0 1) E₀).starProjection
          (herglotzWaveH1 hb ha (Φ5))) := by
  apply (show Function.Injective (sobolevSmoothing (1 / 2) (by norm_num)) by
    intro f g h
    apply lp.ext
    funext n
    have hn := congrArg (fun v : L2Z => v n) h
    simp only [sobolevSmoothing, diagOp_apply] at hn
    exact mul_left_cancel₀ (by
      exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) _).ne') hn)
  exact (normalizedPeriodicRegularOperator_herglotz_fourier hR F hFs hb hL hhol hinj hC hγ hτ hcoord hΓLip hE₀ hW hc ha hbase).trans ((congrArg (fun f : BoundaryL2 => boundaryFourier f) (localConformalRegularPeriodicHerglotzBoundary_eq hR F hFs hb hL hhol hinj hC hγ hτ hcoord hΓLip hE₀ hW hc ha)).trans (regular_boundary_smoothing_difference (sobolevSmoothing (1 / 2) (by norm_num)) _ _ _ _ (show sobolevSmoothing (1 / 2) (by norm_num) ((√(2 * π) : ℂ) • ContinuousLinearMap.adjoint (projObsDual W) (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha)) = boundaryFourier (projectedObservationBoundary hΓLip hW (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha)) by
    rw [projObsDual_eq hΓLip hW, rowSynth, ContinuousLinearMap.adjoint_adjoint]
    apply lp.ext
    funext n
    simp only [sobolevSmoothing, diagOp_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, rowAnalysis_apply, normProjObsRow, inner_smul_left,
      Complex.conj_ofReal, boundaryFourier_projectedObservation]
    change (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) *
      ((√(2 * π)) * ((Real.sqrt (sobWeight n)) * ⟪projObsCoeffVec W n, (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha)⟫_ℂ)) = _
    calc
      _ = ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) *
        (Real.sqrt (sobWeight n))) *
        ((√(2 * π) : ℂ) * ⟪projObsCoeffVec W n, (regularHerglotzObservationVector (γ := physicalCircleTrace F) E₀ W ha)⟫_ℂ) := by ring
      _ = _ := by rw [regular_half_sqrt_cancel, one_mul]) (localConformal_halfSmoothing_halfTrace hR F hFs hL ((h1ResonantSpace (F '' ball 0 1) E₀).starProjection (herglotzWaveH1 hb ha (Φ5))))).symm)

end ActualHerglotzMatching

end PolyaNeumann

end
