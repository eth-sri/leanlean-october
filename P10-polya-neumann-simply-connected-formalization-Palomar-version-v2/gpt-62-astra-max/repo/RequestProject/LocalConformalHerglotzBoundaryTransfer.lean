module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalNormalizedResidueBasis
public import RequestProject.HerglotzReparam
public import RequestProject.ObservationLp
public import RequestProject.PhysicalHardyWeights
public import Mathlib.Analysis.Real.Pi.Bounds
public import RequestProject.PlanarNotation

/-!
The genuine transfer from the normalized periodic boundary estimate to
the original Herglotz direction densities. The weak load is
`b = sqrt(2π) Λ⁻¹ᐟ² ĝ`. Its form is the ordinary, unaveraged boundary
pairing, and `sqrt(2π) • projObsDual b` is the projected ordinary
observation. The paper vector is `sqrt(2π) • b`; only that vector has
the form factor `1 / (2π)`. The unprojected observation is used only on
the actual ordinary L2 conormal trace. The resulting statements are part of
the verified dependency chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace PolyaNeumann

open Set MeasureTheory Filter Metric Real
open scoped InnerProductSpace ComplexConjugate Topology

local notation "μB" => angleMeasure

/-- The actual physical conormal L2 class is linear on direction densities. -/
def herglotzConormalBoundaryLin {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (k : ℝ) : dirDensities →ₗ[ℂ] BoundaryL2 where
  toFun a := herglotzConormalL2 hγ a.property k
  map_add' a b := by
    apply Lp.ext
    filter_upwards [herglotzConormalL2_ae hγ (a + b).property k,
      herglotzConormalL2_ae hγ a.property k, herglotzConormalL2_ae hγ b.property k,
      Lp.coeFn_add (herglotzConormalL2 hγ a.property k)
        (herglotzConormalL2 hγ b.property k)] with θ hab ha hb hs
    rw [hab, hs]
    simp only [Pi.add_apply, ha, hb]
    exact congrFun (herglotzConormal_add_density a.property b.property k γ) θ
  map_smul' c a := by
    apply Lp.ext
    filter_upwards [herglotzConormalL2_ae hγ (c • a).property k,
      herglotzConormalL2_ae hγ a.property k,
      Lp.coeFn_smul c (herglotzConormalL2 hγ a.property k)] with θ hca ha hs
    simp only [RingHom.id_apply]
    rw [hca, hs]
    simp only [Pi.smul_apply, ha, smul_eq_mul]
    exact congrFun (herglotzConormal_smul_density a.property c k γ) θ

/-- Genuine Jacobian transport of ordinary L2 loads as a linear map. -/
def traceReparamConormalLinearMap {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) : BoundaryL2 →ₗ[ℂ] BoundaryL2 where
  toFun := traceReparamConormalL2 hτ
  map_add' g h := by
    apply Lp.ext
    have hadd := isC1TraceReparam_ae_comp hτ (Lp.coeFn_add g h)
    filter_upwards [traceReparamConormalL2_ae hτ (g + h),
      traceReparamConormalL2_ae hτ g, traceReparamConormalL2_ae hτ h,
      Lp.coeFn_add (traceReparamConormalL2 hτ g) (traceReparamConormalL2 hτ h),
      hadd] with θ hab hg hh hs hc
    rw [hab, hs]
    simp only [Pi.add_apply, hg, hh, hc, smul_add]
  map_smul' a g := by
    apply Lp.ext
    have hsmul := isC1TraceReparam_ae_comp hτ (Lp.coeFn_smul a g)
    filter_upwards [traceReparamConormalL2_ae hτ (a • g),
      traceReparamConormalL2_ae hτ g,
      Lp.coeFn_smul a (traceReparamConormalL2 hτ g), hsmul] with θ hag hg hs hc
    simp only [RingHom.id_apply]
    rw [hag, hs]
    simp only [Pi.smul_apply, hg, hc]
    exact smul_comm (deriv τ θ) a (g (τ θ))

/-- The actual normalized weak-load map, with the physical Jacobian. -/
def localConformalBoundaryLoadLinearMap {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) : BoundaryL2 →ₗ[ℂ] L2Z :=
  (sobolevSmoothing halfOrder (by norm_num)).toLinearMap.comp
    (boundaryFourier.toLinearMap.comp (traceReparamConormalLinearMap hτ))

/-- Direction densities give the actual physical conormal followed by its
true Jacobian transport and its unitary Fourier normalization. -/
def localConformalHerglotzBoundaryLin {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (k : ℝ) : dirDensities →ₗ[ℂ] L2Z :=
  (localConformalBoundaryLoadLinearMap hτ).comp (herglotzConormalBoundaryLin hγ k)

/-- Extension to arbitrary direction functions does not change any
condition on the genuine density subspace. -/
theorem exists_localConformalHerglotz_density_conditions {Ω : Set ℂ}
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (k : ℝ) {m : ℕ}
    (ℓ : L2Z →ₗ[ℂ] (Fin m → ℂ)) :
    ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a (ha : IsDirDensity a),
      L a = ℓ (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha k)) := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend
    (ℓ.comp (localConformalHerglotzBoundaryLin hγ hτ k))
  refine ⟨L, fun a ha => ?_⟩
  exact congrArg (fun T => T ⟨a, ha⟩) hL

/-- The actual bounded cut correction has one uniform norm bound near
a nonzero cut, derived from the genuine energy-dependent transport. -/
theorem exists_herglotzCut_uniform_bound {δ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K δ) (Ws : ℝ → TransportPath)
    (hWs : ∀ E, IsTransport δ E (Ws E)) (E₀ : ℝ)
    (hc : cutVector (Ws E₀) ≠ 0) :
    ∃ B ρ : ℝ, 0 < B ∧ 0 < ρ ∧ ∀ E, |E - E₀| < ρ →
      cutVector (Ws E) ≠ 0 ∧ ‖cutBE (Ws E)‖ ≤ B := by
  have hB  :=
    ((tendsto_cutBE_energy hK hWs E₀ hc).norm.eventually
      (gt_mem_nhds (by linarith : ‖cutBE (Ws E₀)‖ < ‖cutBE (Ws E₀)‖ + 1))).mono
        fun _ h => h.le
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
    ((eventually_cutC_ne hK hWs E₀ hc).and hB)
  refine ⟨‖cutBE (Ws E₀)‖ + 1, ρ, by positivity, hρ, fun E hE => ?_⟩
  solve_by_elim

section Coordinates

section

variable (F : ℂ → ℂ) (Φ : ConformalDiskMap)

private theorem herglotz_transfer_observationAdj_congr_ae (W : TransportPath) {g h : ℝ → ℂ}
    (he : g =ᵐ[μB] h) :
    observationAdj W g = observationAdj W h := by
  rw [observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply integral_congr_ae
  filter_upwards [he] with θ hθ
  rw [hθ]

/-- The unitary weak-load scale of the projected observation. The
unprojected integral is evaluated only on the true conormal density. -/
theorem localConformalHerglotzBoundary_projObsDual {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam (F '' unitDisk) γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) {E : ℝ} {W : TransportPath}
    (hW : IsTransport (physicalCircleTrace F) E W) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    fourierScale • projObsDual W
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      cutProj (cutVector W)
        (observationAdj W (herglotzConormal (Real.sqrt E) a (physicalCircleTrace F))) := by
  rw [localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha]
  rw [← map_smul]
  have h := projObsDual_boundary_normalized hΓLip hW
    (localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E))
  rw [herglotz_transfer_observationAdj_congr_ae W
    (localConformalHerglotzCoordinateLoad_ae F hΓLip ha (Real.sqrt E))] at h
  exact h

theorem localConformalHerglotzBoundary_projObsDual_norm_sq {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam (F '' unitDisk) γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCirclePt θ) = γ (τ θ)) {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) {E : ℝ} {W : TransportPath}
    (hW : IsTransport (physicalCircleTrace F) E W) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    anglePeriod * ‖projObsDual W
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))‖ ^ 2 =
      ‖cutProj (cutVector W)
        (observationAdj W (herglotzConormal (Real.sqrt E) a (physicalCircleTrace F)))‖ ^ 2 := by
  have hn := congrArg (fun v : Ell2 => ‖v‖ ^ 2)
    (localConformalHerglotzBoundary_projObsDual F hγ hτ hcoord hΓLip hW ha)
  simpa only [norm_smul, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt Real.two_pi_pos.le] using hn

theorem herglotz_transfer_kernel_summable (Φ : SmoothDiskMap) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E : ℝ} {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (hc : cutVector W ≠ 0) :
    Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2 := by
  have hΓ4 := Φ.boundaryC4
  have hΓ2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) Φ.boundary := hΓ4.of_le (by norm_num)
  obtain ⟨B, hB⟩ := hΓ2.deriv'.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 anglePeriod) isCompact_Icc
  have hdiff : ∀ x ∈ angleInterval, ∀ y ∈ angleInterval,
      ‖deriv Φ.boundary x - deriv Φ.boundary y‖ ≤ B * |x - y| := by
    intro x hx y hy
    have h := hB.dist_le_mul x hx y hy
    rwa [dist_eq_norm, Real.dist_eq] at h
  exact summable_correctedRemainderMatrix hΓLip hdiff hW hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The actual full family on a Herglotz load is its true corrected
observation adjoint. Nonresonance removes precisely the genuine form
kernel, rather than suppressing the constant Fourier mode. -/
theorem normalizedPeriodicBoundaryFamily_herglotz_eq {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (Ws : ℝ → TransportPath) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary)
    (hW : IsTransport Φ.boundary E (Ws E))
    (hc : cutVector (Ws E) ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      fourierScale • ContinuousLinearMap.adjoint (projObsDual (Ws E))
        (regularHerglotzObservationVector (γ := Φ.boundary) E (Ws E) ha) := by
  have hunit := h1HelmholtzForm_isUnit Φ.bounded Φ.lipschitzDomain hE hnr
  have hbase := herglotz_transfer_kernel_summable Φ hΓLip hW hc
  rw [normalizedPeriodicBoundaryFamily_eq_regular_at_nonresonant_reference (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Φ.bounded Φ.lipschitzDomain Ws hE hunit,
    normalizedPeriodicRegularFamily_eq (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E E Ws hbase]
  rw [normalizedPeriodicRegularOperator_herglotz_eq Φ hγ hτ hcoord hΓLip hE hW hc ha hbase,
    h1Resonant_starProjection_eq_zero_of_form_isUnit hunit, map_zero, smul_zero, sub_zero]

private theorem herglotz_transfer_periodic_inner {δ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K δ) (hclosed : δ anglePeriod = δ 0) {E : ℝ} {W : TransportPath}
    (hW : IsTransport δ E W) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    l2Inner (herglotzConormal (Real.sqrt E) a δ)
      (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (δ θ))
        (herglotzConormal (Real.sqrt E) a δ)) =
      ⟪observationAdj W (herglotzConormal (Real.sqrt E) a δ),
        regularHerglotzObservationVector (γ := δ) E W ha⟫_ℂ := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  rw [inner_observationAdj hW.1 hgm hgB]
  
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le Real.two_pi_pos.le] at hθ
  change conj (herglotzConormal (Real.sqrt E) a δ θ) *
      periodicP W (fun s => herglotzWave (Real.sqrt E) a (δ s))
        (herglotzConormal (Real.sqrt E) a δ) θ =
    conj (herglotzConormal (Real.sqrt E) a δ θ) *
      observation W (regularHerglotzObservationVector (γ := δ) E W ha) θ
  rw [periodicP_herglotz_eq_regularObservation hK hclosed hW ha hθ]

/-- The exact complex ordinary-boundary pairing equals the full
normalized pairing for the unitary weak load, with no factor 2π. -/
theorem normalizedPeriodicBoundaryFamily_herglotz_inner {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (Ws : ℝ → TransportPath) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary)
    (hW : IsTransport Φ.boundary E (Ws E))
    (hc : cutVector (Ws E) ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))
    ⟪b, normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E b⟫_ℂ =
      l2Inner (herglotzConormal (Real.sqrt E) a Φ.boundary)
        (periodicP (Ws E) (fun θ => herglotzWave (Real.sqrt E) a (Φ.boundary θ))
          (herglotzConormal (Real.sqrt E) a Φ.boundary)) := by
  dsimp only
  rw [normalizedPeriodicBoundaryFamily_herglotz_eq Φ hγ hτ hcoord Ws hE hnr hΓLip hW hc ha,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
  have hclosed : Φ.boundary anglePeriod = Φ.boundary 0 := by
    simpa only [zero_add] using Φ.periodic_boundary 0
  have hz := regularHerglotzObservationVector_cutProj hΓLip hclosed hW hc ha
  have hobs := localConformalHerglotzBoundary_projObsDual Φ.map hγ hτ hcoord hΓLip hW ha
  calc
    _ = ⟪fourierScale • projObsDual (Ws E)
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))),
          regularHerglotzObservationVector (γ := Φ.boundary) E (Ws E) ha⟫_ℂ := by
      rw [inner_smul_left, Complex.conj_ofReal]
    _ = ⟪observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a Φ.boundary),
        regularHerglotzObservationVector (γ := Φ.boundary) E (Ws E) ha⟫_ℂ := by
      rw [hobs, inner_cutProj_left, hz]
    _ = _ := (herglotz_transfer_periodic_inner hΓLip hclosed hW ha).symm

/-- The sharp normalization in the fixed-energy transfer is A0/(2π).
The remaining correction is the norm of the actual bounded cut operator. -/
theorem localConformalHerglotzForm_lower_of_normalizedBoundary {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (Ws : ℝ → TransportPath) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary)
    (hW : IsTransport Φ.boundary E (Ws E))
    (hc : cutVector (Ws E) ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a) {A₀ : ℝ}
    (hA₀ : 0 ≤ A₀)
    (hbound : let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E));
      -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
        (⟪b, normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E b⟫_ℂ).re) :
    -((A₀ / anglePeriod + ‖cutBE (Ws E)‖) *
      ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a Φ.boundary)‖ ^ 2) ≤
        herglotzForm (Ws E) Φ.boundary E a := by
  dsimp only at hbound
  have hn := localConformalHerglotzBoundary_projObsDual_norm_sq Φ.map hγ hτ hcoord hΓLip hW ha
  have hn' : ‖projObsDual (Ws E)
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))‖ ^ 2 =
      ‖cutProj (cutVector (Ws E))
        (observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a Φ.boundary))‖ ^ 2 /
          anglePeriod := by
    apply (eq_div_iff Real.two_pi_pos.ne').mpr
    simpa only [mul_comm] using hn
  rw [hn', normalizedPeriodicBoundaryFamily_herglotz_inner Φ hγ hτ hcoord Ws hE hnr hΓLip hW hc ha] at hbound
  apply herglotzForm_lower_of_periodicP_lower hΓLip
    (by simpa only [zero_add] using Φ.periodic_boundary 0) hW ha
    (div_nonneg hA₀ Real.two_pi_pos.le)
  convert hbound using 1; ring

theorem localConformalHerglotzForm_lower_of_normalizedBoundary_boundedCut {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (Ws : ℝ → TransportPath) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary)
    (hW : IsTransport Φ.boundary E (Ws E))
    (hc : cutVector (Ws E) ≠ 0) {a : ℝ → ℂ} (ha : IsDirDensity a) {A₀ B : ℝ}
    (hA₀ : 0 ≤ A₀) (hB : ‖cutBE (Ws E)‖ ≤ B)
    (hbound : let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E));
      -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
        (⟪b, normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E b⟫_ℂ).re) :
    -((A₀ / anglePeriod + B) *
      ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a Φ.boundary)‖ ^ 2) ≤
        herglotzForm (Ws E) Φ.boundary E a := by
  have h := localConformalHerglotzForm_lower_of_normalizedBoundary Φ hγ hτ hcoord Ws hE hnr hΓLip hW hc ha hA₀ hbound
  
  nlinarith

/-- The number of direction conditions is exactly the given number of
normalized conditions. Instantiating it with originalNeumannMultiplicity
therefore retains the original complex spectral multiplicity. -/
theorem exists_localConformalHerglotz_boundary_conditions {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (Ws : ℝ → TransportPath) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) {KΓ : NNReal}
    (hΓLip : LipschitzWith KΓ Φ.boundary)
    (hW : IsTransport Φ.boundary E (Ws E))
    (hc : cutVector (Ws E) ≠ 0) {A₀ B : ℝ} (hA₀ : 0 ≤ A₀)
    (hB : ‖cutBE (Ws E)‖ ≤ B) {m : ℕ} (ℓ : L2Z →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ b : L2Z, ℓ b = 0 → -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
      (⟪b, normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E b⟫_ℂ).re) :
    ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
      -((A₀ / anglePeriod + B) * ‖observationAdj (Ws E)
        (herglotzConormal (Real.sqrt E) a Φ.boundary)‖ ^ 2) ≤ herglotzForm (Ws E) Φ.boundary E a := by
  obtain ⟨L, hconditions⟩ := exists_localConformalHerglotz_density_conditions hγ hτ (Real.sqrt E) ℓ
  refine ⟨L, fun a ha hLa => ?_⟩
  apply localConformalHerglotzForm_lower_of_normalizedBoundary_boundedCut Φ hγ hτ hcoord Ws hE hnr hΓLip hW hc ha hA₀ hB
  apply hbound
  exact (hconditions a ha).symm.trans hLa

/-- The same actual conditions give the original arclength-boundary
estimate when the proved reparametrization fixes the integration endpoints. -/
theorem exists_originalHerglotz_boundary_conditions_of_normalized {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (Ws : ℝ → TransportPath) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) {KΓ : NNReal}
    (hΓLip : LipschitzWith KΓ Φ.boundary)
    (hW : IsTransport Φ.boundary E (Ws E))
    (hc : cutVector (Ws E) ≠ 0) {Wγ : TransportPath} (hWγ : IsTransport γ E Wγ)
    {A₀ B : ℝ} (hA₀ : 0 ≤ A₀) (hB : ‖cutBE (Ws E)‖ ≤ B) {m : ℕ} (ℓ : L2Z →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ b : L2Z, ℓ b = 0 → -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
      (⟪b, normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E b⟫_ℂ).re) :
    ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
      -((A₀ / anglePeriod + B) * ‖observationAdj Wγ
        (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤ herglotzForm Wγ γ E a := by
  obtain ⟨L, hconditions⟩ := exists_localConformalHerglotz_boundary_conditions Φ hγ hτ hcoord Ws hE hnr hΓLip hW hc hA₀ hB ℓ hbound
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kτ, hKτ⟩ := hτ.lipschitz
  have hΓ : Φ.boundary = γ ∘ τ := by funext θ; exact hcoord θ
  have hWcomp : IsTransport (γ ∘ τ) E (Ws E) := by rw [← hΓ]; exact hW
  refine ⟨L, ?_⟩
  apply herglotz_density_lower_bound_of_comp hKγ
    hγ.periodic.eq hτ.monotone hKτ
    hτ.zero hτ.endpoint hWγ hWcomp L
  rw [← hΓ]
  exact hconditions

/-- The genuine normalized estimate transfers uniformly to the original
boundary with exactly the original complex multiplicity. Its constant
is A0/(2π) plus a derived uniform cut norm. No form identification or
unprojected observation on rough normalized data is a premise. -/
theorem exists_uniform_originalHerglotz_bound_of_normalized {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {KΓ : NNReal}
    (hΓLip : LipschitzWith KΓ Φ.boundary) (Ws : ℝ → TransportPath)
    (hWs : ∀ E, IsTransport Φ.boundary E (Ws E)) (E₀ : ℝ)
    (hc : cutVector (Ws E₀) ≠ 0)
    (hbound : ∃ A₀ δ₀ : ℝ, 0 < A₀ ∧ 0 < δ₀ ∧ ∀ E, 0 < E → |E - E₀| < δ₀ →
      (∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) →
      ∃ ℓ : L2Z →ₗ[ℂ] (Fin (originalNeumannMultiplicity Φ.domain E₀) → ℂ),
        ∀ b : L2Z, ℓ b = 0 → -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
          (⟪b, normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E b⟫_ℂ).re) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) →
      ∀ Wγ : TransportPath, IsTransport γ E Wγ →
        ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin (originalNeumannMultiplicity Φ.domain E₀) → ℂ),
          ∀ a, IsDirDensity a → L a = 0 →
            -(A * ‖observationAdj Wγ (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
              herglotzForm Wγ γ E a := by
  obtain ⟨A₀, δ₀, hA₀, hδ₀, hnormalized⟩ := hbound
  obtain ⟨B, ρ, hB, hρ, hcutBound⟩ := exists_herglotzCut_uniform_bound hΓLip Ws hWs E₀ hc
  refine ⟨A₀ / anglePeriod + B, min δ₀ ρ,
    (by positivity), lt_min hδ₀ hρ, ?_⟩
  intro E hE hnear hnr Wγ hWγ
  have hnear₀ := lt_of_lt_of_le hnear (min_le_left δ₀ ρ)
  have hnearρ := lt_of_lt_of_le hnear (min_le_right δ₀ ρ)
  obtain ⟨hcE, hBE⟩ := hcutBound E hnearρ
  obtain ⟨ℓ, hℓ⟩ := hnormalized E hE hnear₀ hnr
  exact exists_originalHerglotz_boundary_conditions_of_normalized Φ hγ hτ hcoord Ws hE.le hnr hΓLip (hWs E) hcE hWγ hA₀.le hBE ℓ hℓ

end

end Coordinates
end PolyaNeumann
end
