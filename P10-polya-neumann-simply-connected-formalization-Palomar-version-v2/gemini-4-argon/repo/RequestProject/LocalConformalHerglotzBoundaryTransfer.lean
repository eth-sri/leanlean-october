module

public import RequestProject.LocalConformalNormalizedResidueBasis
public import RequestProject.HerglotzReparam
public import RequestProject.ObservationLp
public import RequestProject.PhysicalHardyWeights
public import Mathlib.Analysis.Real.Pi.Bounds

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
noncomputable section
namespace PolyaNeumann

open Set MeasureTheory Filter Metric Real
open scoped InnerProductSpace ComplexConjugate Topology ContDiff


variable {a : ℝ → ℂ} {L : NNReal} {A₀ B : ℝ}

/-- The actual physical conormal L2 class is linear on direction densities. -/
def herglotzConormalBoundaryLin  
    (hγ : IsBoundaryParam Ω γ) (k : ℝ) : dirDensities →ₗ[ℂ] BoundaryL2 where
  toFun a := herglotzConormalL2 hγ a.property k
  map_add' a b := by
    apply Lp.ext
    filter_upwards [herglotzConormalL2_ae hγ (a + b).property k,
      herglotzConormalL2_ae hγ a.property k, herglotzConormalL2_ae hγ b.property k,
      Lp.coeFn_add (herglotzConormalL2 hγ a.property k)
        (herglotzConormalL2 hγ b.property k)] with θ hab ha hb hs
    rw [hab, hs]
    simp [ha, hb]
    exact congrFun (herglotzConormal_add_density a.property b.property k γ) θ
  map_smul' c a := by
    apply Lp.ext
    filter_upwards [herglotzConormalL2_ae hγ (c • a).property k,
      herglotzConormalL2_ae hγ a.property k,
      Lp.coeFn_smul c (herglotzConormalL2 hγ a.property k)] with θ hca ha hs
    simp
    rw [hca, hs]
    simp [ha]
    exact congrFun (herglotzConormal_smul_density a.property c k γ) θ

/-- Genuine Jacobian transport of ordinary L2 loads as a linear map. -/
def traceReparamConormalLinearMap  
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

/-- Direction densities give the actual physical conormal followed by its
true Jacobian transport and its unitary Fourier normalization. -/
def localConformalHerglotzBoundaryLin  
    (hγ : IsBoundaryParam Ω γ)  
    (hτ : IsC1TraceReparam τ c) (k : ℝ) : dirDensities →ₗ[ℂ] L2Z :=
  ((sobolevSmoothing (1 / 2 : ℝ) (by norm_num)).toLinearMap.comp (boundaryFourier.toLinearMap.comp (traceReparamConormalLinearMap hτ))).comp (herglotzConormalBoundaryLin hγ k)

section Coordinates

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
local notation "ΓF" => physicalCircleTrace F
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL

private theorem herglotz_transfer_observationAdj_congr_ae
    W  (he : g =ᵐ[(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))] h) :
    observationAdj W g = observationAdj W h := by
  rw [observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply integral_congr_ae
  filter_upwards [he] with θ hθ
  rw [hθ]

include hcoord in
/-- The unitary weak-load scale of the projected observation. The
unprojected integral is evaluated only on the true conormal density. -/
theorem localConformalHerglotzBoundary_projObsDual
     (hΓLip : LipschitzWith L ΓF) 
     (hW : IsTransport ΓF E W)
     (ha : IsDirDensity a) :
    (Real.sqrt (2 * Real.pi) : ℂ) • projObsDual W
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
        (observationAdj W (herglotzConormal (Real.sqrt E) a ΓF)) := by
  rw [localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha, ← map_smul]
  have h := projObsDual_boundary_normalized hΓLip hW
    (localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E))
  rw [herglotz_transfer_observationAdj_congr_ae W
    (localConformalHerglotzCoordinateLoad_ae F hΓLip ha (Real.sqrt E))] at h
  exact h

include hcoord in
theorem localConformalHerglotzBoundary_projObsDual_norm_sq
     (hΓLip : LipschitzWith L ΓF) {E : ℝ}
     (hW : IsTransport ΓF E W)
     (ha : IsDirDensity a) :
    2 * Real.pi * ‖projObsDual W
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))‖ ^ 2 =
      ‖cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
        (observationAdj W (herglotzConormal (Real.sqrt E) a ΓF))‖ ^ 2 := by
  have hn := congrArg (fun v => ‖v‖ ^ 2)
    (localConformalHerglotzBoundary_projObsDual F hγ hτ hcoord hΓLip hW ha)
  simpa only [norm_smul, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt Real.two_pi_pos.le] using hn

include hR hFs in
private theorem herglotz_transfer_kernel_summable
     (hΓLip : LipschitzWith L ΓF) 
     (hW : IsTransport ΓF E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2 := by
  obtain ⟨B, hB⟩ := ((contDiff_physicalCircleTrace_four_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))).of_le (by norm_num)).deriv'.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
  exact summable_correctedRemainderMatrix hΓLip (by
    intro x hx y hy
    have h := hB.dist_le_mul x hx y hy
    rwa [dist_eq_norm, Real.dist_eq] at h) hW hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

include hb hhol hinj hC hcoord in
/-- The actual full family on a Herglotz load is its true corrected
observation adjoint. Nonresonance removes precisely the genuine form
kernel, rather than suppressing the constant Fourier mode. -/
theorem normalizedPeriodicBoundaryFamily_herglotz_eq
    Ws  (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
     (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
     (ha : IsDirDensity a) :
    normalizedPeriodicBoundaryFamily QF Ws E
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      (Real.sqrt (2 * Real.pi) : ℂ) • ContinuousLinearMap.adjoint (projObsDual (Ws E))
        (regularHerglotzObservationVector (γ := ΓF) E (Ws E) ha) := by
  have hunit := h1HelmholtzForm_isUnit hb hL hE hnr
  have hbase := herglotz_transfer_kernel_summable hR F hFs hΓLip hW hc
  rw [normalizedPeriodicBoundaryFamily_eq_regular_at_nonresonant_reference QF hb hL Ws hE hunit,
    normalizedPeriodicRegularFamily_eq QF E E Ws hbase, normalizedPeriodicRegularOperator_herglotz_eq hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord hΓLip hE hW hc ha hbase,
    h1Resonant_starProjection_eq_zero_of_form_isUnit hunit, map_zero, smul_zero, sub_zero]

private theorem herglotz_transfer_periodic_inner
    {δ : ℝ → ℂ}  (hK : LipschitzWith K δ)
    (hclosed : δ (2 * Real.pi) = δ 0) 
     (hW : IsTransport δ E W)
     (ha : IsDirDensity a) :
    l2Inner (herglotzConormal (Real.sqrt E) a δ)
      (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (δ θ))
        (herglotzConormal (Real.sqrt E) a δ)) =
      ⟪observationAdj W (herglotzConormal (Real.sqrt E) a δ),
        regularHerglotzObservationVector (γ := δ) E W ha⟫_ℂ := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  rw [inner_observationAdj hW.1 hgm hgB]
  unfold l2Inner
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le Real.two_pi_pos.le] at hθ
  change conj (herglotzConormal (Real.sqrt E) a δ θ) *
      periodicP W (fun s => herglotzWave (Real.sqrt E) a (δ s))
        (herglotzConormal (Real.sqrt E) a δ) θ = _
  rw [periodicP_herglotz_eq_regularObservation hK hclosed hW ha hθ]

include hb hhol hinj hC hcoord in
/-- The exact complex ordinary-boundary pairing equals the full
normalized pairing for the unitary weak load, with no factor 2π. -/
theorem normalizedPeriodicBoundaryFamily_herglotz_inner
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)  (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
     (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
     (ha : IsDirDensity a) :
    let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))
    ⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ =
      l2Inner (herglotzConormal (Real.sqrt E) a ΓF)
        (periodicP (Ws E) (fun θ => herglotzWave (Real.sqrt E) a (ΓF θ))
          (herglotzConormal (Real.sqrt E) a ΓF)) := by
  dsimp only
  rw [normalizedPeriodicBoundaryFamily_herglotz_eq hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord Ws hE hnr hΓLip hW hc ha,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
  have hclosed : ΓF (2 * Real.pi) = ΓF 0 := by
    simpa using physicalCircleTrace_periodic F 0
  calc
    _ = ⟪(Real.sqrt (2 * Real.pi) : ℂ) • projObsDual (Ws E)
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))),
          regularHerglotzObservationVector (γ := ΓF) E (Ws E) ha⟫_ℂ := by
      rw [inner_smul_left, Complex.conj_ofReal]
    _ = ⟪observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF),
        regularHerglotzObservationVector (γ := ΓF) E (Ws E) ha⟫_ℂ := by
      rw [localConformalHerglotzBoundary_projObsDual F hγ hτ hcoord hΓLip hW ha, inner_cutProj_left, regularHerglotzObservationVector_cutProj hΓLip hclosed hW hc ha]
    _ = _ := (herglotz_transfer_periodic_inner hΓLip hclosed hW ha).symm

include hb hhol hinj hC hcoord in
/-- The sharp normalization in the fixed-energy transfer is A0/(2π).
The remaining correction is the norm of the actual bounded cut operator. -/
theorem localConformalHerglotzForm_lower_of_normalizedBoundary
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)  (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
     (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
     (ha : IsDirDensity a)  (hA₀ : 0 ≤ A₀)
    (hbound : let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E));
      -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
        (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    -((A₀ / (2 * Real.pi) + ‖cutBE (Ws E)‖) *
      ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖ ^ 2) ≤
        herglotzForm (Ws E) ΓF E a := by
  dsimp only at hbound
  rw [show ‖projObsDual (Ws E) (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))‖ ^ 2 = ‖cutProj (cutC (Ws E (2 * Real.pi)) (basisVec 0)) (observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF))‖ ^ 2 / (2 * Real.pi) by
    apply (eq_div_iff Real.two_pi_pos.ne').mpr
    simpa [mul_comm] using localConformalHerglotzBoundary_projObsDual_norm_sq F hγ hτ hcoord hΓLip hW ha, normalizedPeriodicBoundaryFamily_herglotz_inner hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord Ws hE hnr hΓLip hW hc ha] at hbound
  apply herglotzForm_lower_of_periodicP_lower hΓLip
    (by simpa using physicalCircleTrace_periodic F 0) hW ha
    (div_nonneg hA₀ Real.two_pi_pos.le)
  convert hbound using 1; ring

include hb hhol hinj hC hcoord in
theorem localConformalHerglotzForm_lower_of_normalizedBoundary_boundedCut
    Ws  (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
     (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
     (ha : IsDirDensity a)  (hA₀ : 0 ≤ A₀)
    (hB : ‖cutBE (Ws E)‖ ≤ B)
    (hbound : let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E));
      -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
        (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    -((A₀ / (2 * Real.pi) + B) *
      ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖ ^ 2) ≤
        herglotzForm (Ws E) ΓF E a := by
  have h := localConformalHerglotzForm_lower_of_normalizedBoundary hR F hFs hb hL hhol
    hinj hC hγ hτ hcoord Ws hE hnr hΓLip hW hc ha hA₀ hbound
  have hm := mul_le_mul_of_nonneg_right hB (sq_nonneg
    ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖)
  nlinarith

include hb hhol hinj hC hγ hτ hcoord in
/-- The number of direction conditions is exactly the given number of
normalized conditions. Instantiating it with originalNeumannMultiplicity
therefore retains the original complex spectral multiplicity. -/
theorem exists_localConformalHerglotz_boundary_conditions
    Ws  (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {KΓ : NNReal} (hΓLip : LipschitzWith KΓ ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
     (hA₀ : 0 ≤ A₀) (hB : ‖cutBE (Ws E)‖ ≤ B) {m : ℕ}
    (ℓ : L2Z →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ b : L2Z, ℓ b = 0 → -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
      (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
      -((A₀ / (2 * Real.pi) + B) * ‖observationAdj (Ws E)
        (herglotzConormal (Real.sqrt E) a ΓF)‖ ^ 2) ≤ herglotzForm (Ws E) ΓF E a := by
  obtain ⟨L, hconditions⟩ : ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a (ha : IsDirDensity a), L a = ℓ (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) := by
    obtain ⟨L, hL⟩ := LinearMap.exists_extend
      (ℓ.comp (localConformalHerglotzBoundaryLin hγ hτ (Real.sqrt E)))
    refine ⟨L, fun a ha => ?_⟩
    exact congrArg (fun T => T ⟨a, ha⟩) hL
  refine ⟨L, fun a ha hLa => ?_⟩
  apply localConformalHerglotzForm_lower_of_normalizedBoundary_boundedCut hR F hFs hb hL
    hhol hinj hC hγ hτ hcoord Ws hE hnr hΓLip hW hc ha hA₀ hB
  apply hbound
  exact (hconditions a ha).symm.trans hLa

include hb hhol hinj hC hγ hτ hcoord in
/-- The same actual conditions give the original arclength-boundary
estimate when the proved reparametrization fixes the integration endpoints. -/
theorem exists_originalHerglotz_boundary_conditions_of_normalized
    Ws  (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {KΓ} (hΓLip : LipschitzWith KΓ ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {Wγ} (hWγ : IsTransport γ E Wγ)
     (hA₀ : 0 ≤ A₀) (hB : ‖cutBE (Ws E)‖ ≤ B) 
    (ℓ : L2Z →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ b : L2Z, ℓ b = 0 → -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
      (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
      -((A₀ / (2 * Real.pi) + B) * ‖observationAdj Wγ
        (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤ herglotzForm Wγ γ E a := by
  obtain ⟨L, hconditions⟩ := exists_localConformalHerglotz_boundary_conditions hR F hFs hb hL
    hhol hinj hC hγ hτ hcoord Ws hE hnr hΓLip hW hc hA₀ hB ℓ hbound
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kτ, hKτ⟩ := hτ.lipschitz
  have hΓ : ΓF = γ ∘ τ := by funext θ; exact hcoord θ
  refine ⟨L, ?_⟩
  apply herglotz_density_lower_bound_of_comp hKγ
    (by simpa using hγ.periodic 0) hτ.monotone hKτ
    hτ.zero hτ.endpoint hWγ (by rw [← hΓ]; exact hW) L
  rw [← hΓ]
  exact hconditions

include hb hhol hinj hC hγ hτ hcoord in
/-- The genuine normalized estimate transfers uniformly to the original
boundary with exactly the original complex multiplicity. Its constant
is A0/(2π) plus a derived uniform cut norm. No form identification or
unprojected observation on rough normalized data is a premise. -/
theorem exists_uniform_originalHerglotz_bound_of_normalized
    {KΓ} (hΓLip : LipschitzWith KΓ ΓF)
    Ws (hWs : ∀ E, IsTransport ΓF E (Ws E))
    (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * Real.pi)) (basisVec 0) ≠ 0)
    (hbound : ∃ A₀ δ₀ : ℝ, 0 < A₀ ∧ 0 < δ₀ ∧ ∀ E, 0 < E → |E - E₀| < δ₀ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∃ ℓ : L2Z →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
        ∀ b : L2Z, ℓ b = 0 → -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
          (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∀ Wγ : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E Wγ →
        ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
          ∀ a, IsDirDensity a → L a = 0 →
            -(A * ‖observationAdj Wγ (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
              herglotzForm Wγ γ E a := by
  obtain ⟨A₀, δ₀, hA₀, hδ₀, hnormalized⟩ := hbound
  obtain ⟨B, ρ, hB, hρ, hcutBound⟩ : ∃ B ρ : ℝ, 0 < B ∧ 0 < ρ ∧ ∀ E, |E - E₀| < ρ → cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0 ∧ ‖cutBE (Ws E)‖ ≤ B := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
      ((eventually_cutC_ne hΓLip hWs E₀ hc).and (((tendsto_cutBE_energy hΓLip hWs E₀ hc).norm.eventually (gt_mem_nhds (by linarith : ‖cutBE (Ws E₀)‖ < ‖cutBE (Ws E₀)‖ + 1))).mono fun _ h => h.le))
    refine ⟨‖cutBE (Ws E₀)‖ + 1, ρ, by positivity, hρ, fun E hE => ?_⟩
    exact hsub (mem_ball.mpr (by simpa [Real.dist_eq] using hE))
  refine ⟨A₀ / (2 * Real.pi) + B, min δ₀ ρ,
    add_pos (div_pos hA₀ Real.two_pi_pos) hB, lt_min hδ₀ hρ, ?_⟩
  intro E hE hnear hnr Wγ hWγ
  obtain ⟨hcE, hBE⟩ := hcutBound E (lt_of_lt_of_le hnear (min_le_right δ₀ ρ))
  obtain ⟨ℓ, hℓ⟩ := hnormalized E hE (lt_of_lt_of_le hnear (min_le_left δ₀ ρ)) hnr
  exact exists_originalHerglotz_boundary_conditions_of_normalized hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord Ws hE.le hnr hΓLip (hWs E) hcE hWγ hA₀.le hBE ℓ hℓ

end Coordinates
end PolyaNeumann
end
