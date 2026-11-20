module

public import RequestProject.LocalConformalNormalizedResidueBasis
public import RequestProject.LocalConformalPeriodicBoundaryNull
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
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann

open Set MeasureTheory Filter Metric Real
open scoped InnerProductSpace ComplexConjugate Topology

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

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
    simp  [ha, hb]
    exact congrFun (herglotzConormal_add_density a.property b.property k γ) θ
  map_smul' c a := by
    apply Lp.ext
    filter_upwards [herglotzConormalL2_ae hγ (c • a).property k,
      herglotzConormalL2_ae hγ a.property k,
      Lp.coeFn_smul c (herglotzConormalL2 hγ a.property k)] with θ hca ha hs
    simp  
    rw [hca, hs]
    simp  [Pi.smul_apply, ha]
    exact congrFun (herglotzConormal_smul_density a.property c k γ) θ

section

variable {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
include τ c hτ

/-- Genuine Jacobian transport of ordinary L2 loads as a linear map. -/
def traceReparamConormalLinearMap  : BoundaryL2 →ₗ[ℂ] BoundaryL2 where
  toFun := traceReparamConormalL2 hτ
  map_add' g h := by
    apply Lp.ext
    have hadd := isC1TraceReparam_ae_comp hτ (Lp.coeFn_add g h)
    filter_upwards [traceReparamConormalL2_ae hτ (g + h),
      traceReparamConormalL2_ae hτ g, traceReparamConormalL2_ae hτ h,
      Lp.coeFn_add (traceReparamConormalL2 hτ g) (traceReparamConormalL2 hτ h),
      hadd] with θ hab hg hh hs hc
    rw [hab, hs]
    simp_all
  map_smul' a g := by
    apply Lp.ext
    have hsmul := isC1TraceReparam_ae_comp hτ (Lp.coeFn_smul a g)
    filter_upwards [traceReparamConormalL2_ae hτ (a • g),
      traceReparamConormalL2_ae hτ g,
      Lp.coeFn_smul a (traceReparamConormalL2 hτ g), hsmul] with θ hag hg hs hc
    simp  [RingHom.id_apply]
    rw [hag, hs]
    simp  [Pi.smul_apply, hg, hc]
    exact smul_comm (deriv τ θ) a (g (τ θ))

/-- The actual normalized weak-load map, with the physical Jacobian. -/
def localConformalBoundaryLoadLinearMap  : BoundaryL2 →ₗ[ℂ] L2Z :=
  (sobolevSmoothing (1 / 2 : ℝ) (by norm_num)).toLinearMap.comp
    (boundaryFourier.toLinearMap.comp (traceReparamConormalLinearMap hτ))

end

section

variable {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) (k : ℝ)
include Ω γ hγ τ c hτ k

/-- Direction densities give the actual physical conormal followed by its
true Jacobian transport and its unitary Fourier normalization. -/
def localConformalHerglotzBoundaryLin  : dirDensities →ₗ[ℂ] L2Z :=
  (localConformalBoundaryLoadLinearMap hτ).comp (herglotzConormalBoundaryLin hγ k)

/-- Extension to arbitrary direction functions does not change any
condition on the genuine density subspace. -/
theorem exists_localConformalHerglotz_density_conditions  {m : ℕ}
    (ℓ : L2Z →ₗ[ℂ] (Fin m → ℂ)) :
    ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a (ha : IsDirDensity a),
      L a = ℓ (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha k)) := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend
    (ℓ.comp (localConformalHerglotzBoundaryLin hγ hτ k))
  refine ⟨L, fun a ha => ?_⟩
  exact congrArg (fun T => T ⟨a, ha⟩) hL

end

/-- The actual bounded cut correction has one uniform norm bound near
a nonzero cut, derived from the genuine energy-dependent transport. -/
theorem exists_herglotzCut_uniform_bound {δ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K δ) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    (hWs : ∀ E, IsTransport δ E (Ws E)) (E₀ : ℝ)
    (hc : cutC (Ws E₀ (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ B ρ : ℝ, 0 < B ∧ 0 < ρ ∧ ∀ E, |E - E₀| < ρ →
      cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0 ∧ ‖cutBE (Ws E)‖ ≤ B := by
  have hB :=
    ((tendsto_cutBE_energy hK hWs E₀ hc).norm.eventually
      (gt_mem_nhds (by linarith : ‖cutBE (Ws E₀)‖ < ‖cutBE (Ws E₀)‖ + 1))).mono
        fun _ h => h.le
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
    ((eventually_cutC_ne hK hWs E₀ hc).and hB)
  refine ⟨‖cutBE (Ws E₀)‖ + 1, ρ, by positivity, hρ, fun E hE => ?_⟩
  exact hsub (mem_ball.mpr (id hE))

section Coordinates

variable (F : ℂ → ℂ) (coords : ConformalDiskCoordinates F)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "ΓF" => physicalCircleTrace F
local notation "QF" => coords.halfTrace

private theorem herglotz_transfer_observationAdj_congr_ae
    (W : ℝ → Ell2 →L[ℂ] Ell2) {g h : ℝ → ℂ} (he : g =ᵐ[μB] h) :
    observationAdj W g = observationAdj W h := by
  rw [observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply integral_congr_ae
  filter_upwards [he] with θ hθ
  tauto

include hcoord in
/-- The unitary weak-load scale of the projected observation. The
unprojected integral is evaluated only on the true conormal density. -/
theorem localConformalHerglotzBoundary_projObsDual
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    (Real.sqrt (2 * Real.pi) : ℂ) • projObsDual W
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
        (observationAdj W (herglotzConormal (Real.sqrt E) a ΓF)) := by
  rw [localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha]
  rw [← map_smul]
  have h := projObsDual_boundary_normalized hΓLip hW
    (localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E))
  rw [herglotz_transfer_observationAdj_congr_ae W
    (localConformalHerglotzCoordinateLoad_ae F hΓLip ha (Real.sqrt E))] at h
  assumption

include hcoord in
theorem localConformalHerglotzBoundary_projObsDual_norm_sq
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    (2 * Real.pi) * ‖projObsDual W
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))‖ ^ 2 =
      ‖cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
        (observationAdj W (herglotzConormal (Real.sqrt E) a ΓF))‖ ^ 2 := by
  have hn := congrArg (fun v : Ell2 => ‖v‖ ^ 2)
    (localConformalHerglotzBoundary_projObsDual F hγ hτ hcoord hΓLip hW ha)
  simpa only [norm_smul, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt Real.two_pi_pos.le] using hn

/-- The Volterra and observation integrals depend only on the actual
load's a.e. class on the cut. -/
private theorem periodicP_congr_at {W : ℝ → Ell2 →L[ℂ] Ell2}
    {n n' g g' : ℝ → ℂ} (hg : g =ᵐ[μB] g') {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) (hn : n θ = n' θ) :
    periodicP W n g θ = periodicP W n' g' θ := by
  have ha := (ae_restrict_iff' measurableSet_Ioc).mp hg
  have hv {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] (k : ℝ → ℂ → H)
      {a b : ℝ} (hab : uIoc a b ⊆ Ioc 0 (2 * Real.pi)) :
      ∫ s in a..b, k s (g s) = ∫ s in a..b, k s (g' s) :=
    intervalIntegral.integral_congr_ae (ha.mono fun s hs hmem => congrArg (k s) (hs (hab hmem)))
  simp  [periodicP, periodicA, volterraOp, volterraOpAdj, observationAdj, hn]
  have h₁ := hv (a := 0) (b := θ) (fun s x => volterraKernel W θ s * x)
    (by grind)
  have h₂ := hv (a := θ) (b := 2 * Real.pi) (fun s x => starRingEnd ℂ (volterraKernel W s θ) * x)
    (by grind)
  have h₃ := hv (a := 0) (b := 2 * Real.pi)
    (fun s x => x • (ContinuousLinearMap.adjoint (W s)) (basisVec 0)) (by rw [uIoc_of_le Real.two_pi_pos.le])
  simp_all

variable {F}

include hcoord in
/-- The exact complex ordinary-boundary pairing equals the full
normalized pairing for the unitary weak load, with no factor 2π. -/
theorem normalizedPeriodicBoundaryFamily_herglotz_inner
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))
    ⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ =
      l2Inner (herglotzConormal (Real.sqrt E) a ΓF)
        (periodicP (Ws E) (fun θ => herglotzWave (Real.sqrt E) a (ΓF θ))
          (herglotzConormal (Real.sqrt E) a ΓF)) := by
  let g := localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E)
  let u := herglotzWaveH1 coords.bounded ha (Real.sqrt E)
  let t := coords.trace u
  let S := sobolevSmoothing (1 / 2) (by norm_num)
  let p := periodicBoundaryL2 hΓLip hW hc t g
  have hload := localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha (Real.sqrt E)
  have hu := localConformalHerglotz_isNormalizedNeumannSolution coords
    hγ hτ hcoord hE ha
  rw [hload] at hu
  have hfour :=
    normalizedPeriodicBoundaryFamily_fourier_of_solution coords.one_lt_radius F coords.smooth coords.bounded coords.lipschitz Ws hE hnr hΓLip hW hc g u hu
  have hS : IsSelfAdjoint S := by
    unfold S sobolevSmoothing
    apply diagOp_isSelfAdjoint
    simp
  dsimp 
  rw [hload]
  change ⟪S (boundaryFourier g), _⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hS,
    ← hfour, LinearIsometryEquiv.inner_map_map, l2Inner,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply integral_congr_ae
  have hg := localConformalHerglotzCoordinateLoad_ae F hΓLip ha (Real.sqrt E)
  filter_upwards [periodicBoundaryL2_ae hΓLip hW hc t g,
    localConformalHerglotz_coordinate_trace_ae coords hγ hτ hcoord ha (Real.sqrt E),
    hg, ae_restrict_mem measurableSet_Ioc] with θ hp ht hx hθ
  have he := periodicP_congr_at (W := Ws E) (n := (t : ℝ → ℂ))
    (n' := fun θ => herglotzWave (Real.sqrt E) a (ΓF θ))
    (show (g : ℝ → ℂ) =ᵐ[μB] _ from hg) (Ioc_subset_Icc_self hθ) ht
  change p θ * star (g θ) = _
  rw [show p θ = _ from hp, he, show g θ = _ from hx, mul_comm]
  rfl

include hcoord in
/-- The sharp normalization in the fixed-energy transfer is A0/(2π).
The remaining correction is the norm of the actual bounded cut operator. -/
theorem localConformalHerglotzForm_lower_of_normalizedBoundary
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hbound : let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E));
      -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
        (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    -((A₀ / (2 * Real.pi) + ‖cutBE (Ws E)‖) *
      ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖ ^ 2) ≤
        herglotzForm (Ws E) ΓF E a := by
  dsimp  at hbound
  have hn := localConformalHerglotzBoundary_projObsDual_norm_sq F hγ hτ hcoord hΓLip hW ha
  have hn' : ‖projObsDual (Ws E)
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))‖ ^ 2 =
      ‖cutProj (cutC (Ws E (2 * Real.pi)) (basisVec 0))
        (observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF))‖ ^ 2 /
          (2 * Real.pi) := by
    apply (eq_div_iff Real.two_pi_pos.ne').mpr
    simpa only [mul_comm] using hn
  rw [hn', normalizedPeriodicBoundaryFamily_herglotz_inner coords
    hγ hτ hcoord Ws hE hnr hΓLip hW hc ha] at hbound
  apply herglotzForm_lower_of_periodicP_lower hΓLip
    (by simpa only [zero_add] using physicalCircleTrace_periodic F 0) hW ha
    (div_nonneg hA₀ Real.two_pi_pos.le)
  convert hbound using 1; ring

include hγ hτ hcoord in
/-- The genuine normalized estimate transfers uniformly to the original
boundary with exactly the original complex multiplicity. Its constant
is A0/(2π) plus a derived uniform cut norm. No form identification or
unprojected observation on rough normalized data is a premise. -/
theorem exists_uniform_originalHerglotz_bound_of_normalized
    {KΓ : NNReal} (hΓLip : LipschitzWith KΓ ΓF)
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (hWs : ∀ E, IsTransport ΓF E (Ws E))
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
  obtain ⟨B, ρ, hB, hρ, hcutBound⟩ := exists_herglotzCut_uniform_bound hΓLip Ws hWs E₀ hc
  refine ⟨A₀ / (2 * Real.pi) + B, min δ₀ ρ,
    add_pos (div_pos hA₀ Real.two_pi_pos) hB, lt_min hδ₀ hρ, ?_⟩
  intro E hE hnear hnr Wγ hWγ
  obtain ⟨hcE, hBE⟩ := hcutBound E (hnear.trans_le (min_le_right _ _))
  obtain ⟨ℓ, hℓ⟩ := hnormalized E hE (hnear.trans_le (min_le_left _ _)) hnr
  obtain ⟨L, hL'⟩ := exists_localConformalHerglotz_density_conditions hγ hτ (Real.sqrt E) ℓ
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kτ, hKτ⟩ := hτ.lipschitz
  have hΓ : ΓF = γ ∘ τ := funext hcoord
  refine ⟨L, herglotz_density_lower_bound_of_comp hKγ
    (by simpa only [zero_add] using hγ.periodic 0) hτ.monotone hKτ hτ.zero hτ.endpoint
    hWγ (hΓ ▸ hWs E) L ?_⟩
  rw [← hΓ]
  intro a ha hLa
  have h := localConformalHerglotzForm_lower_of_normalizedBoundary coords hγ hτ hcoord Ws hE.le hnr hΓLip (hWs E) hcE ha hA₀.le
    (hℓ _ ((hL' a ha).symm.trans hLa))
  have hm := mul_le_mul_of_nonneg_right hBE (sq_nonneg
    ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖)
  nlinarith

end Coordinates
end PolyaNeumann
end
