module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalForcedModes
public import RequestProject.LocalConformalPrincipalFactorization
public import RequestProject.NeumannProjectedWeak
public import RequestProject.DiskHardyDerivative
public import RequestProject.PlanarNotation

/-!
# The actual regular Neumann principal part in supplied conformal coordinates

The projected weak equation has physical mass forcing
`E • u_reg - (E₀ + 1) • w`, where `w` is the actual resonant projection
of the load. Its harmonic tests give a factorization of the actual regular
normalized NtD remainder through one Fourier derivative. The zero mode is
retained by the genuine rank-one projection. The same zero-load tests give
the one-derivative factor of the actual Neumann residue.

Existence of the supplied smooth conformal coordinates is a separate
obligation; none of these statements adds coordinates to the final theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real InnerProductSpace ComplexConjugate

private theorem forced_remainder_scalar {s k : ℝ}
    (hk : k ≠ 0) (hs : s ≠ 0) (hsk : s = k + 1)
    {t b d : ℂ} (h : t - ((s / k : ℝ) : ℂ) * b = d) :
    t - b = (s : ℂ)⁻¹ *
      (((s / k : ℝ) : ℂ) * b + (s : ℂ) * d) := by
  
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hskc : s = (k : ℂ) + 1 := by exact_mod_cast hsk
  
  calc
    _ = ((s / k : ℝ) : ℂ) * b - b + d := by linear_combination h
    _ = _ := by
      simp [Complex.ofReal_div, hskc]
      field_simp [(by exact_mod_cast hk), (by rwa [hskc] at hsc)]
      ring

private theorem forced_remainder_mode (n : ℤ) (hn : n ≠ 0)
    {t b d : ℂ} (h : t - normalizedInverseAbsSymbol n * b = d) :
    t - b = (sobWeight n : ℂ)⁻¹ *
      (normalizedInverseAbsSymbol n * b + (sobWeight n : ℂ) * d) := by
  have hk : |(n : ℝ)| ≠ 0 := (by positivity)
  have hs  := (sobWeight_pos n).ne'
  
  simp only [normalizedInverseAbsSymbol, if_neg hn] at h ⊢
  refine forced_remainder_scalar hk hs ?_ h
  unfold sobWeight; ring

private theorem forced_principal_factorization_of_modes
    (T M : FourierOp) (d : L2Z → ℤ → ℂ)
    (hM : ∀ b n, M b n = (sobWeight n : ℂ) * d b n)
    (hz : ∀ b, d b 0 = 0)
    (hm : ∀ b n, n ≠ 0 → T b n - normalizedInverseAbsSymbol n * b n = d b n) :
    T - 1 = (sobolevSmoothing 1 (by norm_num)).comp
      (normalizedInverseAbsOperator + M) + zeroModeProjection.comp (T - 1) := by
  apply ContinuousLinearMap.ext
  intro b
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    derivative_smoothing_one_apply, normalizedInverseAbsOperator_apply,
    zeroModeProjection_apply, lp.coeFn_sub, lp.coeFn_add,
    Pi.sub_apply, Pi.add_apply, hM]
  by_cases hn : n = 0
  · subst n
    simp [normalizedInverseAbsSymbol, hz]
  · rw [if_neg hn, zero_mul, add_zero]
    exact forced_remainder_mode n hn (hm b n hn)

section

section

variable (Φ : SmoothDiskMap) (hL : IsLipschitzDomain Φ.domain)
include hL

/-- The actual mass input of the projected regular weak equation. -/
def SmoothDiskMap.regularMassInput (E₀ E : ℝ) :
    L2Z →L[ℂ] NeumannH1 Φ.domain :=
  (((E : ℂ) • h1RegularResolvent Φ.domain E₀ E) -
    ((E₀ + 1 : ℝ) : ℂ) • (h1ResonantSpace Φ.domain E₀).starProjection).comp
      (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL))

/-- The actual regular interior solution satisfies the general forced
weak equation with the genuine projected mass input above. -/
theorem localConformalRegular_isForcedSolution {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm Φ.domain E₀ E)) (b : L2Z) :
    IsNormalizedNeumannForcedSolution (Φ.pulledBackHalfTrace hL) b
      (h1RegularResolvent Φ.domain E₀ E
        (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL) b))
      (Φ.regularMassInput hL E₀ E b) := by
  intro v
  have h := h1RegularResolvent_adjoint_weak_pairing
    (Φ.pulledBackHalfTrace hL) hE₀ hunit b v
  simp only [SmoothDiskMap.regularMassInput, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    map_sub, map_smul, inner_sub_right, inner_smul_right]
  linear_combination h

/-- The bounded factor before the compact one-derivative smoothing in
the actual regular normalized NtD remainder. -/
def SmoothDiskMap.regularPrincipalFactor {K : ℝ} (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K)
    (E₀ E : ℝ) : FourierOp :=
  normalizedInverseAbsOperator + (Φ.massFourierH1 hL hK).comp
    (Φ.regularMassInput hL E₀ E)

end

theorem localConformal_regular_principal_factorization (Φ : DiskCoordinates) {E₀ E : ℝ}
    (hE₀ : 0 ≤ E₀) (hunit : IsUnit (h1ComplementForm Φ.domain E₀ E)) :
    normalizedNeumannRegular (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ E - 1 =
      (sobolevSmoothing 1 (by norm_num)).comp
        (Φ.regularPrincipalFactor Φ.lipschitzDomain Φ.deriv_upper E₀ E) +
      zeroModeProjection.comp
        (normalizedNeumannRegular (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ E - 1) := by
  refine forced_principal_factorization_of_modes
    (normalizedNeumannRegular (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ E)
    ((Φ.massFourierH1 Φ.lipschitzDomain Φ.deriv_upper).comp
      (Φ.regularMassInput Φ.lipschitzDomain E₀ E))
    (fun b n => diskMassForcingCoeff (Φ.massForcing Φ.lipschitzDomain Φ.deriv_upper
      (Φ.regularMassInput Φ.lipschitzDomain E₀ E b)) n) ?_ ?_ ?_
  · simp
  · simp [diskMassForcingCoeff]
  · intro b n hn
    have hforced := localConformalRegular_isForcedSolution Φ Φ.lipschitzDomain hE₀ hunit b
    have hm := localConformal_forced_principal_mode_ne_zero Φ b
      (h1RegularResolvent Φ.domain E₀ E
        (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace Φ.lipschitzDomain) b))
      (Φ.regularMassInput Φ.lipschitzDomain E₀ E b) hforced n hn
    simpa only [normalizedNeumannRegular, ContinuousLinearMap.comp_apply,
      normalizedInverseAbsSymbol, if_neg hn] using hm

theorem isCompactOperator_localConformal_normalizedNeumannRegular_sub_one (Φ : ConformalDiskMap)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = Φ.map) (hsource : closedDisk ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm Φ.domain E₀ E)) :
    IsCompactOperator
      (normalizedNeumannRegular (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ E -
        (1 : FourierOp)) := by
  obtain ⟨K, _, hK⟩ := exists_localConformalMassDensity_bound Φ
  rw [localConformal_regular_principal_factorization ⟨⟨Φ, hK⟩, e, he, hsource, hes⟩ hE₀ hunit]
  exact ((isCompactOperator_sobolevSmoothing (by norm_num : (0 : ℝ) < 1)).comp_clm
    (Φ.regularPrincipalFactor Φ.lipschitzDomain hK E₀ E)).add
      (isCompactOperator_zeroModeProjection.comp_clm
        (normalizedNeumannRegular (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E₀ E - 1))

end

end PolyaNeumann

end
