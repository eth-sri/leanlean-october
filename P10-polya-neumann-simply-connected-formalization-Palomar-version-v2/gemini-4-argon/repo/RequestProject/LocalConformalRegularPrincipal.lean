module

public import RequestProject.LocalConformalForcedModes
public import RequestProject.LocalConformalPrincipalFactorization
public import RequestProject.NeumannProjectedWeak

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real InnerProductSpace ComplexConjugate ContDiff

variable {E₀ E : ℝ}

private theorem forced_remainder_scalar 
    (hk : k ≠ 0) (hs : s ≠ 0) (hsk : s = k + 1)
     (h : t - ((s / k : ℝ) : ℂ) * b = d) :
    t - b = (s : ℂ)⁻¹ *
      (((s / k : ℝ) : ℂ) * b + (s : ℂ) * d) := by
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hskc : (s : ℂ) = (k : ℂ) + 1 := by exact_mod_cast hsk
  calc
    _ = (s / k : ℝ) * b - b + d := by linear_combination h
    _ = _ := by
      simp [hskc]
      field_simp [(by exact_mod_cast hk), show (k : ℂ) + 1 ≠ 0 by rwa [hskc] at hsc]
      ring

private theorem forced_remainder_mode n (hn : n ≠ 0)
     (h : t - normalizedInverseAbsSymbol n * b = d) :
    t - b = (sobWeight n : ℂ)⁻¹ *
      (normalizedInverseAbsSymbol n * b + (sobWeight n : ℂ) * d) := by
  simp only [normalizedInverseAbsSymbol, if_neg hn] at h ⊢
  exact forced_remainder_scalar (abs_ne_zero.mpr (by exact_mod_cast hn)) ((sobWeight_pos n).ne') (by unfold sobWeight; ring) h

private theorem forced_principal_factorization_of_modes
    T M (d : L2Z → ℤ → ℂ)
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
    have h_inl b n : sobolevSmoothing 1 (by norm_num) b n = (sobWeight n : ℂ)⁻¹ * b n := by simp [sobolevSmoothing, Real.rpow_neg_one]
    h_inl, normalizedInverseAbsOperator_apply,
    zeroModeProjection_apply, lp.coeFn_sub, lp.coeFn_add,
    Pi.sub_apply, Pi.add_apply, hM]
  by_cases hn : n = 0
  · subst n
    simp [normalizedInverseAbsSymbol, hz]
  · rw [if_neg hn, zero_mul, add_zero]
    exact forced_remainder_mode n hn (hm b n hn)

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

/-- The actual mass input of the projected regular weak equation. -/
local notation "Φ2" => ball 0 1

def localConformalRegularMassInput (E₀ E : ℝ) :
    L2Z →L[ℂ] NeumannH1 (F '' Φ2) :=
  (((E : ℂ) • h1RegularResolvent (F '' Φ2) E₀ E) -
    ((E₀ + 1 : ℝ) : ℂ) • (h1ResonantSpace (F '' Φ2) E₀).starProjection).comp
      (ContinuousLinearMap.adjoint (localConformalDiskHalfTrace hR F hFs hL))

/-- The actual regular interior solution satisfies the general forced
weak equation with the genuine projected mass input above. -/
local notation "Φ0" => localConformalDiskHalfTrace hR F hFs hL

theorem localConformalRegular_isForcedSolution  (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' Φ2) E₀ E)) b :
    IsNormalizedNeumannForcedSolution (Φ0) b
      (h1RegularResolvent (F '' Φ2) E₀ E
        (ContinuousLinearMap.adjoint (Φ0) b))
      (localConformalRegularMassInput hR F hFs hL E₀ E b) := by
  intro v
  simp only [localConformalRegularMassInput, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    map_sub, map_smul, inner_sub_right, inner_smul_right]
  linear_combination (h1RegularResolvent_adjoint_weak_pairing (Φ0) hE₀ hunit b v)

/-- The bounded factor before the compact one-derivative smoothing in
the actual regular normalized NtD remainder. -/
def localConformalRegularPrincipalFactor (E₀ E : ℝ) : L2Z →L[ℂ] L2Z :=
  normalizedInverseAbsOperator + (localConformalMassFourierH1 hR F hFs hL hK).comp
    (localConformalRegularMassInput hR F hFs hL E₀ E)




local notation "Φ1" => localConformalRegularMassInput hR F hFs hL E₀ E
include hb hhol hinj hC e he hsource hes in
theorem isCompactOperator_localConformal_normalizedNeumannRegular_sub_one
     (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' Φ2) E₀ E)) :
    IsCompactOperator
      (normalizedNeumannRegular (localConformalDiskHalfTrace hR F hFs hL) E₀ E -
        (1 : L2Z →L[ℂ] L2Z)) := by
  obtain ⟨K, _, hK⟩ := exists_localConformalMassDensity_bound hR F hFs
  have h_inl : normalizedNeumannRegular (Φ0) E₀ E - 1 = (sobolevSmoothing 1 (by norm_num)).comp (localConformalRegularPrincipalFactor hR F hFs hL hK E₀ E) + zeroModeProjection.comp (normalizedNeumannRegular (Φ0) E₀ E - 1) := by
    refine forced_principal_factorization_of_modes
      (normalizedNeumannRegular (Φ0) E₀ E)
      ((localConformalMassFourierH1 hR F hFs hL hK).comp
        (Φ1))
      (fun b n => diskMassForcingCoeff (localConformalMassForcing hR F hFs hL hK
        (Φ1 b)) n) ?_ ?_ ?_
    · intro b n
      simp
    · intro b
      simp [diskMassForcingCoeff]
    · intro b n hn
      have hm := localConformal_forced_principal_mode_ne_zero hR F hFs hb hL hhol hinj hC hK
        e he hsource hes b
        (h1RegularResolvent (F '' Φ2) E₀ E
          (ContinuousLinearMap.adjoint (Φ0) b))
        (Φ1 b) (localConformalRegular_isForcedSolution hR F hFs hL hE₀ hunit b) n hn
      simpa [normalizedNeumannRegular, normalizedInverseAbsSymbol, if_neg hn] using hm
  rw [h_inl]
  exact ((isCompactOperator_sobolevSmoothing (by norm_num : (0 : ℝ) < 1)).comp_clm
    (localConformalRegularPrincipalFactor hR F hFs hL hK E₀ E)).add
      (isCompactOperator_zeroModeProjection.comp_clm
        (normalizedNeumannRegular (Φ0) E₀ E - 1))

end

end PolyaNeumann

end
