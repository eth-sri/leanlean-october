module

public import RequestProject.DiskHardyDerivative


public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter

private theorem forced_remainder_scalar 
    (hk : k ≠ 0) (hs : s ≠ 0) (hsk : s = k + 1)
     (h : t - ((s / k : ℝ) : ℂ) * b = d) :
    t - b = (s : ℂ)⁻¹ *
      (((s / k : ℝ) : ℂ) * b + (s : ℂ) * d) := by
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hskc : (s : ℂ) = (k : ℂ) + 1 := by exact_mod_cast hsk
  have hsc' : (k : ℂ) + 1 ≠ 0 := by rwa [hskc] at hsc
  calc
    t - b = ((s / k : ℝ)) * b - b + d := by linear_combination h
    _ = _ := by
      simp  [hskc]
      field_simp [hkc]
      ring

private theorem forced_remainder_mode n (hn : n ≠ 0)
     (h : t - normalizedInverseAbsSymbol n * b = d) :
    t - b = (sobWeight n : ℂ)⁻¹ *
      (normalizedInverseAbsSymbol n * b + (sobWeight n : ℂ) * d) := by
  have hk : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hn)
  grind [sobWeight, normalizedInverseAbsSymbol, forced_remainder_scalar, PolyaNeumann.sobWeight, PolyaNeumann.normalizedInverseAbsSymbol]

private theorem forced_principal_factorization_of_modes
    (T M : L2Z →L[ℂ] L2Z) (d : L2Z → FourierSeq)
    (hM : ∀ b n, M b n = (sobWeight n : ℂ) * d b n)
    (hz : ∀ b, d b 0 = 0)
    (hm : ∀ b n, n ≠ 0 → T b n - normalizedInverseAbsSymbol n * b n = d b n) :
    T - 1 = (sobolevSmoothing 1 (by norm_num)).comp
      (normalizedInverseAbsOperator + M) + zeroModeProjection.comp (T - 1) := by
  apply ContinuousLinearMap.ext
  intro b
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, common_derivative_smoothing_one_apply, zeroModeProjection_apply, lp.coeFn_add, Pi.add_apply, hM]
  by_cases hn : n = 0
  · subst n
    simp [normalizedInverseAbsSymbol, hz]
  · rw [if_neg hn, zero_mul, add_zero]
    exact forced_remainder_mode n hn (hm b n hn)

section

variable {R } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) {C K }
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
local notation "diskHalfTraceFixed" => localConformalDiskHalfTrace hR F hFs hL


/-- The actual mass input of the projected regular weak equation. -/
def localConformalRegularMassInput (E₀ E : ℝ) :
    L2Z →L[ℂ] NeumannH1 (F '' unitDisk) :=
  (((E : ℂ) • h1RegularResolvent (F '' unitDisk) E₀ E) -
    ((E₀ + 1 : ℝ) : ℂ) • (h1ResonantSpace (F '' unitDisk) E₀).starProjection).comp
      (ContinuousLinearMap.adjoint diskHalfTraceFixed)

section
variable {E₀ E : ℝ} (hE₀ : 0 ≤ E₀) (hunit : IsUnit (h1ComplementForm (F '' unitDisk) E₀ E))

include E₀ E hE₀ hunit in
/-- The actual regular interior solution satisfies the general forced
weak equation with the genuine projected mass input above. -/
theorem localConformalRegular_isForcedSolution (b : L2Z) :
    IsNormalizedNeumannForcedSolution diskHalfTraceFixed b
      (h1RegularResolvent (F '' unitDisk) E₀ E
        (ContinuousLinearMap.adjoint diskHalfTraceFixed b))
      (localConformalRegularMassInput hR F hFs hL E₀ E b) := by
  intro v
  have h := h1RegularResolvent_adjoint_weak_pairing
    diskHalfTraceFixed hE₀ hunit b v
  simp only [localConformalRegularMassInput, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    map_sub, map_smul, inner_sub_right, inner_smul_right]
  linear_combination h

/-- The bounded factor before the compact one-derivative smoothing in
the actual regular normalized NtD remainder. -/
def localConformalRegularPrincipalFactor (E₀ E : ℝ) : L2Z →L[ℂ] L2Z :=
  normalizedInverseAbsOperator + (localConformalMassFourierH1 hR F hFs hL hK).comp
    (localConformalRegularMassInput hR F hFs hL E₀ E)

section
include hb hhol hinj hC e he hsource hes E₀ E hE₀ hunit

theorem localConformal_regular_principal_factorization :
    normalizedNeumannRegular diskHalfTraceFixed E₀ E - 1 =
      (sobolevSmoothing 1 (by norm_num)).comp
        (localConformalRegularPrincipalFactor hR F hFs hL hK E₀ E) +
      zeroModeProjection.comp
        (normalizedNeumannRegular diskHalfTraceFixed E₀ E - 1) := by
  refine forced_principal_factorization_of_modes
    (normalizedNeumannRegular diskHalfTraceFixed E₀ E)
    ((localConformalMassFourierH1 hR F hFs hL hK).comp
      (localConformalRegularMassInput hR F hFs hL E₀ E))
    (fun b n => diskMassForcingCoeff (localConformalMassForcing hR F hFs hL hK
      (localConformalRegularMassInput hR F hFs hL E₀ E b)) n) ?_ ?_ ?_
  · intros; rfl
  · intros; rfl
  · intro b n hn
    have hforced := localConformalRegular_isForcedSolution hR F hFs hL hE₀ hunit b
    have hm := localConformal_forced_principal_mode_ne_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b
      (h1RegularResolvent (F '' ball 0 1) E₀ E
        (ContinuousLinearMap.adjoint diskHalfTraceFixed b))
      (localConformalRegularMassInput hR F hFs hL E₀ E b) hforced n hn
    simpa only [normalizedNeumannRegular, ContinuousLinearMap.comp_apply,
      normalizedInverseAbsSymbol, if_neg hn] using hm

theorem isCompactOperator_localConformal_normalizedNeumannRegular_sub_one :
    IsCompactOperator
      (normalizedNeumannRegular diskHalfTraceFixed E₀ E -
        (1 : L2Z →L[ℂ] L2Z)) := by
  obtain ⟨K, _, hK⟩ := exists_localConformalMassDensity_bound hR F hFs
  rw [localConformal_regular_principal_factorization hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hE₀ hunit]
  exact ((isCompactOperator_sobolevSmoothing (by norm_num)).comp_clm
    (localConformalRegularPrincipalFactor hR F hFs hL hK E₀ E)).add
      (isCompactOperator_zeroModeProjection.comp_clm
        (normalizedNeumannRegular diskHalfTraceFixed E₀ E - 1))

end


end


end

end PolyaNeumann

end
