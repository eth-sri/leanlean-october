module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientWeakTest

/-!
# Coordinate derivative of the localized spatial energy test

This module records the coefficient-free coordinate derivative of the bundled
localized spatial difference-quotient energy test.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

theorem sq_tsupport_subset
    {d : ℕ} {inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) :
    tsupport η.sq.toFun ⊆ tsupport η.toFun := by
  simpa only [PDE.QuantitativeSmoothCutoff.sq_toFun, pow_two] using
    (tsupport_mul_subset_left (f := η.toFun) (g := η.toFun))

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
  (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : η.ShiftMapsInto k h Ω) (j : Fin d) (y : PDE.Vec d)

/-- Differentiation commutes with the backward quotient in the localized energy test. -/
theorem energyWeakTest_partialDeriv_eq_backwardSquare :
    PDE.WeakTestFunction.partialDeriv
      (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) j y =
      ((localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((sq_tsupport_subset η).trans hηΩ)).partialDeriv j
          (y + (-h) • PDE.basisVec k) -
        (localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((sq_tsupport_subset η).trans hηΩ)).partialDeriv j y) / h := by
  let ψ := localizedSpatialDifferenceQuotientWeakTest η.sq k h φ ((sq_tsupport_subset η).trans hηΩ)
  have hψ : Differentiable ℝ (ψ : PDE.Vec d → ℝ) := ψ.contDiff.differentiable (by simp)
  have hshift : DifferentiableAt ℝ (fun x : PDE.Vec d => ψ (x + (-h) • PDE.basisVec k)) y :=
    (hψ.comp (differentiable_id.add_const _)) y
  have heq : localizedSpatialDifferenceQuotientEnergyTest η k h φ =
      fun x => h⁻¹ • (ψ (x + (-h) • PDE.basisVec k) - ψ x) := by
    ext x
    simp only [ψ, localizedSpatialDifferenceQuotientEnergyTest_apply,
      localizedSpatialDifferenceQuotient_apply, localizedSpatialDifferenceQuotientWeakTest_apply,
      PDE.QuantitativeSmoothCutoff.sq_toFun, pow_two, neg_smul, sub_eq_add_neg, smul_eq_mul]
    ring
  change (fderiv ℝ (localizedSpatialDifferenceQuotientEnergyTest η k h φ) y) (PDE.basisVec j) = _
  have hq : DifferentiableAt ℝ (fun x : PDE.Vec d => ψ (x + (-h) • PDE.basisVec k) - ψ x) y :=
    hshift.sub (hψ y)
  rw [heq, fderiv_fun_const_smul hq, fderiv_fun_sub hshift (hψ y),
    fderiv_comp_add_right, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
  change h⁻¹ * (ψ.partialDeriv j (y + (-h) • PDE.basisVec k) - ψ.partialDeriv j y) = _
  rw [div_eq_inv_mul]

/-- The localized energy test has the literal translated coordinate product
rule, with the totalized backward quotient at signed step `-h`. -/
theorem localizedSpatialDifferenceQuotientEnergyWeakTest_partialDeriv :
    (localizedSpatialDifferenceQuotientEnergyWeakTest
      η k h φ φ.contDiff hηΩ hηshift).partialDeriv j y =
      ((2 * η (y + (-h) • PDE.basisVec k) *
            PDE.classicalGradient η.toFun (y + (-h) • PDE.basisVec k) j *
            ((φ (y + (-h) • PDE.basisVec k + h • PDE.basisVec k) -
                φ (y + (-h) • PDE.basisVec k)) / h) +
          η (y + (-h) • PDE.basisVec k) ^ 2 *
            ((φ.partialDeriv j
                (y + (-h) • PDE.basisVec k + h • PDE.basisVec k) -
              φ.partialDeriv j (y + (-h) • PDE.basisVec k)) / h)) -
        (2 * η y * PDE.classicalGradient η.toFun y j *
            ((φ (y + h • PDE.basisVec k) - φ y) / h) +
          η y ^ 2 *
            ((φ.partialDeriv j (y + h • PDE.basisVec k) -
              φ.partialDeriv j y) / h))) / h := by
  rw [energyWeakTest_partialDeriv_eq_backwardSquare η k h φ hηΩ hηshift j y]
  rw [localizedSpatialDifferenceQuotientWeakTest_partialDeriv η.sq k h φ
      ((sq_tsupport_subset η).trans hηΩ) j (y + (-h) • PDE.basisVec k)]
  rw [localizedSpatialDifferenceQuotientWeakTest_partialDeriv η.sq k h φ
      ((sq_tsupport_subset η).trans hηΩ) j y]
  simp only [PDE.QuantitativeSmoothCutoff.sq_apply,
    PDE.QuantitativeSmoothCutoff.sq_classicalGradient, Pi.smul_apply, smul_eq_mul]

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
