module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPointwise

/-!
# Localized spatial quotient smooth tests

This module bundles the cutoff-weighted forward spatial difference quotient of
a smooth compactly supported test and records its coordinate weak derivative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The localized forward quotient of a bundled smooth test, supported by the
cutoff inside the raw carrier. -/
def localizedSpatialDifferenceQuotientWeakTest
    {d : ℕ} {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω) :
    PDE.WeakTestFunction Ω where
  toFun := localizedSpatialDifferenceQuotient η k h φ
  contDiff := ContDiff.localizedSpatialDifferenceQuotient φ.contDiff η k h
  hasCompactSupport := localizedSpatialDifferenceQuotient_hasCompactSupport η k h φ
  tsupport_subset :=
    (tsupport_localizedSpatialDifferenceQuotient_subset η k h φ).trans hηΩ

variable {d : ℕ} {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω) (hηΩ : tsupport η.toFun ⊆ Ω)

/-- The bundled localized quotient has the literal pointwise value. -/
@[simp] theorem localizedSpatialDifferenceQuotientWeakTest_apply
     (y : PDE.Vec d) :
    localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ y =
      η y * ((φ (y + h • PDE.basisVec k) - φ y) / h) :=
  rfl

/-- The coordinate derivative of the bundled localized quotient obeys the
literal cutoff product rule. -/
theorem localizedSpatialDifferenceQuotientWeakTest_partialDeriv

    (j : Fin d) (y : PDE.Vec d) :
    (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ).partialDeriv j y =
      PDE.classicalGradient η.toFun y j *
          ((φ (y + h • PDE.basisVec k) - φ y) / h) +
        η y *
          ((φ.partialDeriv j (y + h • PDE.basisVec k) -
              φ.partialDeriv j y) / h) := by
  let sharedTerm_53a1a6cadb := ((fun x : PDE.Vec d => (φ (x + h • PDE.basisVec k) - φ x) / h))
  unfold PDE.WeakTestFunction.partialDeriv localizedSpatialDifferenceQuotientWeakTest
  change (fderiv ℝ (fun x  =>
    η x * ((φ (x + h • PDE.basisVec k) - φ x) / h)) y) (PDE.basisVec j) = _
  have hφshift : DifferentiableAt ℝ
      (fun x  => φ (x + h • PDE.basisVec k)) y :=
    (φ.contDiff.comp (contDiff_id.add contDiff_const)).contDiffAt.differentiableAt (by simp)
  have hφ : DifferentiableAt ℝ (φ : PDE.ScalarField d) y :=
    φ.contDiff.contDiffAt.differentiableAt (by simp)
  let q  := fun x =>
    φ (x + h • PDE.basisVec k) - φ x
  have hq : DifferentiableAt ℝ q y := hφshift.sub hφ

  rw [fderiv_fun_mul
    (η.smooth.contDiffAt.differentiableAt (by simp)) (by
        convert hq.const_smul h⁻¹ using 1
        funext x
        simp only [q, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
        ring)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, PDE.classicalGradient_apply]
  have hquotientDeriv :
      (fderiv ℝ sharedTerm_53a1a6cadb y) (PDE.basisVec j) =
        (φ.partialDeriv j (y + h • PDE.basisVec k) - φ.partialDeriv j y) / h := by
    have hrewrite : (sharedTerm_53a1a6cadb) =
        fun x => h⁻¹ • q x := by
      funext x
      simp only [q, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hrewrite, fderiv_fun_const_smul hq h⁻¹]
    have hqderiv : (fderiv ℝ q y) (PDE.basisVec j) =
        φ.partialDeriv j (y + h • PDE.basisVec k) - φ.partialDeriv j y := by
      dsimp only [q]
      rw [fderiv_fun_sub hφshift hφ, fderiv_comp_add_right]
      rfl
    rw [ContinuousLinearMap.smul_apply, hqderiv]
    simp only [PDE.WeakTestFunction.partialDeriv,
      PDE.WeakTestFunction.partialDeriv, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hquotientDeriv]
  simp only [PDE.WeakTestFunction.partialDeriv]
  ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
