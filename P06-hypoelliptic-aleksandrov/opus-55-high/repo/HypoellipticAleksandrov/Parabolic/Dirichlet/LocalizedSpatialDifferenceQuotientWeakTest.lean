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
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω) :
    PDE.WeakTestFunction Ω where
  toFun := localizedSpatialDifferenceQuotient η k h φ
  contDiff := ContDiff.localizedSpatialDifferenceQuotient φ.contDiff η k h
  hasCompactSupport := localizedSpatialDifferenceQuotient_hasCompactSupport η k h φ
  tsupport_subset :=
    (tsupport_localizedSpatialDifferenceQuotient_subset η k h φ).trans hηΩ

variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)

/-- The bundled localized quotient has the literal pointwise value. -/
@[simp] theorem localizedSpatialDifferenceQuotientWeakTest_apply
     (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω) (y : PDE.Vec d) :
    localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ y =
      η y * ((φ (y + h • PDE.basisVec k) - φ y) / h) :=
  rfl

/-- The coordinate derivative of the bundled localized quotient obeys the
literal cutoff product rule. -/
theorem localizedSpatialDifferenceQuotientWeakTest_partialDeriv
     (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (j : Fin d) (y : PDE.Vec d) :
    (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ).partialDeriv j y =
      PDE.classicalGradient η.toFun y j *
          ((φ (y + h • PDE.basisVec k) - φ y) / h) +
        η y *
          ((φ.partialDeriv j (y + h • PDE.basisVec k) -
              φ.partialDeriv j y) / h) := by
  change (fderiv ℝ (fun x : PDE.Vec d =>
    η x * ((φ _ - φ x) / h)) y) _ = _
  have hφshift : DifferentiableAt ℝ
      (fun x : PDE.Vec d => φ (x + h • PDE.basisVec k)) y :=
    (φ.contDiff.comp (contDiff_id.add contDiff_const)).contDiffAt.differentiableAt (by simp)
  have hφ : DifferentiableAt ℝ φ y :=
    φ.contDiff.contDiffAt.differentiableAt (by simp)
  let q  := fun x =>
    φ (x + h • PDE.basisVec k) - φ x
  have hq : DifferentiableAt ℝ q y := by
    fun_prop
  have hquotient : DifferentiableAt ℝ
      (fun x : PDE.Vec d => (φ (x + h • PDE.basisVec k) - φ x) / h) y :=
    by
      fun_prop
  rw [fderiv_fun_mul
    (η.smooth.contDiffAt.differentiableAt (by simp)) hquotient]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, PDE.classicalGradient_apply]
  have hquotientDeriv :
      (fderiv ℝ (fun x : PDE.Vec d =>
        (φ (x + h • PDE.basisVec k) - φ x) / h) y) (PDE.basisVec j) =
        (φ.partialDeriv j (y + h • PDE.basisVec k) - φ.partialDeriv j y) / h := by
    have hrewrite : (fun x : PDE.Vec d =>
        (φ (x + h • PDE.basisVec k) - φ x) / h) =
        fun x => h⁻¹ • q x := by
      funext x
      ring
    rw [hrewrite, fderiv_fun_const_smul hq h⁻¹]
    have hqderiv : (fderiv ℝ q y) (PDE.basisVec j) =
        φ.partialDeriv j (y + h • PDE.basisVec k) - φ.partialDeriv j y := by
      rw [fderiv_fun_sub hφshift hφ, fderiv_comp_add_right]
      rfl
    rw [ContinuousLinearMap.smul_apply, hqderiv]
    ring
  rw [hquotientDeriv]
  ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
