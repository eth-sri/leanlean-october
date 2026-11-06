module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientWeakTest

/-!
# Coordinate derivative of the localized spatial energy test

This module records the coefficient-free coordinate derivative of the bundled
localized spatial difference-quotient energy test.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)

theorem sq_tsupport_subset
     {inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) :
    tsupport η.sq.toFun ⊆ tsupport η.toFun := by
  simpa only [PDE.QuantitativeSmoothCutoff.sq_toFun, pow_two] using
    (tsupport_mul_subset_left (f := η.toFun) (g := η.toFun))

theorem energyWeakTest_partialDeriv_eq_backwardSquare
    
    (φ : PDE.WeakTestFunction Ω) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (j : Fin d) (y : PDE.Vec d) :
    PDE.WeakTestFunction.partialDeriv
      (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) j y =
      ((localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((sq_tsupport_subset η).trans hηΩ)).partialDeriv j
          (y + (-h) • PDE.basisVec k) -
        (localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((sq_tsupport_subset η).trans hηΩ)).partialDeriv j y) / h := by
  let ψ := localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
    ((sq_tsupport_subset η).trans hηΩ)
  have hψshift : DifferentiableAt ℝ
      (fun x : PDE.Vec d => ψ (x + (-h) • PDE.basisVec k)) y :=
    (ψ.contDiff.comp (contDiff_id.add contDiff_const)).contDiffAt.differentiableAt (by simp)
  have hψ : DifferentiableAt ℝ ψ y :=
    ψ.contDiff.contDiffAt.differentiableAt (by simp)
  let q  := fun x =>
    ψ (x + (-h) • PDE.basisVec k) - ψ x
  have hq : DifferentiableAt ℝ q y := hψshift.sub hψ
  have hrewrite : localizedSpatialDifferenceQuotientEnergyTest η k h φ =
      fun x : PDE.Vec d => (ψ (x + (-h) • PDE.basisVec k) - ψ x) / h := by
    funext x
    dsimp only [ψ]
    simp only [localizedSpatialDifferenceQuotientEnergyTest_apply,
      localizedSpatialDifferenceQuotient_apply,
      localizedSpatialDifferenceQuotientWeakTest_apply,
      PDE.QuantitativeSmoothCutoff.sq_toFun]
    rw [neg_smul]
    ring
  change (fderiv ℝ (localizedSpatialDifferenceQuotientEnergyTest η k h φ) y)
      _ = _
  rw [hrewrite]
  have hquotient : (fun x : PDE.Vec d =>
      (ψ (x + (-h) • PDE.basisVec k) - ψ x) / h) = fun x => h⁻¹ • q x := by
    funext x
    ring
  rw [hquotient, fderiv_fun_const_smul hq h⁻¹]
  have hqderiv : (fderiv ℝ q y) (PDE.basisVec j) =
      ψ.partialDeriv j (y + (-h) • PDE.basisVec k) - ψ.partialDeriv j y := by
    rw [fderiv_fun_sub hψshift hψ, fderiv_comp_add_right]
    rfl
  rw [ContinuousLinearMap.smul_apply, hqderiv]
  ring

/-- The localized energy test has the literal translated coordinate product
rule, with the totalized backward quotient at signed step `-h`. -/
theorem localizedSpatialDifferenceQuotientEnergyWeakTest_partialDeriv
     (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (j : Fin d) (y : PDE.Vec d) :
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
  rw [energyWeakTest_partialDeriv_eq_backwardSquare, localizedSpatialDifferenceQuotientWeakTest_partialDeriv]
  rw [localizedSpatialDifferenceQuotientWeakTest_partialDeriv]
  simp only [PDE.QuantitativeSmoothCutoff.sq_apply,
    PDE.QuantitativeSmoothCutoff.sq_classicalGradient, Pi.smul_apply, smul_eq_mul]

end HypoellipticAleksandrov.Parabolic.Dirichlet
