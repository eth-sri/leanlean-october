module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientWeakTest
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyTestH10

open private HypoellipticAleksandrov.Parabolic.Dirichlet.sq_tsupport_subset from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyTestH10
section
open private HypoellipticAleksandrov.Parabolic.Dirichlet.energyWeakTest_partialDeriv_eq_backwardSquare from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyTestH10
private alias _sharedProof_35_0 := HypoellipticAleksandrov.Parabolic.Dirichlet.energyWeakTest_partialDeriv_eq_backwardSquare
end


/-!
# Coordinate derivative of the localized spatial energy test

This module records the coefficient-free coordinate derivative of the bundled
localized spatial difference-quotient energy test.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}




variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω) (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω) (j : Fin d) (y : PDE.Vec d)

private theorem energyWeakTest_partialDeriv_eq_backwardSquare
      :
    PDE.WeakTestFunction.partialDeriv
      (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) j y =
      ((localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.sq_tsupport_subset η).trans hηΩ)).partialDeriv j
          (y + (-h) • PDE.basisVec k) -
        (localizedSpatialDifferenceQuotientWeakTest η.sq k h φ
          ((_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.sq_tsupport_subset η).trans hηΩ)).partialDeriv j y) / h := (_sharedProof_35_0 η k h φ hηΩ hηshift j y)


/-- The localized energy test has the literal translated coordinate product
rule, with the totalized backward quotient at signed step `-h`. -/
theorem localizedSpatialDifferenceQuotientEnergyWeakTest_partialDeriv
      :
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
      ((_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.sq_tsupport_subset η).trans hηΩ) j (y + (-h) • PDE.basisVec k)]
  rw [localizedSpatialDifferenceQuotientWeakTest_partialDeriv η.sq k h φ
      ((_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.sq_tsupport_subset η).trans hηΩ) j y]
  simp only [PDE.QuantitativeSmoothCutoff.sq_apply,
    PDE.QuantitativeSmoothCutoff.sq_classicalGradient, Pi.smul_apply, smul_eq_mul]

end HypoellipticAleksandrov.Parabolic.Dirichlet
