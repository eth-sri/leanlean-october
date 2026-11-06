module

public import HypoellipticAleksandrov.Parabolic.SpatialTranslationLocalIntegrability
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra

/-!
# Weak derivatives of spatial difference quotients

This module combines raw spatial translation, local-integrability transport,
restriction, and weak-derivative algebra on arbitrary time--velocity sets.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

/-- A weak velocity derivative commutes with a spatial difference quotient
on a domain supporting both the original and translated relations. -/
theorem HasWeakVelocityPartialDerivOn.spatialDifferenceQuotient_of_subset_mapsTo
    {d : ℕ} {U V : HypoellipticAleksandrov.Parabolic.Region d} {i : Fin d}
    {u dui : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduiLoc : LocallyIntegrableOn dui U volume)
    (k : Fin d) (h : ℝ)
    (hVU : V ⊆ U)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    HasWeakVelocityPartialDerivOn V i
      (spatialDifferenceQuotient k h u)
      (spatialDifferenceQuotient k h dui) := by






  have hsub := (hu.spatialTranslate_of_mapsTo k h hshift).sub (hu.restrict hVU) (LocallyIntegrableOn.spatialTranslate_of_mapsTo huLoc k h hshift) (LocallyIntegrableOn.spatialTranslate_of_mapsTo hduiLoc k h hshift)
    (huLoc.mono_set hVU) (hduiLoc.mono_set hVU)

  convert (hsub.smul h⁻¹) using 1 <;> ext z <;>
    simp only [spatialDifferenceQuotient_apply, Pi.smul_apply, smul_eq_mul,
      div_eq_mul_inv] <;> ring

end HypoellipticAleksandrov.Parabolic
