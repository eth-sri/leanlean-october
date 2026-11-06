module

public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Restricted Lp membership under spatial quotients

This module transports restricted `Lᵖ` membership through spatial translations
and totalized spatial difference quotients at a fixed signed step.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

theorem ParabolicMemLpOn.spatialTranslate_of_mapsTo
    {d U V p f}
    (hf : ParabolicMemLpOn U p f)
    (k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    ParabolicMemLpOn V p (spatialTranslate k h f) := by
  have _h_inl_7 : MeasurableEmbedding (spatialShift k h) := by
    change MeasurableEmbedding (fun z : TimeVelocity d => z + (0, h • PDE.basisVec k))
    simpa only [Homeomorph.coe_addRight] using
      (Homeomorph.addRight
        ((0, h • PDE.basisVec k) : TimeVelocity d)).measurableEmbedding
  exact (hf.comp_measurePreserving ((spatialShift_measurePreserving k h).restrict_preimage_emb _h_inl_7 U)).mono_measure (Measure.restrict_mono_set volume hshift)

/- Restricted `Lᵖ` membership transports to a totalized signed spatial
difference quotient on a shifted subdomain. -/
theorem ParabolicMemLpOn.spatialDifferenceQuotient_of_subset_mapsTo
    {d U V p f}
    (hf : ParabolicMemLpOn U p f)
    (k : Fin d) (h : ℝ)
    (hVU : V ⊆ U)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    ParabolicMemLpOn V p (spatialDifferenceQuotient k h f) := by
  convert ((hf.spatialTranslate_of_mapsTo k h hshift).sub (hf.mono_measure (Measure.restrict_mono_set volume hVU))).const_smul h⁻¹ using 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, spatialDifferenceQuotient_apply,
    Pi.sub_apply, div_eq_mul_inv]
  ring_nf

end HypoellipticAleksandrov.Parabolic
