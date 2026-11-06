module

public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local integrability under spatial translation

This module transports raw-set local integrability through native spatial
translations on domains mapped forward into the original domain.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

/-- Raw-set local integrability transports through a spatial translation on
any domain sent into the original domain. -/
theorem LocallyIntegrableOn.spatialTranslate_of_mapsTo
    {d : ℕ} {U V : HypoellipticAleksandrov.Parabolic.Region d}
    {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hf : LocallyIntegrableOn f U ) (k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    LocallyIntegrableOn (spatialTranslate k h f) V  := (fun x hx =>
  Exists.casesOn (hf (spatialShift k h x) (hshift hx)) fun s h_1 =>
    And.casesOn h_1 fun hs hfs =>
      Exists.intro (spatialShift k h ⁻¹' s)
        ⟨ContinuousWithinAt.preimage_mem_nhdsWithin'
            (Continuous.continuousWithinAt (id (Homeomorph.continuous (Homeomorph.addRight (0, h • PDE.basisVec k)))))
            (nhdsWithin_mono (spatialShift k h x) (Set.MapsTo.image_subset hshift) hs),
          id
            ((MeasurePreserving.integrableOn_comp_preimage (spatialShift_measurePreserving k h)
                  (id (Homeomorph.measurableEmbedding (Homeomorph.addRight (0, h • PDE.basisVec k))))).mpr
              hfs)⟩)

end HypoellipticAleksandrov.Parabolic
