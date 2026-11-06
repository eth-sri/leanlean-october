module

public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives

open private HypoellipticAleksandrov.Parabolic.spatialShift_measurableEmbedding from HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives


/-!
# Restricted Lp membership under spatial quotients

This module transports restricted `Lᵖ` membership through spatial translations
and totalized spatial difference quotients at a fixed signed step.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}




variable {U V : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞} {f : HypoellipticAleksandrov.Parabolic.ScalarField d} (hf : ParabolicMemLpOn U p f) (k : Fin d) (h : ℝ)

include hf
/-- Restricted `Lᵖ` membership transports through a spatial translation from
a domain mapped into the original carrier. -/
theorem ParabolicMemLpOn.spatialTranslate_of_mapsTo

    (hshift : Set.MapsTo (spatialShift k h) V U) :
    ParabolicMemLpOn V p (spatialTranslate k h f) := (MemLp.mono_measure (Measure.restrict_mono_set volume hshift)
  (MemLp.comp_measurePreserving hf
    (MeasurePreserving.restrict_preimage_emb (spatialShift_measurePreserving k h) (spatialShift_measurableEmbedding k h)
      U)))

/-- Restricted `Lᵖ` membership transports to a totalized signed spatial
difference quotient on a shifted subdomain. -/
theorem ParabolicMemLpOn.spatialDifferenceQuotient_of_subset_mapsTo

    (hVU : V ⊆ U)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    ParabolicMemLpOn V p (spatialDifferenceQuotient k h f) := by



  convert ((hf.spatialTranslate_of_mapsTo k h hshift).sub (hf.mono_measure (Measure.restrict_mono_set volume hVU))).const_smul h⁻¹ using 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, spatialDifferenceQuotient_apply,
    Pi.sub_apply, div_eq_mul_inv]
  ring_nf

end HypoellipticAleksandrov.Parabolic
