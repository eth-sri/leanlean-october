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

section
variable {d : ℕ} {U V : Set (TimeVelocity d)} {p : ℝ≥0∞} {f : TimeVelocity d → ℝ}
  (hf : ParabolicMemLpOn U p f) (k : Fin d) (h : ℝ)
include hf

/-- Restricted `Lᵖ` membership transports through a spatial translation from
a domain mapped into the original carrier. -/
theorem ParabolicMemLpOn.spatialTranslate_of_mapsTo
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    ParabolicMemLpOn V p (spatialTranslate k h f) := by
  have hpre : MemLp (f ∘ spatialShift k h) p
      ((volume : Measure (TimeVelocity d)).restrict
        (spatialShift k h ⁻¹' U)) :=
    hf.comp_measurePreserving
      ((spatialShift_measurePreserving k h).restrict_preimage_emb
        (_root_.HypoellipticAleksandrov.Parabolic.spatialShift_measurableEmbedding k h) U)
  have hsub : V ⊆ spatialShift k h ⁻¹' U := hshift
  exact hpre.mono_measure (Measure.restrict_mono_set volume hsub)

/-- Restricted `Lᵖ` membership transports to a totalized signed spatial
difference quotient on a shifted subdomain. -/
theorem ParabolicMemLpOn.spatialDifferenceQuotient_of_subset_mapsTo
    (hVU : V ⊆ U)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    ParabolicMemLpOn V p (spatialDifferenceQuotient k h f) := by
  rw [spatialDifferenceQuotient_eq_smul]
  exact ((hf.spatialTranslate_of_mapsTo k h hshift).sub
    (hf.mono_measure (Measure.restrict_mono_set volume hVU))).const_smul _

end

/-- A global spatial difference quotient of an `Lᵖ` representative is in `Lᵖ`. -/
theorem memLp_spatialDifferenceQuotient {d : ℕ} {p : ℝ≥0∞} {f : TimeVelocity d → ℝ}
    (hf : MemLp f p volume) (k : Fin d) (h : ℝ) : MemLp (spatialDifferenceQuotient k h f) p volume := by
  rw [spatialDifferenceQuotient_eq_smul]
  exact ((hf.comp_measurePreserving (spatialShift_measurePreserving k h)).sub hf).const_smul _

end HypoellipticAleksandrov.Parabolic
