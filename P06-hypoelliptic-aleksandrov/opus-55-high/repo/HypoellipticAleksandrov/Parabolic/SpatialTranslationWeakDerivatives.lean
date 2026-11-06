module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Spatial translation of raw weak derivatives

This module transports the representative-level weak time and velocity
derivative identities through native spatial translations.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal Topology

variable {d : ℕ} (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ) (z : TimeVelocity d)

theorem spatialShift_neg_comp_apply
     :
    spatialShift k (-h) (spatialShift k h z) = z := by
  aesop

theorem spatialShift_comp_neg_apply
     :
    spatialShift k h (spatialShift k (-h) z) = z := by
  aesop

theorem spatialShift_measurableEmbedding
     :
    MeasurableEmbedding (spatialShift k h) := by
  change MeasurableEmbedding (fun z => z + (0, h • PDE.basisVec k))
  simpa using
    (Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d)).measurableEmbedding

/-- A native coordinate spatial shift preserves product Lebesgue volume. -/
theorem spatialShift_measurePreserving
     :
    MeasurePreserving (spatialShift k h)
      (volume : Measure (TimeVelocity d))
      (volume : Measure (TimeVelocity d)) := measurePreserving_add_right volume _

/-- Time differentiation commutes exactly with spatial translation. -/
@[simp] theorem timeDerivative_spatialTranslate
     :
    timeDerivative (spatialTranslate k h f) z =
      timeDerivative f (spatialShift k h z) := by
  unfold timeDerivative spatialTranslate spatialShift
  rw [fderiv_comp_add_right]

/-- The velocity gradient commutes exactly with spatial translation. -/
@[simp] theorem velocityGradient_spatialTranslate
     :
    velocityGradient (spatialTranslate k h f) z =
      velocityGradient f (spatialShift k h z) := by
  unfold velocityGradient spatialTranslate spatialShift
  rw [fderiv_comp_add_right]

/-- A weak velocity derivative transports to any subdomain whose forward shift lies
in the original domain. -/
theorem HasWeakVelocityPartialDerivOn.spatialTranslate_of_mapsTo
     {U V : Set (TimeVelocity d)} {i : Fin d}
    {u dui : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    HasWeakVelocityPartialDerivOn V i
      (spatialTranslate k h u) (spatialTranslate k h dui) := by
  intro φ hφSmooth hφCompact hφSupport
  have himageVU : spatialShift k h '' V ⊆ U := by
    aesop
  have hbackSmooth : ContDiff ℝ _ (spatialTranslate k (-h) φ) :=
    ContDiff.spatialTranslate hφSmooth
  have hbackCompact : HasCompactSupport (spatialTranslate k (-h) φ) :=
    HasCompactSupport.spatialTranslate hφCompact
  have hbackSupport : tsupport (spatialTranslate k (-h) φ) ⊆ spatialShift k h '' V := by
    intro z hz
    rw [mem_tsupport_spatialTranslate_iff] at hz
    aesop
  have hweak := hu.restrict himageVU _
    hbackSmooth hbackCompact hbackSupport
  have hmeasure := spatialShift_measurePreserving k h
  have hembed := spatialShift_measurableEmbedding k h
  calc
    ∫ z in V, spatialTranslate k h u z * velocityGradient φ z i ∂volume =
        ∫ z in spatialShift k h '' V,
          u z * velocityGradient _ z i ∂volume := by
      rw [hmeasure.setIntegral_image_emb hembed]
      apply integral_congr_ae
      filter_upwards with z
      aesop
    _ = -∫ z in spatialShift k h '' V,
          dui z * spatialTranslate k _ φ z ∂volume := hweak
    _ = -∫ z in V, spatialTranslate k h dui z * φ z ∂volume := by
      rw [hmeasure.setIntegral_image_emb hembed]
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      aesop

end HypoellipticAleksandrov.Parabolic
