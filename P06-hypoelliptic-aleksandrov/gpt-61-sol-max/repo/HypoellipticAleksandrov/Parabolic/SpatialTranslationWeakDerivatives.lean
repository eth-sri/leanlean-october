module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Bound
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Spatial translation of raw weak derivatives

This module transports the representative-level weak time and velocity
derivative identities through native spatial translations.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

variable (k : Fin d) (h : ℝ)

variable (z : TimeVelocity d)

private theorem spatialShift_neg_comp_apply
       :
    spatialShift k (-h) (spatialShift k h z) = z := by
  bound

private theorem spatialShift_comp_neg_apply
       :
    spatialShift k h (spatialShift k (-h) z) = z := by
  bound

private theorem spatialShift_measurableEmbedding
      :
    MeasurableEmbedding (spatialShift k h) := (id (Homeomorph.measurableEmbedding (Homeomorph.addRight (0, h • PDE.basisVec k))))

/-- A native coordinate spatial shift preserves product Lebesgue volume. -/
theorem spatialShift_measurePreserving
      :
    MeasurePreserving (spatialShift k h)
      (volume )
       := (id (measurePreserving_add_right volume (0, h • PDE.basisVec k)))

variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d)

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
     {U V : HypoellipticAleksandrov.Parabolic.Region d} {i : Fin d}
    {u dui : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    HasWeakVelocityPartialDerivOn V i
      (spatialTranslate k h u) (spatialTranslate k h dui) := by
  intro φ hφSmooth hφCompact hφSupport




  have hweak := hu.restrict (show spatialShift k h '' V ⊆ U by
      rintro z ⟨y, hy, rfl⟩
      exact hshift hy) _
    (ContDiff.spatialTranslate hφSmooth) (HasCompactSupport.spatialTranslate hφCompact) (show tsupport (spatialTranslate k (-h) φ) ⊆ spatialShift k h '' V by
        intro z hz
        rw [mem_tsupport_spatialTranslate_iff] at hz
        refine ⟨spatialShift k (-h) z, hφSupport hz, ?_⟩
        exact spatialShift_comp_neg_apply k h z)
  have hmeasure := spatialShift_measurePreserving k h
  have hembed := spatialShift_measurableEmbedding k h
  calc
    ∫ z in V, spatialTranslate k h u z * velocityGradient φ z i =
        ∫ z in spatialShift k h '' V,
          u z * velocityGradient (spatialTranslate k (-h) φ) z i := by
      rw [hmeasure.setIntegral_image_emb hembed]
      apply integral_congr_ae
      filter_upwards with z
      simp only [spatialTranslate_apply, velocityGradient_spatialTranslate]
      rw [spatialShift_neg_comp_apply]
    _ = -∫ z in spatialShift k h '' V,
          dui z * spatialTranslate k (-h) φ z := hweak
    _ = -∫ z in V, spatialTranslate k h dui z * φ z := by
      rw [hmeasure.setIntegral_image_emb hembed]
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      simp only [spatialTranslate_apply]
      rw [spatialShift_neg_comp_apply]

end HypoellipticAleksandrov.Parabolic
