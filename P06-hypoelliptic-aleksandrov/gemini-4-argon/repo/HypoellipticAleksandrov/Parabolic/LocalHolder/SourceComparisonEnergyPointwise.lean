module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyInterior
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonRepresentative
import Mathlib.MeasureTheory.Group.Measure

/-! # Pointwise source bounds for classical energy representatives

The sharp affine variational envelope transfers through time reflection and the product
representative. Interior continuity promotes the resulting almost-everywhere bound.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set Dirichlet
open scoped ENNReal Topology MatrixOrder Matrix.Norms.Elementwise

/- Original-time reflection preserves the literal restricted reverse-time volume. -/
theorem sourceTimeReflection_measurePreserving (a T : ℝ) :
    MeasurePreserving (fun t : ℝ => T - t)
      (volume.restrict (Ioo a T)) (reverseTimeVolume (T - a)) := by
  have hm : MeasurePreserving (fun t : ℝ => T - t) (volume : Measure ℝ) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure ℝ) T).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpre : (fun t : ℝ => T - t) ⁻¹' Ioo 0 (T - a) = Ioo a T := by
    rw [preimage_const_sub_Ioo]
    congr 1 <;> ring
  rw [reverseTimeVolume, reverseTimeOpenInterval, ← hpre]
  exact hm.restrict_preimage isOpen_Ioo.measurableSet

/- A continuous classical representative of the zero-initial energy correction has
the sharp source-amplitude time bound at every interior point. -/
end HypoellipticAleksandrov.Parabolic.LocalHolder
