module

public import PDEFoundation.Geometry.Affine
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Translation and dilation of volume

Exact change-of-variable statements for native vectors. These are the
measure-level foundation of all later scale-invariant norms.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

open MeasureTheory


theorem setIntegral_comp_addRight_translateSet
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ y in U, f (y + z) ∂volume =
      ∫ x in translateSet z U, f x ∂volume  := by
  have measurePreserving_addRight_restrict_translateSet :
      MeasurePreserving (fun x => x + z)
      (volumeOn U) (volumeOn (translateSet z U)) := by
    let hμ :
        MeasurePreserving (fun x => x + z)
          (volume : Measure (Vec d)) volume :=
      measurePreserving_add_right
        (volume : Measure (Vec d)) z
    simpa [volumeOn, preimage_addNeg_eq_translateSet (z := z) U,
      image_addRight_eq_translateSet (z := z) U, sub_eq_add_neg] using
      MeasurePreserving.restrict_image_emb hμ
        (Homeomorph.addRight z).measurableEmbedding U
  simpa using
    (measurePreserving_addRight_restrict_translateSet).integral_comp
      (Homeomorph.addRight z).measurableEmbedding f

theorem volume_translateSet_eq {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) :
    volume (translateSet z U) = volume U := by
  simpa [preimage_addRight_translateSet_eq] using (MeasurePreserving.measure_preimage_emb (measurePreserving_add_right (volume : Measure (Vec d)) z) (Homeomorph.addRight z).measurableEmbedding (translateSet z U)).symm

theorem volume_smul_set_of_nonneg {d : ℕ}
    {r : ℝ} (hr : 0 ≤ r) (U : Set (Vec d)) :
    volume (r • U) =
      ENNReal.ofReal (r ^ d) * volume U := by
  simpa [Vec] using
    (Measure.addHaar_smul_of_nonneg
      (μ := volume) hr U)


end PDE
