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

 public section

open scoped Pointwise

namespace PDE

open MeasureTheory

variable {d : ℕ}

theorem measurePreserving_addRight_restrict_translateSet
    (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x  => x + z)
      (volumeOn U) (volumeOn (translateSet z U)) := by
  let hμ :
      MeasurePreserving (fun x  => x + z)
        (volume )  :=
    measurePreserving_add_right
      _ z
  simpa only [volumeOn, image_addRight_eq_translateSet (z := z) U] using
    MeasurePreserving.restrict_image_emb hμ (Homeomorph.addRight z).measurableEmbedding U

theorem setIntegral_comp_addRight_translateSet
     {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ y in U, f (y + z) =
      ∫ x in translateSet z U, f x := by
  simpa using
    (measurePreserving_addRight_restrict_translateSet z U).integral_comp
      (Homeomorph.addRight z).measurableEmbedding f

theorem volume_translateSet_eq
    (z : Vec d) (U : Set (Vec d)) :
    volume (translateSet z U) = volume U := by
  have h :=
    MeasurePreserving.measure_preimage_emb
      (measurePreserving_add_right
        (volume : Measure (Vec d)) z)
      (Homeomorph.addRight z).measurableEmbedding
      (translateSet z U)
  simpa [preimage_addRight_translateSet_eq] using h.symm

theorem volume_smul_set_of_nonneg
    {r : ℝ} (hr : 0 ≤ r) (U : Set (Vec d)) :
    volume (r • U) =
      ENNReal.ofReal (r ^ d) * volume U := by
  simpa [Vec] using
    (Measure.addHaar_smul_of_nonneg
      (μ := volume) (E := Vec d) hr U)

theorem setIntegral_comp_smul_of_pos
     {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : 0 < r) (U : Set (Vec d))
    (f : Vec d → E) :
    ∫ x in U, f (r • x) =
      (r ^ d)⁻¹ • ∫ y in r • U, f y := by
  simpa [Vec] using
    (Measure.setIntegral_comp_smul_of_pos
      (μ := volume) (f := f) (s := U) hr)

end PDE
