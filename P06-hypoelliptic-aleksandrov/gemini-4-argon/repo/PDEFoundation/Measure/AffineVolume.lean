module

public import PDEFoundation.Geometry.Affine
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Set.Basic
import PDEFoundation.Ambient.Basic

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
      ∫ x in translateSet z U, f x ∂volume := by
  have _h_inl_11 : MeasurePreserving (fun x : Vec d => x + z) (volumeOn U) (volumeOn (translateSet z U)) := by
    let hμ :=
      measurePreserving_add_right
        (volume : Measure (Vec d)) z
    have _h_xinl_1 : (fun x : Vec d => x + z) '' U = translateSet z U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    simpa [volumeOn, preimage_addNeg_eq_translateSet (z := z) U,
      _h_xinl_1, sub_eq_add_neg] using
      MeasurePreserving.restrict_image_emb hμ
        (Homeomorph.addRight z).measurableEmbedding U
  simpa using
    _h_inl_11.integral_comp
      (Homeomorph.addRight z).measurableEmbedding f

theorem volume_translateSet_eq {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) :
    volume (translateSet z U) = volume U := by
  have _h_xinl_0 (z : Vec d) (U) : (fun x : Vec d => x + z) ⁻¹' translateSet z U = U := by
    ext x
    simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg, add_assoc]
  simpa [_h_xinl_0] using (MeasurePreserving.measure_preimage_emb (measurePreserving_add_right (volume : Measure (Vec d)) z) (Homeomorph.addRight z).measurableEmbedding (translateSet z U)).symm

theorem volume_smul_set_of_nonneg {d : ℕ}
    {r : ℝ} (hr : 0 ≤ r) (U : Set (Vec d)) :
    volume (r • U) =
      ENNReal.ofReal (r ^ d) * volume U := by
  simpa [Vec] using
    (Measure.addHaar_smul_of_nonneg
      (μ := volume) (E := Vec d) hr U)

theorem setIntegral_comp_smul_of_pos
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : 0 < r) (U : Set (Vec d))
    (f : Vec d → E) :
    ∫ x in U, f (r • x) ∂volume =
      (r ^ d)⁻¹ • ∫ y in r • U, f y ∂volume := by
  simpa [Vec] using
    (Measure.setIntegral_comp_smul_of_pos
      (μ := volume) (f := f) (s := U) hr)

end PDE
