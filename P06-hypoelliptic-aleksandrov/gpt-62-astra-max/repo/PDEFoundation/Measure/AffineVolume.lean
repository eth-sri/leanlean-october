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

variable {d : ℕ} (z : Vec d) {r : ℝ} {E : Type*} (hr : 0 ≤ r) (U : Set (Vec d))

theorem volume_translateSet_eq :
    volume (translateSet z U) = volume U := by
  simpa [preimage_addRight_translateSet_eq] using (MeasurePreserving.measure_preimage_emb (measurePreserving_add_right (volume : Measure (Vec d)) z) (Homeomorph.addRight z).measurableEmbedding (translateSet z U)).symm

include hr in
theorem volume_smul_set_of_nonneg :
    volume (r • U) =
      ENNReal.ofReal (r ^ d) * volume U := by
  simpa [Vec] using
    (Measure.addHaar_smul_of_nonneg
      (μ := volume) (E := Vec d) hr U)

end PDE
