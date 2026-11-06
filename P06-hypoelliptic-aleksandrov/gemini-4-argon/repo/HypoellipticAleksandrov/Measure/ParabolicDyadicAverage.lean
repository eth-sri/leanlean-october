module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicFiltration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Finite parabolic dyadic averages

This module records the explicit finite-cell averaging function at a complete
parabolic dyadic checkpoint.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/- The ordinary normalized integral of `f` over one addressed dyadic cell. -/
def parabolicDyadicCellAverage (d n : ℕ)
    (f : ParabolicDyadicReferenceSpace d → ℝ)
    (index : ParabolicDyadicIndex d n) : ℝ :=
  ((parabolicDyadicReferenceMeasure d).real
      (parabolicDyadicRestrictedCell index))⁻¹ *
    ∫ x in parabolicDyadicRestrictedCell index,
      f x ∂parabolicDyadicReferenceMeasure d

/- The finite indicator sum of the addressed-cell averages at generation
`n`. -/
def parabolicDyadicCheckpointAverage (d n : ℕ)
    (f : ParabolicDyadicReferenceSpace d → ℝ) :
    ParabolicDyadicReferenceSpace d → ℝ :=
  fun z => ∑ index : ParabolicDyadicIndex d n,
    (parabolicDyadicRestrictedCell index).indicator
      (fun _ => parabolicDyadicCellAverage d n f index) z

/- Restricting the reference-subtype measure to an addressed cell recovers
the ambient volume of that half-open cell. -/
theorem parabolicDyadicReferenceMeasure_restrictedCell {d n }
    (index : ParabolicDyadicIndex d n) :
    parabolicDyadicReferenceMeasure d (parabolicDyadicRestrictedCell index) =
      volume (parabolicDyadicHalfOpenCell index) := by
  rw [parabolicDyadicReferenceMeasure, comap_subtype_coe_apply
    (measurableSet_parabolicDyadicReferenceCell d)]
  change volume (Subtype.val '' (Subtype.val ⁻¹' parabolicDyadicHalfOpenCell index)) = _
  rw [Subtype.image_preimage_coe, inter_comm,
    inter_eq_left.mpr (parabolicDyadicHalfOpenCell_subset_reference index)]

/- The real reference-subtype measure of a generation-`n` addressed cell is
the exact parabolic dyadic volume. -/
theorem parabolicDyadicReferenceMeasure_restrictedCell_real_pos {d n }
    (index : ParabolicDyadicIndex d n) :
    0 < (parabolicDyadicReferenceMeasure d).real
      (parabolicDyadicRestrictedCell index) := by
  have _h_inl_12 (index : ParabolicDyadicIndex d n) : (parabolicDyadicReferenceMeasure d (parabolicDyadicRestrictedCell index)).toReal = (2 : ℝ) ^ d / (2 : ℝ) ^ ((d + 2) * n) := by
    rw [parabolicDyadicReferenceMeasure_restrictedCell]
    exact volume_parabolicDyadicHalfOpenCell_toReal index
  rw [Measure.real, _h_inl_12]
  exact div_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)

/- On an addressed generation-`n` cell, the checkpoint average is the
corresponding single-cell average. -/
theorem parabolicDyadicCheckpointAverage_eq_cellAverage {d n }
    (f : ParabolicDyadicReferenceSpace d → ℝ)
    (index z)
    (hz : z ∈ parabolicDyadicRestrictedCell index) :
    parabolicDyadicCheckpointAverage d n f z =
      parabolicDyadicCellAverage d n f index := by
  classical
  unfold parabolicDyadicCheckpointAverage
  rw [Finset.sum_eq_single index]
  · simp only [Set.indicator_of_mem hz]
  · intro other _ hne
    have hnot : z ∉ parabolicDyadicRestrictedCell other := by
      intro hother
      exact (Set.disjoint_left.mp
        (parabolicDyadicHalfOpenCell_disjoint_of_ne hne) hother hz).elim
    simp only [Set.indicator_of_notMem hnot]
  · simp

/- The finite checkpoint average is strongly measurable for the checkpoint
filtration. -/
theorem integrable_parabolicDyadicCheckpointAverage (d n : ℕ)
    (f : ParabolicDyadicReferenceSpace d → ℝ) :
    Integrable (parabolicDyadicCheckpointAverage d n f)
      (parabolicDyadicReferenceMeasure d) := by
  classical
  letI : IsFiniteMeasure (parabolicDyadicReferenceMeasure d) :=
    ⟨lt_top_iff_ne_top.mpr (parabolicDyadicReferenceMeasure_univ_ne_top d)⟩
  unfold parabolicDyadicCheckpointAverage
  apply integrable_finset_sum Finset.univ
  intro index _
  exact IntegrableOn.integrable_indicator integrableOn_const
    (measurableSet_parabolicDyadicRestrictedCell index)

/- The set integral of the checkpoint average over an addressed cell is the
set integral of the original function over that cell. -/
end

end HypoellipticAleksandrov.Parabolic
