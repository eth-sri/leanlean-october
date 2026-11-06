module

public import Mathlib.MeasureTheory.Measure.Real

public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section

/-- Equality of two finite-valued spins is the disjoint sum over their common colour. -/
theorem measureReal_same_colour_sum {X C : Type*} [MeasurableSpace X] [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype C] (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → C) (hf : Measurable f) (hg : Measurable g) :
    μ.real {x | f x = g x} = ∑ c : C, μ.real {x | f x = c ∧ g x = c} := by
  have he : {x | f x = g x} = ⋃ c ∈ (Finset.univ : Finset C), {x | f x = c ∧ g x = c} := by
    aesop
  have hd : (↑(Finset.univ : Finset C) : Set C).PairwiseDisjoint
      (fun c => {x | f x = c ∧ g x = c}) := by
    intro c _ d _ hcd
    grind
  rw [he]
  exact measureReal_biUnion_finset hd (fun c _ =>
    (hf (measurableSet_singleton c)).inter (hg (measurableSet_singleton c)))

end
end PottsDiscontinuity.Potts
