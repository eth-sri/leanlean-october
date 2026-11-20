module

public import NearlyMinimax.ProductBoundedDifferences


@[expose] public section

/-!
# Genuine independent label blocks for the actual finite history marks
-/

noncomputable section
open MeasureTheory Set
namespace NearlyMinimax

variable {J I E : Type*} [Fintype J] [Fintype I] [MeasurableSpace E]

/-- Reconstruct each actual occurrence mark from the independent vector for its true label.
Unused coordinates give a harmless redundant realization of independent finite label blocks. -/
def labelBlockReconstruct (labels : I → J) (blocks : J → I → E) : I → E :=
  fun i => blocks (labels i) i

omit [Fintype J] [Fintype I] in
/-- The actual label-block reconstruction is jointly measurable. -/
theorem labelBlockReconstruct_measurable (labels : I → J) :
    Measurable (labelBlockReconstruct labels (E := E)) := by
  apply measurable_pi_iff.2
  intro i
  exact (measurable_pi_apply i).comp (by fun_prop)

/-- Redundant independent label vectors reproduce exactly the original independent occurrence marks. -/
theorem labelBlockReconstruct_preserving (labels : I → J) (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (labelBlockReconstruct labels)
      (Measure.pi (fun _ => Measure.pi (fun _ => π)))
      (Measure.pi (fun _ => π)) := by
  classical
  refine ⟨labelBlockReconstruct_measurable labels, ?_⟩
  apply (Measure.pi_eq ?_).symm
  intro s hs
  rw [Measure.map_apply (labelBlockReconstruct_measurable labels) (MeasurableSet.univ_pi hs)]
  have hp : labelBlockReconstruct labels ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun j => Set.univ.pi (fun i => if labels i = j then s i else Set.univ)) := by
    ext blocks
    aesop
  rw [hp]
  simp_rw [Measure.pi_pi]
  have he : ∀ j i, π (if labels i = j then s i else Set.univ) =
      if labels i = j then π (s i) else 1 := by
    intro j i
    split_ifs <;> simp
  simp_rw [he]
  rw [Finset.prod_comm]
  simp

omit [Fintype J] [Fintype I] [MeasurableSpace E] in
/-- Replacing a label block leaves every occurrence of another label exactly unchanged. -/
theorem labelBlockReconstruct_update_other [DecidableEq J] (labels : I → J) (blocks : J → I → E)
    (j : J) (new : I → E) (i : I) (hi : labels i ≠ j) :
    labelBlockReconstruct labels (Function.update blocks j new) i = labelBlockReconstruct labels blocks i := by
  simp_all [labelBlockReconstruct]

end NearlyMinimax
