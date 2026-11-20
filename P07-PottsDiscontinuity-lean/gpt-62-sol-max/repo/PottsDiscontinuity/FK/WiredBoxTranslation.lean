/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The finite laws use wired vertex boundaries and open exterior extension. -/
module

public import PottsDiscontinuity.FK.WiredBoxLaw
public import PottsDiscontinuity.FK.BoxTranslation
public import PottsDiscontinuity.FK.BoundaryPartitionLaw

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory
noncomputable section

section

variable (e : squareLattice ≃g squareLattice)
  (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
  (c : LatticeVertex) (r : ℕ)
include hbox

private theorem mem_vertexBoundary_latticeBox_iso_iff (v : LatticeVertex) :
    e v ∈ vertexBoundary (latticeBox (e c) r) ↔ v ∈ vertexBoundary (latticeBox c r) := by
  have hex := e.surjective.exists (p := fun w => squareLattice.Adj (e v) w ∧
    w ∉ latticeBox (e c) r)
  exact and_congr (hbox c v r) (hex.trans (exists_congr fun w =>
    and_congr e.map_rel_iff' (not_congr (hbox c w r))))

private theorem boundaryConditionIso_wired_box_partition :
    (boundaryConditionIso (boxGraphIsoOfLatticeIso e hbox c r)
      (BoundaryCondition.wired (boxVertexBoundary c r))).partition =
      (BoundaryCondition.wired (boxVertexBoundary (e c) r)).partition := by
  let I := boxGraphIsoOfLatticeIso e hbox c r
  apply Setoid.ext
  intro u v
  obtain ⟨u, rfl⟩ := I.surjective u
  obtain ⟨v, rfl⟩ := I.surjective v
  change (I.symm (I u) = I.symm (I v) ∨
    I.symm (I u) ∈ boxVertexBoundary c r ∧ I.symm (I v) ∈ boxVertexBoundary c r) ↔
    (I u = I v ∨ e u.1 ∈ vertexBoundary (latticeBox (e c) r) ∧
      e v.1 ∈ vertexBoundary (latticeBox (e c) r))
  rw [I.symm_apply_apply, I.symm_apply_apply, I.injective.eq_iff,
    mem_vertexBoundary_latticeBox_iso_iff e hbox, mem_vertexBoundary_latticeBox_iso_iff e hbox]
  rfl

theorem wiredBoxProbabilityMeasure_iso_map (θ : Parameters) :
    ProbabilityMeasure.map (wiredBoxProbabilityMeasure θ c r) (latticeConfigurationIsoHomeomorph e) =
      wiredBoxProbabilityMeasure θ (e c) r :=
  probabilityMeasureMap_eq_of_PMF (latticeConfigurationIsoHomeomorph e).continuous.measurable
    (boxLaw_iso_map_of_commute e hbox c r θ _ _ (boundaryConditionIso_wired_box_partition e hbox c r) _ _
      (boxExtension_iso_commute e hbox c r wiredBoxConfiguration true
        wiredBoxConfiguration_at wiredBoxConfiguration_outside))

end
end
end PottsDiscontinuity.FK
