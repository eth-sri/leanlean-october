/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.FK.Graph

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*}

section
variable (G : SimpleGraph V) (A : Configuration G) (L : Finset V)
/-- Boolean indicator of actual open connectivity to the seed set. This deliberately
uses `ActualConnected`, so boundary identifications play no role. -/
noncomputable def actualReachabilityLabel (v : V) : Bool := by
  classical
  exact decide (∃ u, u ∈ L ∧ ActualConnected G A u v)

theorem actualReachabilityLabel_eq_true_iff (v : V) :
    actualReachabilityLabel G A L v = true ↔
      ∃ u, u ∈ L ∧ ActualConnected G A u v := by
  simp [actualReachabilityLabel]

theorem actualReachabilityLabel_eq_true_of_mem {v : V} (hv : v ∈ L) :
    actualReachabilityLabel G A L v = true := by
  apply (actualReachabilityLabel_eq_true_iff G A L v).2
  tauto

theorem actualReachabilityLabel_eq_of_actualConnected {x y : V}
    (hxy : ActualConnected G A x y) :
    actualReachabilityLabel G A L x = actualReachabilityLabel G A L y := by
  have hiff : (∃ u, u ∈ L ∧ ActualConnected G A u x) ↔
      (∃ u, u ∈ L ∧ ActualConnected G A u y) := by
    constructor
    · rintro ⟨u, hu, hux⟩
      exact ⟨u, hu, hux.trans hxy⟩
    · rintro ⟨u, hu, huy⟩
      exact ⟨u, hu, huy.trans hxy.symm⟩
  apply Bool.eq_iff_iff.mpr
  rwa [actualReachabilityLabel_eq_true_iff, actualReachabilityLabel_eq_true_iff]
end

section
variable (G : SimpleGraph V) (A : Configuration G)
theorem actualReachabilityLabel_eq_false_of_no_seed_path (L R : Finset V)
    (hno : ∀ u, u ∈ L → ∀ v, v ∈ R → ¬ ActualConnected G A u v)
    {v : V} (hv : v ∈ R) :
    actualReachabilityLabel G A L v = false := by
  grind [actualReachabilityLabel, ActualConnected, False.elim]

theorem actualEdge_mem_configuration_implies_labels_eq (L : Finset V) {u v : V} (hG : s(u, v) ∈ G.edgeSet)
    (hA : (⟨s(u, v), hG⟩ : G.edgeSet) ∈ A) :
    actualReachabilityLabel G A L u = actualReachabilityLabel G A L v := by
  apply actualReachabilityLabel_eq_of_actualConnected G A L
  apply actualConnected_of_adj
  rw [openGraph_adj]
  exact ⟨⟨s(u, v), hG⟩, hA, rfl⟩
end

end PottsDiscontinuity.FK
