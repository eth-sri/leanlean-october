module

public import Erdos821.S2.HistoryOrders
public import Erdos821.S2.SpanBirthTask
public import Erdos821.S2.SpanUniqueness

/-! Finite configurations parameterize the full ordered lifespan construction. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace ResiduePath

theorem ghostBatchLabels_injective {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)
     S   i   g  :
    Function.Injective (Q.ghostBatchLabels S i g) := by
  apply List.nodup_ofFn.mp
  rw [Q.ghostBatchLabels_enumeration]
  exact Finset.nodup_toList _

end ResiduePath

abbrev SpanConfiguration (A : Model F P J m) (n ) :=
  (Q : {Q : ResiduePath A n // Q.Valid}) ×
    (S : {S : LifespanAssignment P n // Q.val.lifespanValid S}) ×
      (y : {y : P.SmallResidues // Q.val.SmallCompatible y}) ×
        (Q.val.reconstructedHistory S.val S.property y.val).BatchOrders

instance (A : Model F P J m) (n : ℕ) : Fintype (SpanConfiguration A n) := inferInstance

namespace SpanConfiguration

variable {A : Model F P J m} {n : ℕ} (c : SpanConfiguration A n)

def history  :=
  (c.1.val.reconstructedHistory c.2.1.val c.2.1.property c.2.2.1.val).reorderBatches c.2.2.2

section
variable (hMem : SpanEdgeMemoryTask) (hBirth : SpanBirthTask) (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)


include hMem hk in
theorem history_valid  
      :
    c.history.Valid := by
  apply (MemoryHistory.reorderBatches_valid _ _).mpr
  exact c.1.val.reconstructedHistory_valid hMem c.2.1.val c.1.property c.2.1.property
    hk c.2.2.1.val c.2.2.1.property

include hBirth hk in
theorem history_distinct  
      :
    c.history.DistinctBirths := by
  apply (MemoryHistory.reorderBatches_distinct _ _).mpr
  exact hBirth F P J m n A c.1.val c.2.1.val c.1.property c.2.1.property hk c.2.2.1.val

end

theorem history_projection : c.history.toResiduePath = c.1.val := by
  unfold history
  rw [MemoryHistory.reorderBatches_projection, ResiduePath.reconstructedHistory_projection]

theorem history_injective : Function.Injective (history (A := A) (n := n)) := by
  intro c d he
  have hq : c.1 = d.1 := Subtype.ext (by
    rw [← c.history_projection, ← d.history_projection, he])
  rcases c with ⟨q, s, y, sigma⟩
  rcases d with ⟨q', s', y', tau⟩
  dsimp only at hq
  cases hq
  have hs : s = s' := Subtype.ext (q.val.lifespan_eq_of_memories s.val s'.val
    s.property s'.property
    (fun i g => congrArg (fun H : MemoryHistory A n => (H.before i).2.2 g) he)
    (fun i g => congrArg (fun H : MemoryHistory A n => (H.after i).2.2 g) he))
  cases hs
  have hy : y = y' := Subtype.ext (by
    have hv := congrArg (fun H : MemoryHistory A n => (H.before 0).1) he
    change translateSmallResidues (q.val.offset 0) y.val =
      translateSmallResidues (q.val.offset 0) y'.val at hv
    simpa only [ResiduePath.offset_zero, translateSmallResidues_zero] using hv)
  cases hy
  have ho : sigma = tau :=
    MemoryHistory.reorderBatches_injective _
      (q.val.ghostBatchLabels_injective s.val) he
  cases ho
  rfl

end SpanConfiguration
end Erdos821.S2Core
