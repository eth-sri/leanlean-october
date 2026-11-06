module

public import Erdos821.S2.MemoryEdge

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge


lemma fresh_sum_eq {α : Type*} [Fintype α] [DecidableEq α] (mu : α → ℝ) (k : ℕ) :
    ∑ p : Fin k → α, ∏ i, mu (p i) = (∑ a, mu a) ^ k := by
  classical
  have h1 := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset α))
    (fun _ : Fin k => fun a : α => mu a)
  simp_all

end Erdos821.P3Edge
