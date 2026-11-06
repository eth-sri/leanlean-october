module

public import Erdos821.P4Probe.Bridge

@[expose] public section

set_option autoImplicit false
open scoped Classical

namespace Erdos821.P4Probe

noncomputable section

lemma balanced_blocks {α : Type*} [Fintype α] [DecidableEq α] :
    ∃ block : α → Bool,
      (Finset.univ.filter (fun g => block g = false)).card = Fintype.card α / 2 ∧
      (Finset.univ.filter (fun g => block g = true)).card =
        Fintype.card α - Fintype.card α / 2 := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset α))
    (show Fintype.card α / 2 ≤ Finset.univ.card by grind)
  let block : α → Bool := fun g => if g ∈ s then false else true
  have hfalse : Finset.univ.filter (fun g => block g = false) = s := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, block]
    by_cases hg : g ∈ s <;> simp
  have htrue : Finset.univ.filter (fun g => block g = true) = Finset.univ \ s := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, block]
    by_cases hg : g ∈ s <;> simp
  exact ⟨block, hfalse ▸ hcard, by grind⟩

lemma balanced_block_lower {α : Type*} [Fintype α] [DecidableEq α]
    (hn : 3 ≤ Fintype.card α) :
    ∃ block : α → Bool, ∀ side : Bool,
      (Fintype.card α : ℝ) / 3 ≤
        ((Finset.univ.filter (fun g => block g = side)).card : ℝ) := by
  obtain ⟨block, hfalse, htrue⟩ := balanced_blocks (α := α)
  refine ⟨block, ?_⟩
  intro side
  cases side
  · rw [hfalse]
    have h : Fintype.card α ≤ 3 * (Fintype.card α / 2) := by omega
    have h' : (Fintype.card α : ℝ) ≤ 3 * (Fintype.card α / 2 : ℕ) := by exact_mod_cast h
    linarith
  · rw [htrue]
    have h : Fintype.card α ≤ 3 * (Fintype.card α - Fintype.card α / 2) := by omega
    have h' : (Fintype.card α : ℝ) ≤ 3 * (Fintype.card α - Fintype.card α / 2 : ℕ) := by exact_mod_cast h
    linarith

end
end Erdos821.P4Probe
