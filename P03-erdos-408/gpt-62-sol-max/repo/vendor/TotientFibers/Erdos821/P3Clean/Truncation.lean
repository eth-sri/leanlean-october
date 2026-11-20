module

public import Erdos821.P3Clean.Structure

/-! The cutoff leaves a finite memory state space, without choosing ordered representatives. -/

@[expose] public section

noncomputable section

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

instance finite_bounded_multiset {α : Type*} [Finite α] (B : ℕ) :
    Finite {z : Multiset α // z.card ≤ B} := by
  let encode (z : {z : Multiset α // z.card ≤ B}) :
      (j : Fin (B + 1)) × Sym α j.val :=
    ⟨⟨z.val.card, Nat.lt_succ_of_le z.property⟩, ⟨z.val, rfl⟩⟩
  apply Finite.of_injective encode
  intro z w h
  apply Subtype.ext
  exact congrArg (fun c : (j : Fin (B + 1)) × Sym α j.val => c.2.val) h



end Erdos821.P3Clean
