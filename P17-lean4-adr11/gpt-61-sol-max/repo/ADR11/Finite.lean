module
public import Mathlib
@[expose] public section
/-- The trace of a cluster on a chosen subset. -/
abbrev Finset.trace {α : Type*} [DecidableEq α] (A S : Finset α) : Finset S :=
  A.subtype (· ∈ S)

namespace ADR11

/-- A finite family of clusters. -/
abbrev Family (α : Type*) := Finset (Finset α)

/-- The clusters below `A` whose trace agrees with that of `A`. -/
abbrev branchChain {α : Type*} [DecidableEq α] (H : Family α) (S A : Finset α) : Family α :=
  H.filter fun B => B ⊆ A ∧ B.trace S = A.trace S

/-- The cluster pulled back along a sampling map. -/
abbrev clusterPreimage {α β : Type*} [Fintype α] [DecidableEq β]
    (s : α → β) (A : Finset β) : Finset α := Finset.univ.filter fun l => s l ∈ A

theorem clusterPreimage_mono {α β : Type*} [Fintype α] [DecidableEq β]
    (s : α → β) {A B : Finset β} (h : A ⊆ B) : clusterPreimage s A ⊆ clusterPreimage s B := by
  intro l hl
  simpa using h (by simpa using hl)

open Finset in
theorem sup_univ_equiv {ι κ α : Type*} [Fintype ι] [Fintype κ] [SemilatticeSup α]
    [OrderBot α] (e : ι ≃ κ) (f : κ → α) :
    univ.sup (fun i => f (e i)) = univ.sup f := by
  conv_rhs => rw [← Finset.map_univ_equiv e, Finset.sup_map]
  rfl

end ADR11
