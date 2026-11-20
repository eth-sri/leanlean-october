module

public import Mathlib


@[expose] public section

/-! The finite occupancy argument behind the hyperplane field moment bound. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

variable {I J : Type*} [DecidableEq I] [DecidableEq J] {s : Finset J} {p : J → I} (hs : 4 ≤ s.card)
    (h : ∀ i, Even ((s.filter (fun j => p j = i)).card))
include h

theorem even_cell_has_partner
    {a : J} (ha : a ∈ s) : ∃ b ∈ s, b ≠ a ∧ p b = p a := by
  let f := s.filter (fun j => p j = p a)
  have haf : a ∈ f := by simp [f, ha]
  have hpos  := Finset.card_pos.mpr ⟨a, haf⟩
  have he : Even f.card := h (p a)
  obtain ⟨k, hk⟩ := he
  have hne : 0 < (f.erase a).card := by
    rw [Finset.card_erase_of_mem haf]
    omega
  grind

theorem even_cells_erase_pair
    {a b : J} (ha : a ∈ s) (hb : b ∈ s) (hab : b ≠ a) (hp : p b = p a) :
    ∀ i, Even (((s.erase a).erase b).filter (fun j => p j = i)).card := by
  intro i
  rw [Finset.filter_erase, Finset.filter_erase]
  by_cases hpa : p a = i
  · have hai : a ∈ s.filter (fun j => p j = i) := by simp [ha, hpa]
    have hbi : b ∈ s.filter (fun j => p j = i) := by simp_all
    rw [Finset.card_erase_of_mem (by simp [hab, hbi]), Finset.card_erase_of_mem hai]
    obtain ⟨k, hk⟩ := h i
    exact ⟨k - 1, by omega⟩
  · aesop

include hs in
theorem even_cells_two_disjoint_pairs :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ e ∈ s,
      b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧
        p b = p a ∧ p e = p c := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  obtain ⟨b, hb, hab, hpab⟩ := even_cell_has_partner h ha
  let t := (s.erase a).erase b
  have hbe : b ∈ s.erase a := by simp [hab, hb]
  have ht : 2 ≤ t.card := by
    simp [t, Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  obtain ⟨e, he, hec, hpec⟩ := even_cell_has_partner (even_cells_erase_pair h ha hb hab hpab) hc
  have hct := Finset.mem_erase.mp hc
  grind

end NearlyMinimax
