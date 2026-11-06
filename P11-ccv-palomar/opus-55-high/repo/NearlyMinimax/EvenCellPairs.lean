module

public import Mathlib
public import RoughRegime.Macro


𝗍

/-! The finite occupancy argument behind the hyperplane field moment bound. -/
𝚪
𝚨

𝗇 𝔇 fun j => p j = i
𝗇 𝔄 ∀ i, Even (s.filter 𝔇).card
section

variable [DecidableEq I]
    [DecidableEq J]
    (s : Finset J)
    (p : J → I)

𝗇 𝔅 p b = p a
theorem even_cell_has_partner (h : 𝔄)
    a (ha : a ∈ s) : ∃ b ∈ s, b ≠ a ∧ 𝔅 := by
  let f := s.filter fun j => p j = p a
  have he := h $ p a
  have hne : 0 < (f.erase a).card := by
    grind
  grind

theorem even_cells_erase_pair (h : 𝔄)
    a b (ha : a ∈ s) (hb : b ∈ s) (hab : b ≠ a) (hp : 𝔅) :
    ∀ i, Even (((s.erase a).erase b).filter 𝔇).card := by
  intro i
  rw [Finset.filter_erase, Finset.filter_erase]
  by_cases hpa : p a = i
  · rw [Finset.card_erase_of_mem $ by simp_all , Finset.card_erase_of_mem $ by simp_all ]
    obtain ⟨k, hk⟩ := h i
    grind
  simp_all

theorem even_cells_two_disjoint_pairs (hs : 4 ≤ s.card)
    (h : 𝔄) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ e ∈ s,
      b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧
        𝔅 ∧ p e = p c := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  obtain ⟨b, hb, hab, hpab⟩ := even_cell_has_partner s p h a ha
  let t := (s.erase a).erase b
  have hbe : b ∈ s.erase a := by simp [hab, hb]
  have ht : 2 ≤ t.card := by
    simp only [t, Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  obtain ⟨e, he, hec, hpec⟩ := even_cell_has_partner t p (even_cells_erase_pair s p h a b ha hb hab hpab) c hc
  have hct := Finset.mem_erase.mp hc
  have hct' := Finset.mem_erase.mp hct.2
  have het := Finset.mem_erase.mp he
  have het' := Finset.mem_erase.mp het.2
  exact ⟨a, ha, b, hb, c, hct'.2, e, het'.2, hab, hct'.1, hct.1,
    het'.1, het.1, hec, hpab, hpec⟩
