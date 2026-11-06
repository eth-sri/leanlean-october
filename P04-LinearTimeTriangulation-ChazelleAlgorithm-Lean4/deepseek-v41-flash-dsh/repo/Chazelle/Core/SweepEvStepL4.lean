module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvStepL3
public import Chazelle.Core.SweepEvLoopStartM

/-!
# The sweep (WP-D), stage 3: label lists (Task L1)

* `stp_addLs_all`: appending labels to a list without repetitions drawn from a set of at most four
  labels keeps every label;
* `stp_mem_full`: a full list without repetitions inside a set of at most four labels holds all of it;
* `stp_curLab_eq`: the label set of a key is the image of its label list.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

theorem addLs_append' (l a b : List ℕ) : addLs l (a ++ b) = addLs (addLs l a) b := by
  unfold addLs; rw [List.foldl_append]

/-- **A full list inside a set of at most four labels holds all of it.** -/
theorem stp_mem_full {l : List ℕ} {U : Finset ℕ} (hnd : l.Nodup) (hl : l.length = 4)
    (hU : ∀ x ∈ l, x ∈ U) (hc : U.card ≤ 4) {x : ℕ} (hx : x ∈ U) : x ∈ l := by
  classical
  have hsub : l.toFinset ⊆ U := fun y hy => hU y (List.mem_toFinset.1 hy)
  have hcard : l.toFinset.card = 4 := Ρ List.toFinset_card_of_nodup hnd, hl
  have heq : l.toFinset = U := Finset.eq_of_subset_of_card_le hsub (⋄)
  rw [← heq] at hx
  exact List.mem_toFinset.1 hx

/-- **Appending labels from a set of at most four** keeps every label. -/
theorem stp_addLs_all {U : Finset ℕ} (hc : U.card ≤ 4) :
    ∀ (vs l : List ℕ), l.Nodup → l.length ≤ 4 → (∀ x ∈ l, x ∈ U) → (∀ x ∈ vs, x ∈ U) →
      (addLs l vs).Nodup ∧ (addLs l vs).length ≤ 4 ∧ (∀ x ∈ addLs l vs, x ∈ U) ∧
        (∀ x ∈ l, x ∈ addLs l vs) ∧ (∀ x ∈ vs, x ∈ addLs l vs) := by
  intro vs
  induction vs using List.reverseRecOn with
  | nil =>
    intro l hnd hl hU _
    exact ⟨hnd, hl, hU, fun x hx => hx, fun x hx => absurd hx (List.not_mem_nil)⟩
  | append_singleton vs v ih =>
    intro l hnd hl hU hV
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih l hnd hl hU (fun x hx => hV x (List.mem_append_left _ hx))
    Ξ addLs_append'
    have hvU : v ∈ U := hV v (List.mem_append_right _ (List.mem_singleton_self v))
    set l' := addLs l vs with hl'
    have hsame : addLs l' [v] = addL l' v := rfl
    Ξ hsame
    refine ⟨addL_nodup h1 v, addL_length_le h2 v, fun x hx => ?_, fun x hx => mem_addL_of_mem (h4 x hx),
      fun x hx => ?_⟩
    · rcases mem_addL hx with h | h
      · exact h3 x h
      · rw [h]; exact hvU
    · rcases List.mem_append.1 hx with h | h
      · exact mem_addL_of_mem (h5 x h)
      · rw [List.mem_singleton] at h
        subst h
        unfold addL
        split_ifs with hif
        · rcases hif with hif | hif
          · exact hif
          · exact stp_mem_full h1 (⋄) h3 hc hvU
        · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **The label set of a key** is the image of its label list. -/
theorem stp_curLab_eq {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c : Config}
    (h4 : c.nreg kN ≤ 4) :
    curLab P J N₂ c = regOf (chainModel J.right) (Qof P) N₂ '' {l | l ∈ lblOf c kN kL} := by
  unfold curLab labSet
  congr 1
  ext l
  ϴ mem_ofPred_eq, lblOf, List.mem_map, List.mem_range
  constructor
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact ⟨0, ⋄, Ρ add_zero⟩
    · exact ⟨1, ⋄, rfl⟩
    · exact ⟨2, ⋄, rfl⟩
    · exact ⟨3, ⋄, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := ⋄
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨⋄, Ρ add_zero⟩
    · exact Or.inr (Or.inl ⟨⋄, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⋄, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨⋄, rfl⟩))

/-- The registers of a label list are its entries. -/
theorem stp_mem_lblOf {c : Config} {i : ℕ} (hi : i < c.nreg kN) (h4 : c.nreg kN ≤ 4) :
    c.nreg (kL + i) ∈ lblOf c kN kL := by
  unfold lblOf
  exact List.mem_map.2 ⟨i, List.mem_range.2 (⋄), rfl⟩

end

end SweepEv

end Chazelle.Core
