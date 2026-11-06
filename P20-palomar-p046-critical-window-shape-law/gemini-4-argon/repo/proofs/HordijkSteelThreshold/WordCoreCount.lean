module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold
open Classical

def shortBinaryWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | k + 1 => insert [] ((Finset.univ : Finset Bool).biUnion
      (fun b => (shortBinaryWords k).image (List.cons b)))

theorem mem_shortBinaryWords (s : List Bool) (k : ℕ) :
    s ∈ shortBinaryWords k ↔ s.length ≤ k := by
  induction k generalizing s with
  | zero => simp [shortBinaryWords]
  | succ k ih =>
    cases s with
    | nil => simp [shortBinaryWords]
    | cons b t => cases b <;> simp [shortBinaryWords, ih]

theorem shortBinaryWords_card_lt (k : ℕ) : (shortBinaryWords k).card < 2 ^ (k + 1) := by
  induction k with
  | zero => simp [shortBinaryWords]
  | succ k ih =>
    have hc : ((Finset.univ : Finset Bool).biUnion
        (fun b => (shortBinaryWords k).image (List.cons b))).card ≤
        2 * (shortBinaryWords k).card :=
      Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun _ _ => Finset.card_image_le).trans_eq (by simp [two_mul]))
    have hi := Finset.card_insert_le [] ((Finset.univ : Finset Bool).biUnion
      (fun b => (shortBinaryWords k).image (List.cons b)))
    simp only [shortBinaryWords]; rw [pow_succ]; omega

theorem core_containing_words_card_lt (S : Finset (List Bool)) (core : List Bool) (k : ℕ)
    (hc : ∀ s ∈ S, ∃ l r : List Bool, s = l ++ core ++ r)
    (hl : ∀ s ∈ S, s.length ≤ core.length + k) : S.card < 2 ^ (2 * (k + 1)) := by
  have hs : S ⊆ ((shortBinaryWords k) ×ˢ (shortBinaryWords k)).image (fun lr => lr.1 ++ core ++ lr.2) := by
    intro s hs'
    obtain ⟨l, r, rfl⟩ := hc s hs'
    have hlen := hl _ hs'
    simp only [List.length_append] at hlen
    exact Finset.mem_image.mpr ⟨(l, r), Finset.mem_product.mpr
      ⟨(mem_shortBinaryWords l k).mpr (by omega), (mem_shortBinaryWords r k).mpr (by omega)⟩, rfl⟩
  refine ((Finset.card_le_card hs).trans (Finset.card_image_le.trans_eq (Finset.card_product _ _))).trans_lt ?_
  simpa only [← pow_add, two_mul] using Nat.mul_self_lt_mul_self (shortBinaryWords_card_lt k)

end HordijkSteelThreshold
