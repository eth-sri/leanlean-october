module

public import proofs.HordijkSteelThreshold.WordCoreCount

@[expose] public section

namespace HordijkSteelThreshold
open Classical

def actualBinaryWords (N : ℕ) : Finset (List Bool) := (shortBinaryWords N).erase []

theorem mem_actualBinaryWords (s : List Bool) (N : ℕ) :
    s ∈ actualBinaryWords N ↔ s ≠ [] ∧ s.length ≤ N := by
  simp only [actualBinaryWords, Finset.mem_erase, mem_shortBinaryWords]

theorem actualBinaryWords_card (N : ℕ) : (actualBinaryWords N).card = 2 ^ (N + 1) - 2 := by
  have hexact (n : ℕ) : (shortBinaryWords n).card + 1 = 2 ^ (n + 1) := by
    induction n with
    | zero => simp [shortBinaryWords]
    | succ n ih =>
      have he : shortBinaryWords (n + 1) = insert []
          (((shortBinaryWords n).image (List.cons true)) ∪
           ((shortBinaryWords n).image (List.cons false))) := by ext; simp [shortBinaryWords]
      have hd : Disjoint ((shortBinaryWords n).image (List.cons true))
          ((shortBinaryWords n).image (List.cons false)) := by
        rw [Finset.disjoint_left]; rintro _ ha hb
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨_, _, h⟩ := Finset.mem_image.mp hb; cases h
      rw [he, Finset.card_insert_of_notMem (by simp), Finset.card_union_of_disjoint hd,
        Finset.card_image_of_injective _ List.cons_injective,
        Finset.card_image_of_injective _ List.cons_injective, pow_succ]
      omega
  have := hexact N
  simp only [actualBinaryWords, Finset.card_erase_of_mem ((mem_shortBinaryWords [] N).mpr (by simp))]
  omega

theorem molecular_minor_side_below_band (N M : ℕ) (hMN : M < N)
    (S : Finset (List Bool)) (hsub : S ⊆ actualBinaryWords N)
    (hminor : S.card ≤ (actualBinaryWords N \ S).card)
    (hconstant : ∀ u ∈ actualBinaryWords N, ∀ v ∈ actualBinaryWords N,
      M ≤ u.length → M ≤ v.length → (u ∈ S ↔ v ∈ S))
    (s : List Bool) (hs : s ∈ S) : s.length < M := by
  by_contra h
  have hcomp : actualBinaryWords N \ S ⊆ shortBinaryWords (M - 1) := fun t ht => by
    obtain ⟨htU, htS⟩ := Finset.mem_sdiff.mp ht
    exact (mem_shortBinaryWords t (M - 1)).mpr (Nat.le_sub_one_of_lt <| by
      by_contra hge; exact htS ((hconstant s (hsub hs) t htU (by omega) (by omega)).mp hs))
  have hM : 0 < M := by
    by_contra hz
    have hc : actualBinaryWords N \ S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun t ht =>
      (Finset.mem_sdiff.mp ht).2 ((hconstant s (hsub hs) t (Finset.mem_sdiff.mp ht).1 (by omega) (by omega)).mp hs)
    have := Finset.card_pos.mpr ⟨s, hs⟩
    simp only [hc, Finset.card_empty] at hminor; omega
  have hx := (Finset.card_le_card hcomp).trans_lt (shortBinaryWords_card_lt (M - 1))
  rw [Nat.sub_add_cancel hM] at hx
  have := (pow_lt_pow_iff_right₀ (by decide : 1 < 2)).mpr hMN
  have hpart := Finset.card_sdiff_add_card_eq_card hsub
  rw [actualBinaryWords_card, pow_succ] at hpart; omega

end HordijkSteelThreshold
