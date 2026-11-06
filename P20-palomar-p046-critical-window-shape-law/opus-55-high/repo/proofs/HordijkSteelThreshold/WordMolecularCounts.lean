module

public import proofs.HordijkSteelThreshold.WordCoreCount

@[expose] public section

namespace HordijkSteelThreshold
open Classical

theorem shortBinaryWords_card_exact (n : ℕ) :
    (shortBinaryWords n).card + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : shortBinaryWords (n + 1) = insert []
        (((shortBinaryWords n).image $ List.cons true) ∪
         ((shortBinaryWords n).image $ List.cons false)) := by
      simp [shortBinaryWords]
    have hd : Disjoint ((shortBinaryWords n).image $ List.cons true)
        ((shortBinaryWords n).image $ List.cons false) := by
      apply Finset.disjoint_left.mpr
      simp_all
    have hn : [] ∉ ((shortBinaryWords n).image $ List.cons true) ∪
        ((shortBinaryWords n).image $ List.cons false) := by simp
    simp_all
    rw [Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective]
    omega

variable (N : ℕ)

def actualBinaryWords  : Finset (List Bool) := (shortBinaryWords N).erase []

theorem mem_actualBinaryWords (s : List Bool) (N : ℕ) :
    s ∈ actualBinaryWords N ↔ s ≠ [] ∧ s.length ≤ N := by
  simp only [actualBinaryWords, Finset.mem_erase, mem_shortBinaryWords]

theorem actualBinaryWords_card  : (actualBinaryWords N).card = 2 ^ (N + 1) - 2 := by
  have h := shortBinaryWords_card_exact N
  have hn := (mem_shortBinaryWords [] N).mpr $ by simp
  simp only [actualBinaryWords, Finset.card_erase_of_mem hn]
  omega


/-- A molecularly smaller side cannot contain a constant-label high band with a spare level.
The proof counts the complement below M, rather than the contracted graph vertices. -/
theorem molecular_minor_side_below_band (N M : ℕ) (hMN : M < N)
    (S : Finset $ List Bool) (hsub : S ⊆ actualBinaryWords N)
    (hminor : S.card ≤ (actualBinaryWords N \ S).card)
    (hconstant : ∀ u ∈ actualBinaryWords N, ∀ v ∈ actualBinaryWords N,
      M ≤ u.length → M ≤ v.length → (u ∈ S ↔ v ∈ S))
    (s : List Bool) (hs : s ∈ S) : s.length < M := by
  by_contra h
  have hcomp : actualBinaryWords N \ S ⊆ shortBinaryWords (M - 1) := by
    intro t ht
    have hlt : t.length < M := by
      grind
    exact (mem_shortBinaryWords t $ M - 1).mpr $ by omega
  have hM : 0 < M := by
    by_contra hz
    have hc : actualBinaryWords N \ S = ∅ := by
      grind
    simp_all
  have hc : (actualBinaryWords N \ S).card < 2 ^ M := by
    have hx := (Finset.card_le_card hcomp).trans_lt $ shortBinaryWords_card_lt $ M - 1
    grind
  have hp : 2 ^ M < 2 ^ N := (pow_lt_pow_iff_right₀ $ by omega).mpr hMN
  have hpartition := Finset.card_sdiff_add_card_eq_card hsub
  rw [actualBinaryWords_card] at hpartition
  omega

end HordijkSteelThreshold
