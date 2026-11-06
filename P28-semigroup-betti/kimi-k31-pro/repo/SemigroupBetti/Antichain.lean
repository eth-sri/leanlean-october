/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import SemigroupBetti.Identities

/-!
# Antichain counting

Write-up `PROOF_B_lean_writeup.md`: Lemma 10, Lemma 11, Lemma 12.
-/

@[expose] public section

namespace SemigroupBetti

open Finset

/-! ### Lemma 11: positive-pair antichains -/

section PairAntichain

variable {T : Finset (ℕ × ℕ)}

/-- Distinct members of `T` are coordinatewise incomparable. -/
def IsPairAntichain (T : Finset (ℕ × ℕ)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x.1 ≤ y.1 → x.2 ≤ y.2 → x = y

lemma IsPairAntichain.fst_inj (hT : IsPairAntichain T) {x y : ℕ × ℕ} (hx : x ∈ T) (hy : y ∈ T)
    (h : x.1 = y.1) : x = y :=
  (le_total x.2 y.2).elim (hT x hx y hy h.le) fun h2 => (hT y hy x hx h.ge h2).symm

lemma IsPairAntichain.snd_inj (hT : IsPairAntichain T) {x y : ℕ × ℕ} (hx : x ∈ T) (hy : y ∈ T)
    (h : x.2 = y.2) : x = y :=
  (le_total x.1 y.1).elim (fun h1 => hT x hx y hy h1 h.le) fun h1 => (hT y hy x hx h1 h.ge).symm

/-- **Lemma 11 (forward bound).** The number of members whose first coordinate is at most
`x.1` (the rank of `x` in the sorted enumeration) is at most `x.1`. -/
lemma IsPairAntichain.rank_le (hT : IsPairAntichain T) (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2)
    {x : ℕ × ℕ} : (T.filter (fun y => y.1 ≤ x.1)).card ≤ x.1 := by
  have := card_le_card_of_injOn (fun y : ℕ × ℕ => y.1) (s := T.filter (fun y => y.1 ≤ x.1)) (t := Icc 1 x.1)
    (fun y hy => by
      have hy' := mem_filter.1 (mem_coe.1 hy)
      exact mem_coe.2 (mem_Icc.2 ⟨(hpos y hy'.1).1, hy'.2⟩))
    (fun y hy y' hy' h => hT.fst_inj (mem_filter.1 (mem_coe.1 hy)).1
      (mem_filter.1 (mem_coe.1 hy')).1 h)
  simpa using this

/-- **Lemma 11 (backward bound).** The number of members whose first coordinate is at least
`x.1` is at most `x.2`. -/
lemma IsPairAntichain.corank_le (hT : IsPairAntichain T) (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2)
    {x : ℕ × ℕ} (hx : x ∈ T) : (T.filter (fun y => x.1 ≤ y.1)).card ≤ x.2 := by
  have hle : ∀ y ∈ T, x.1 ≤ y.1 → y.2 ≤ x.2 := by
    intro y hy h1
    by_contra h2
    have := hT x hx y hy h1 (by omega)
    subst this; omega
  have := card_le_card_of_injOn (fun y : ℕ × ℕ => y.2) (s := T.filter (fun y => x.1 ≤ y.1)) (t := Icc 1 x.2)
    (fun y hy => by
      have hy' := mem_filter.1 (mem_coe.1 hy)
      exact mem_coe.2 (mem_Icc.2 ⟨(hpos y hy'.1).2, hle y hy'.1 hy'.2⟩))
    (fun y hy y' hy' h => hT.snd_inj (mem_filter.1 (mem_coe.1 hy)).1
      (mem_filter.1 (mem_coe.1 hy')).1 h)
  simpa using this

/-- **Lemma 11.** In a positive-pair antichain with `k` members, for every `1 ≤ r ≤ k` the
`r`-th member in increasing order of first coordinate satisfies `u ≥ r` and `v ≥ k + 1 - r`.
(Stated as existence of a member with these bounds; the member is the one of rank `r`.) -/
theorem IsPairAntichain.exists_rank (hT : IsPairAntichain T)
    (hpos : ∀ x ∈ T, 1 ≤ x.1 ∧ 1 ≤ x.2) {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ T.card) :
    ∃ x ∈ T, r ≤ x.1 ∧ T.card + 1 - r ≤ x.2 := by
  classical
  let rk : ℕ × ℕ → ℕ := fun x => (T.filter (fun y => y.1 ≤ x.1)).card
  have hmaps : ∀ x (hx : x ∈ T), rk x ∈ Icc 1 T.card := by
    intro x hx
    refine mem_Icc.2 ⟨card_pos.2 ⟨x, mem_filter.2 ⟨hx, le_rfl⟩⟩, card_le_card (filter_subset _ _)⟩
  have hinj : ∀ x y (hx : x ∈ T) (hy : y ∈ T), rk x = rk y → x = y := by
    intro x y hx hy h
    by_contra hne
    have aux : ∀ x y, x ∈ T → y ∈ T → x.1 < y.1 → rk x < rk y := by
      intro x y hx hy hlt
      apply card_lt_card
      refine ⟨fun z hz => ?_, fun hsub => ?_⟩
      · have := mem_filter.1 hz; exact mem_filter.2 ⟨this.1, by omega⟩
      · have := (mem_filter.1 (hsub (mem_filter.2 ⟨hy, le_rfl⟩))).2; omega
    rcases lt_trichotomy x.1 y.1 with hlt | heq | hlt
    · have := aux x y hx hy hlt; omega
    · exact hne (hT.fst_inj hx hy heq)
    · have := aux y x hy hx hlt; omega
  obtain ⟨x, hx, hxr⟩ := surj_on_of_inj_on_of_card_le (fun x _ => rk x) hmaps hinj
    (by simp) r (mem_Icc.2 ⟨hr1, hrk⟩)
  refine ⟨x, hx, ?_, ?_⟩
  · have := hT.rank_le hpos (x := x); simp only [rk] at hxr; omega
  · have hunion : T.filter (fun y => y.1 ≤ x.1) ∪ T.filter (fun y => x.1 ≤ y.1) = T := by
      ext y; simp only [mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hy; rcases le_total y.1 x.1 with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
    have hinter : T.filter (fun y => y.1 ≤ x.1) ∩ T.filter (fun y => x.1 ≤ y.1) = {x} := by
      ext y; simp only [mem_inter, mem_filter, mem_singleton]
      constructor
      · rintro ⟨⟨hy, h1⟩, -, h2⟩; exact hT.fst_inj hy hx (le_antisymm h1 h2)
      · rintro rfl; exact ⟨⟨hx, le_rfl⟩, hx, le_rfl⟩
    have hsum := card_union_add_card_inter (T.filter (fun y => y.1 ≤ x.1))
      (T.filter (fun y => x.1 ≤ y.1))
    rw [hunion, hinter, card_singleton] at hsum
    have := hT.corank_le hpos hx
    simp only [rk] at hxr
    omega

end PairAntichain

namespace GenData

variable (G : GenData)

/-! ### Selected pairs -/

lemma sel_le_of_coords {K : Finset (Fin 4)} {i k : Fin 4} (hKe : K = {i, k}) (hK : K.card = 2)
    {d d' : ℕ} (hS : G.IsSplit d K) (hS' : G.IsSplit d' K)
    (hi : G.sel d K i ≤ G.sel d' K i) (hk : G.sel d K k ≤ G.sel d' K k) :
    G.sel d K ≤ G.sel d' K := by
  intro j
  by_cases hj : j ∈ K
  · rw [hKe, mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl <;> assumption
  · rw [G.sel_eq_zero hS hK hj, G.sel_eq_zero hS' hK hj]

lemma sel_coord_injOn {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) :
    Set.InjOn (fun d => G.sel d K k) F := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro d hd d' hd' h
  simp only at h
  by_contra hne
  rcases le_total (G.sel d K i) (G.sel d' K i) with hi | hi
  · exact G.sel_antichain hK (hF d hd) (hF d' hd') hne
      (G.sel_le_of_coords hKe hK (hF d hd) (hF d' hd') hi h.le)
  · exact G.sel_antichain hK (hF d' hd') (hF d hd) (Ne.symm hne)
      (G.sel_le_of_coords hKe hK (hF d' hd') (hF d hd) hi h.ge)

noncomputable def pairsOf (F : Finset ℕ) (K : Finset (Fin 4)) (i k : Fin 4) : Finset (ℕ × ℕ) :=
  F.image (fun d => (G.sel d K i, G.sel d K k))

lemma card_pairsOf {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) : (G.pairsOf F K i k).card = F.card :=
  card_image_of_injOn
    (fun _ hd _ hd' h => G.sel_coord_injOn hik hKe F hF hd hd' (congrArg Prod.snd h))

lemma pairsOf_antichain {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) : IsPairAntichain (G.pairsOf F K i k) := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro x hx y hy h1 h2
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  obtain ⟨d', hd', rfl⟩ := mem_image.1 hy
  by_cases hne : d = d'
  · rw [hne]
  · exact absurd (G.sel_le_of_coords hKe hK (hF d hd) (hF d' hd') h1 h2)
      (G.sel_antichain hK (hF d hd) (hF d' hd') hne)

lemma pairsOf_pos {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) :
    ∀ x ∈ G.pairsOf F K i k, 1 ≤ x.1 ∧ 1 ≤ x.2 := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro x hx
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  exact ⟨G.sel_pos (hF d hd) hK (by rw [hKe]; simp),
    G.sel_pos (hF d hd) hK (by rw [hKe]; simp)⟩

/-- A family whose selected `k`-coordinates are injective with values in `[1, c]` has at most
`c` members. -/
lemma card_le_of_coord {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ G.sel d K k ∧ G.sel d K k ≤ c) : F.card ≤ c := by
  have := card_le_card_of_injOn (fun d => G.sel d K k) (t := Icc 1 c)
    (fun d hd => mem_coe.2 (mem_Icc.2 (hc d (mem_coe.1 hd))))
    (G.sel_coord_injOn hik hKe F hF)
  simpa using this

lemma isSplit_of_mem_fam {K : Finset (Fin 4)} {d : ℕ} (h : d ∈ G.fam K) : G.IsSplit d K :=
  (G.mem_fam.1 h).2.2.2

lemma sideP_split {d : ℕ} (hd : d ∈ G.famP) : G.IsSplit d {2, 3} := by
  have hc : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
  exact hc ▸ (G.isSplit_of_mem_fam hd).compl

lemma sideQ_split {d : ℕ} (hd : d ∈ G.famQ) : G.IsSplit d {1, 3} := by
  have hc : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
  exact hc ▸ (G.isSplit_of_mem_fam hd).compl

/-- **Lemma 10.** `P ≤ R - 1`. -/
theorem P_le : G.P ≤ G.R - 1 := by
  have h1 : G.P ≤ G.B - 1 :=
    G.card_le_of_coord (i := 0) (k := 1) (by decide) rfl G.famP
      (fun d hd => G.isSplit_of_mem_fam hd)
      (fun d hd => G.sel_one_bounds (G.isSplit_of_mem_fam hd) (by decide) (by decide))
  have h2 : G.P ≤ G.W - G.A - 1 :=
    G.card_le_of_coord (K := {2, 3}) (i := 3) (k := 2) (by decide) (by decide) G.famP
      (fun d hd => G.sideP_split hd)
      (fun d hd => G.sel_two_bounds (G.sideP_split hd) (by decide) (by decide))
  unfold R; omega

/-- **Lemma 10.** `Q ≤ R - 1`. -/
theorem Q_le : G.Q ≤ G.R - 1 := by
  have h1 : G.Q ≤ G.W - G.A - 1 :=
    G.card_le_of_coord (i := 0) (k := 2) (by decide) rfl G.famQ
      (fun d hd => G.isSplit_of_mem_fam hd)
      (fun d hd => G.sel_two_bounds (G.isSplit_of_mem_fam hd) (by decide) (by decide))
  have h2 : G.Q ≤ G.B - 1 :=
    G.card_le_of_coord (K := {1, 3}) (i := 3) (k := 1) (by decide) (by decide) G.famQ
      (fun d hd => G.sideQ_split hd)
      (fun d hd => G.sel_one_bounds (G.sideQ_split hd) (by decide) (by decide))
  unfold R; omega

/-! ### Lemma 12 -/

lemma isSplit12_of_mem_famE {d : ℕ} (h : d ∈ G.famE) : G.IsSplit d {1, 2} := by
  have hc : ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} := by decide
  exact hc ▸ (G.isSplit_of_mem_fam h).compl

noncomputable abbrev pairsE : Finset (ℕ × ℕ) := G.pairsOf G.famE {1, 2} 1 2

lemma card_pairsE : G.pairsE.card = G.E :=
  G.card_pairsOf (by decide) rfl fun _ => G.isSplit12_of_mem_famE

lemma pairsE_antichain : IsPairAntichain G.pairsE :=
  G.pairsOf_antichain (by decide) rfl fun _ => G.isSplit12_of_mem_famE

lemma pairsE_pos : ∀ x ∈ G.pairsE, 1 ≤ x.1 ∧ 1 ≤ x.2 :=
  G.pairsOf_pos (by decide) rfl fun _ => G.isSplit12_of_mem_famE

/-- **Lemma 12.** `E ≤ p + q - 1`. -/
theorem E_le : G.E ≤ G.p + G.q - 1 := by
  by_contra hc
  have hp := G.p_pos
  have hq := G.q_pos
  have hk : G.p + G.q ≤ G.pairsE.card := by rw [card_pairsE]; omega
  obtain ⟨x, hx, hx1, hx2⟩ :=
    G.pairsE_antichain.exists_rank G.pairsE_pos (r := G.p) hp (by omega)
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  set z := G.sel d {1, 2}
  have hv : G.q ≤ z 2 := by simp only at hx2; omega
  have hne : (z 1, z 2) ≠ (G.p, G.q) :=
    fun h => by simp only [Prod.mk.injEq] at h; simp only at hx2; omega
  have hS := G.isSplit12_of_mem_famE hd
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  have hU : G.U3 ≤ z := by
    intro i; fin_cases i <;> simp [U3, hx1, hv]
  by_cases h1 : G.p < z 1
  · exact G.no_replace hS hK hU G.identity3 (k := 1) (by simpa [U3] using h1)
      (j := 0) (by decide) (by simp [V3]; omega)
  · have h2 : G.q < z 2 := by
      by_contra h2
      exact hne (Prod.ext (by omega) (by omega))
    exact G.no_replace hS hK hU G.identity3 (k := 2) (by simpa [U3] using h2)
      (j := 0) (by decide) (by simp [V3]; omega)

end GenData

end SemigroupBetti
