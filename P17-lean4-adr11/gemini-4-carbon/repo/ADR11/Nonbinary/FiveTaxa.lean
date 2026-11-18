module

public import ADR11.Identifiability.Unrooted

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

def t5Code (b c : ℕ) : List ℕ := unrootL 5 [1, 2, 4, 8, 16, b, c, 31]

def T5code : ℕ → List ℕ
  | 1 => t5Code 3 7 | 2 => t5Code 3 11 | 3 => t5Code 3 19 | 4 => t5Code 5 7
  | 5 => t5Code 5 13 | 6 => t5Code 5 21 | 7 => t5Code 9 11 | 8 => t5Code 9 13
  | 9 => t5Code 9 25 | 10 => t5Code 17 19
  | 13 => t5Code 6 7 | 14 => t5Code 10 11 | 15 => t5Code 18 19
  | _ => []

@[simp] lemma decC_5_3 : decC 5 3 = {0, 1} := by decide +kernel
@[simp] lemma decC_5_7 : decC 5 7 = {0, 1, 2} := by decide +kernel
@[simp] lemma decC_5_15 : decC 5 15 = {0, 1, 2, 3} := by decide +kernel
@[simp] lemma decC_5_24 : decC 5 24 = {3, 4} := by decide +kernel
@[simp] lemma decC_5_27 : decC 5 27 = {0, 1, 3, 4} := by decide +kernel

def bal5Poly (i : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  let m1 := [(7, 1), (24, 1)]; let m2 := (3, 1) :: m1; let m3 := [(3, 1), (7, 3), (24, 1)]
  match i with
  | 1 => [(1, []), (-2/3, [(3, 1)]), (-2/3, m1), (1/3, m2), (1/15, m3)]
  | 2 | 3 => [(1/3, m1), (-1/6, m2), (-1/10, m3)]
  | 4 | 13 => [(1/3, [(3, 1)]), (-1/3, m2), (1/15, m3)]
  | 5 | 9 => [(1/6, m2), (-1/10, m3)]
  | _ => [(1/15, m3)]

def cat5Poly (i : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  let m1 := [(3, 1), (7, 1)]; let m2 := [(3, 1), (7, 3)]; let m3 := [(3, 1), (7, 3), (15, 6)]
  match i with
  | 1 => [(1, []), (-2/3, [(3, 1)]), (-2/3, [(7, 1)]), (1/3, m1), (1/18, m2), (1/90, m3)]
  | 2 => [(1/3, [(7, 1)]), (-1/6, m1), (-1/9, m2), (1/90, m3)]
  | 3 => [(1/3, [(7, 1)]), (-1/6, m1), (-1/18, m2), (-2/45, m3)]
  | 4 | 13 => [(1/3, [(3, 1)]), (-1/3, m1), (1/18, m2), (1/90, m3)]
  | 6 | 9 => [(1/6, m1), (-1/18, m2), (-2/45, m3)]
  | _ => [(1/18, m2), (1/90, m3)]

def pse5Poly (i : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  let m1 := [(3, 1), (24, 1)]; let m2 := [(3, 1), (24, 1), (27, 6)]
  match i with
  | 2 | 3 => [(1/3, [(24, 1)]), (-5/18, m1), (1/90, m2)]
  | 4 | 13 => [(1/3, [(3, 1)]), (-5/18, m1), (1/90, m2)]
  | 8 => [(1/9, m1), (-2/45, m2)]
  | _ => [(1/18, m1), (1/90, m2)]

lemma u_sub_certsB {H : Finset (Finset (Fin 5))} (hH : IsHierarchy H) (T : BTree)
    (hwf : T.wfB 5 H = true) (htop : T.code = 31) (is : List ℕ)
    (hd : ∀ j ∈ is, decF 5 (T5code j) = T5 j)
    (P : ℕ → List (ℚ × List (ℕ × ℕ)))
    (hc : certsB 5 (T.outL 5) (is.map fun i => (T5code i, P i)) = true)
    (σ : SpeciesTree (Fin 5)) (hsub : σ.clusters ⊆ H) {i : ℕ} (hi : i ∈ is) :
    u σ i = evalPoly (fun A => if A ∈ σ.clusters then σ.length A else 0) (P i) := by
  unfold u; rw [← hd i hi]
  exact unrootedDist_sub_of_certsB hH T hwf htop hc σ hsub (List.mem_map.2 ⟨i, hi, rfl⟩)

lemma u_sub_bal5 (σ : SpeciesTree (Fin 5)) (hsub : σ.clusters ⊆ balanced5) (i : ℕ)
    (hi : i ∈ ([1, 2, 3, 4, 5, 8, 9, 13, 15] : List ℕ) := by decide) :
    u σ i = evalPoly (fun A => if A ∈ σ.clusters then σ.length A else 0) (bal5Poly i) :=
  u_sub_certsB ⟨by decide, by decide, by decide, by decide⟩
    (.bin 31 (.bin 7 (.bin 3 (.leaf 0) (.leaf 1)) (.leaf 2)) (.bin 24 (.leaf 3) (.leaf 4)))
    (by decide +kernel) rfl _ (by decide +kernel) bal5Poly (by decide +kernel) σ hsub hi

lemma u_sub_cat5 (σ : SpeciesTree (Fin 5)) (hsub : σ.clusters ⊆ caterpillar5) (i : ℕ)
    (hi : i ∈ ([1, 2, 3, 4, 6, 7, 9, 10, 13, 14, 15] : List ℕ) := by decide) :
    u σ i = evalPoly (fun A => if A ∈ σ.clusters then σ.length A else 0) (cat5Poly i) :=
  u_sub_certsB ⟨by decide, by decide, by decide, by decide⟩
    (.bin 31 (.bin 15 (.bin 7 (.bin 3 (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)) (.leaf 4))
    (by decide +kernel) rfl _ (by decide +kernel) cat5Poly (by decide +kernel) σ hsub hi

lemma u_sub_pse5 (σ : SpeciesTree (Fin 5)) (hsub : σ.clusters ⊆ pseudocaterpillar5) (i : ℕ)
    (hi : i ∈ ([2, 3, 4, 5, 7, 8, 13] : List ℕ) := by decide) :
    u σ i = evalPoly (fun A => if A ∈ σ.clusters then σ.length A else 0) (pse5Poly i) :=
  u_sub_certsB ⟨by decide, by decide, by decide, by decide⟩
    (.bin 31 (.bin 27 (.bin 3 (.leaf 0) (.leaf 1)) (.bin 24 (.leaf 3) (.leaf 4))) (.leaf 2))
    (by decide +kernel) rfl _ (by decide +kernel) pse5Poly (by decide +kernel) σ hsub hi

abbrev c01 : Finset (Fin 5) := {0, 1}
abbrev c34 : Finset (Fin 5) := {3, 4}
abbrev c012 : Finset (Fin 5) := {0, 1, 2}
abbrev c0123 : Finset (Fin 5) := {0, 1, 2, 3}
abbrev c0134 : Finset (Fin 5) := {0, 1, 3, 4}

noncomputable def eVal (τ : SpeciesTree (Fin 5)) (A : Finset (Fin 5)) : ℝ :=
  exp (-if A ∈ τ.clusters then τ.length A else 0)

lemma eVal_pos (τ : SpeciesTree (Fin 5)) (A : Finset (Fin 5)) : 0 < eVal τ A := exp_pos _

lemma eVal_lt_one_iff (τ : SpeciesTree (Fin 5)) {A : Finset (Fin 5)} (hAu : A ≠ univ) :
    eVal τ A < 1 ↔ A ∈ τ.clusters := by
  unfold eVal; split_ifs with h
  · exact ⟨fun _ => h, fun _ => exp_lt_one_iff.2 (neg_lt_zero.2 (τ.length_pos A h hAu))⟩
  · simp [h]

lemma eVal_pow_lt_one (τ : SpeciesTree (Fin 5)) {A : Finset (Fin 5)} (hAu : A ≠ univ)
    (hA : A ∈ τ.clusters) {n : ℕ} (hn : n ≠ 0) : eVal τ A ^ n < 1 :=
  pow_lt_one₀ (eVal_pos τ A).le ((eVal_lt_one_iff τ hAu).2 hA) hn

lemma cat5_rels (ρ : SpeciesTree (Fin 5)) (hsub : ρ.clusters ⊆ caterpillar5) :
    u ρ 2 - u ρ 3 = -1 / 18 * eVal ρ c01 * eVal ρ c012 ^ 3 * (1 - eVal ρ c0123 ^ 6) ∧
    (c0123 ∈ ρ.clusters → u ρ 2 < u ρ 3) ∧ u ρ 4 = u ρ 13 ∧
    (c012 ∉ ρ.clusters → u ρ 1 = u ρ 2) ∧ (c01 ∉ ρ.clusters → u ρ 1 = u ρ 13) ∧
    u ρ 10 = u ρ 15 ∧
    (c01 ∉ ρ.clusters → c012 ∉ ρ.clusters →
      u ρ 7 = u ρ 2 ∧ u ρ 14 = u ρ 2 ∧ u ρ 6 = u ρ 3 ∧ u ρ 9 = u ρ 3) := by
  have d23 : u ρ 2 - u ρ 3 = -1 / 18 * eVal ρ c01 * eVal ρ c012 ^ 3 * (1 - eVal ρ c0123 ^ 6) := by
    rw [u_sub_cat5 ρ hsub 2, u_sub_cat5 ρ hsub 3]; simp [cat5Poly, eVal]; ring
  refine ⟨d23, fun hz => ?_, by rw [u_sub_cat5 ρ hsub 4, u_sub_cat5 ρ hsub 13]; rfl,
    fun hy => ?_, fun hx => ?_, by rw [u_sub_cat5 ρ hsub 10, u_sub_cat5 ρ hsub 15]; rfl, fun hx hy => ?_⟩
  · have hz6 := eVal_pow_lt_one ρ (by decide) hz (n := 6) (by decide)
    have hxy : 0 < eVal ρ c01 * eVal ρ c012 ^ 3 := by positivity [eVal_pos ρ c01, eVal_pos ρ c012]
    linarith [mul_pos hxy (show 0 < 1 - eVal ρ c0123 ^ 6 by linarith)]
  · rw [u_sub_cat5 ρ hsub 1, u_sub_cat5 ρ hsub 2]; simp [cat5Poly, hy]; ring
  · rw [u_sub_cat5 ρ hsub 1, u_sub_cat5 ρ hsub 13]; simp [cat5Poly, hx]; ring
  · have e7 : u ρ 7 = u ρ 2 := by rw [u_sub_cat5 ρ hsub 7, u_sub_cat5 ρ hsub 2]; simp [cat5Poly, hx, hy]; ring
    have e6 : u ρ 6 = u ρ 3 := by rw [u_sub_cat5 ρ hsub 6, u_sub_cat5 ρ hsub 3]; simp [cat5Poly, hx, hy]; ring
    exact ⟨e7, by rw [← e7, u_sub_cat5 ρ hsub 14, u_sub_cat5 ρ hsub 7]; rfl,
      e6, by rw [← e6, u_sub_cat5 ρ hsub 9, u_sub_cat5 ρ hsub 6]; rfl⟩

lemma bal5_diffs (ρ : SpeciesTree (Fin 5)) (hsub : ρ.clusters ⊆ balanced5) :
    u ρ 2 = u ρ 3 ∧ u ρ 4 = u ρ 13 ∧ u ρ 8 = u ρ 15 ∧ u ρ 5 = u ρ 9 ∧
    u ρ 5 - u ρ 8 = 1 / 6 * eVal ρ c01 * eVal ρ c012 * eVal ρ c34 * (1 - eVal ρ c012 ^ 2) ∧
    15 * u ρ 8 = (eVal ρ c01 * eVal ρ c012 * eVal ρ c34) * eVal ρ c012 ^ 2 :=
  ⟨by rw [u_sub_bal5 ρ hsub 2, u_sub_bal5 ρ hsub 3]; rfl,
   by rw [u_sub_bal5 ρ hsub 4, u_sub_bal5 ρ hsub 13]; rfl,
   by rw [u_sub_bal5 ρ hsub 8, u_sub_bal5 ρ hsub 15]; rfl,
   by rw [u_sub_bal5 ρ hsub 5, u_sub_bal5 ρ hsub 9]; rfl,
   by rw [u_sub_bal5 ρ hsub 5, u_sub_bal5 ρ hsub 8]; simp [bal5Poly, eVal]; ring,
   by rw [u_sub_bal5 ρ hsub 8]; simp [bal5Poly, eVal]; ring⟩

lemma pse5_diffs (ρ : SpeciesTree (Fin 5)) (hsub : ρ.clusters ⊆ pseudocaterpillar5) :
    u ρ 2 = u ρ 3 ∧ u ρ 4 = u ρ 13 ∧
    u ρ 5 - u ρ 8 = -1 / 18 * eVal ρ c01 * eVal ρ c34 * (1 - eVal ρ c0134 ^ 6) ∧
    u ρ 7 - u ρ 8 = -1 / 18 * eVal ρ c01 * eVal ρ c34 * (1 - eVal ρ c0134 ^ 6) :=
  ⟨by rw [u_sub_pse5 ρ hsub 2, u_sub_pse5 ρ hsub 3]; rfl,
   by rw [u_sub_pse5 ρ hsub 4, u_sub_pse5 ρ hsub 13]; rfl,
   by rw [u_sub_pse5 ρ hsub 5, u_sub_pse5 ρ hsub 8]; simp [pse5Poly, eVal]; ring,
   by rw [u_sub_pse5 ρ hsub 7, u_sub_pse5 ρ hsub 8]; simp [pse5Poly, eVal]; ring⟩

lemma same_of_eVal_eq {A B C : Finset (Fin 5)}
    {ρ ρ' : SpeciesTree (Fin 5)} (hsub : ρ.clusters ⊆ hierarchyOf {A, B, C})
    (hsub' : ρ'.clusters ⊆ hierarchyOf {A, B, C})
    (hA : eVal ρ A = eVal ρ' A) (hB : eVal ρ B = eVal ρ' B) (hC : eVal ρ C = eVal ρ' C)
    (hSu : A ≠ univ ∧ B ≠ univ ∧ C ≠ univ := by decide) :
    ρ.SameRootedMetricTree ρ' := by
  have heq : ∀ D ∈ ({A, B, C} : Finset _), D ≠ univ ∧ eVal ρ D = eVal ρ' D := by
    simp only [mem_insert, mem_singleton]
    rintro D (rfl | rfl | rfl); exacts [⟨hSu.1, hA⟩, ⟨hSu.2.1, hB⟩, ⟨hSu.2.2, hC⟩]
  have hcl_sub : ∀ a b : SpeciesTree (Fin 5), a.clusters ⊆ hierarchyOf {A, B, C} →
      (∀ D ∈ ({A, B, C} : Finset _), eVal a D = eVal b D) → a.clusters ⊆ b.clusters := fun a b ha hab D hD => by
    rcases mem_insert.1 (ha hD) with rfl | h'
    · exact b.univ_mem
    · rcases mem_union.1 h' with hDS | hx
      · exact (eVal_lt_one_iff b (heq D hDS).1).1 (hab D hDS ▸ (eVal_lt_one_iff a (heq D hDS).1).2 hD)
      · obtain ⟨x, -, rfl⟩ := mem_image.1 hx; exact b.singleton_mem x
  have hcl := Subset.antisymm (hcl_sub ρ ρ' hsub fun D hD => (heq D hD).2)
    (hcl_sub ρ' ρ hsub' fun D hD => (heq D hD).2.symm)
  refine ⟨hcl, fun D hD hD2 hDu => ?_⟩
  rcases mem_insert.1 (hsub hD) with rfl | h'
  · exact absurd rfl hDu
  · rcases mem_union.1 h' with hDS | hx
    · have hD' : D ∈ ρ'.clusters := hcl ▸ hD
      have he := (heq D hDS).2
      simp only [eVal, ite_eq_left hD, ite_eq_left hD'] at he
      linarith [exp_injective he]
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hx; simp at hD2

lemma u_rels (τ : SpeciesTree (Fin 5)) (g : Equiv.Perm (Fin 5)) {l : List (ℕ × ℕ)}
    (h : ∀ p ∈ l, relabelFamily g (T5 p.1) = T5 p.2) :
    (l.map fun p => u τ p.1) = l.map fun p => u (τ.relabel g) p.2 :=
  List.map_congr_left fun p hp => by unfold u; rw [← h p hp, SpeciesTree.unrootedDist_relabel]

abbrev sw (a b : Fin 5) : Equiv.Perm (Fin 5) := Equiv.swap a b
def pFlip : Equiv.Perm (Fin 5) := (sw 0 3).trans (sw 1 4)
def pFlip2 : Equiv.Perm (Fin 5) := (sw 0 4).trans (sw 1 3)

noncomputable def tag0 (τ : SpeciesTree (Fin 5)) : ℕ :=
  if u τ 4 < u τ 13 then 1 else if u τ 13 < u τ 4 then 2
  else if u τ 2 < u τ 1 then 3 else if u τ 1 < u τ 2 then 4 else 0

noncomputable def tag1 (τ : SpeciesTree (Fin 5)) : ℕ :=
  if u τ 2 < u τ 1 then 5 else if u τ 1 < u τ 2 then 6 else if u τ 1 < u τ 3 then 7
  else if u τ 4 < u τ 13 then 3 else if u τ 13 < u τ 4 then 4 else 0

noncomputable def tag2 (τ : SpeciesTree (Fin 5)) : ℕ :=
  if u τ 2 < u τ 3 then 0 else if u τ 3 < u τ 2 then 1 else if u τ 4 < u τ 13 then 2
  else if u τ 13 < u τ 4 then 3 else if u τ 8 < u τ 5 then 5 else if u τ 8 < u τ 7 then 6 else 4

noncomputable def pick (k : ℕ) (τ : SpeciesTree (Fin 5)) :
    Equiv.Perm (Fin 5) × Finset (Finset (Fin 5)) :=
  match k with
  | 0 => (match tag0 τ with
    | 1 => sw 0 4 | 2 => sw 1 4 | 3 => sw 2 4 | 4 => sw 3 4 | _ => .refl _, caterpillar5)
  | 1 => match tag1 τ with
    | 0 => (pFlip, balanced5) | 3 => (pFlip2, caterpillar5) | 4 => (pFlip, caterpillar5)
    | 5 => (sw 2 4, caterpillar5) | 6 => (sw 3 4, caterpillar5) | _ => (.refl _, caterpillar5)
  | _ => match tag2 τ with
    | 0 => (.refl _, caterpillar5) | 1 => (sw 3 4, caterpillar5)
    | 2 => (pFlip2, caterpillar5) | 3 => (pFlip, caterpillar5)
    | 5 => (.refl _, balanced5) | 6 => (pFlip, balanced5) | _ => (.refl _, pseudocaterpillar5)

section
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype
set_option synthInstance.maxSize 2000

lemma pick_spec (τ : SpeciesTree (Fin 5)) {k : ℕ} (hk : k ∈ ({0, 1, 2} : Finset ℕ))
    (h : unroot τ.clusters = U5 k) :
    (τ.relabel (pick k τ).1).clusters ⊆ (pick k τ).2 := by
  have u_pFlip : let ρ := τ.relabel pFlip
      u τ 1 = u ρ 1 ∧ u τ 2 = u ρ 13 ∧ u τ 3 = u ρ 4 ∧ u τ 4 = u ρ 3 ∧
      u τ 5 = u ρ 15 ∧ u τ 7 = u ρ 9 ∧ u τ 8 = u ρ 8 ∧ u τ 13 = u ρ 2 := by
    simpa using u_rels τ pFlip (l := [(1, 1), (2, 13), (3, 4), (4, 3), (5, 15), (7, 9), (8, 8), (13, 2)])
      (by decide +kernel)
  have u_pFlip2 : let ρ := τ.relabel pFlip2
      u τ 1 = u ρ 1 ∧ u τ 2 = u ρ 4 ∧ u τ 3 = u ρ 13 ∧ u τ 4 = u ρ 2 ∧ u τ 13 = u ρ 3 := by
    simpa using u_rels τ pFlip2 (l := [(1, 1), (2, 4), (3, 13), (4, 2), (13, 3)]) (by decide +kernel)
  have u_swap34 : let ρ := τ.relabel (sw 3 4)
      u τ 1 = u ρ 1 ∧ u τ 2 = u ρ 3 ∧ u τ 3 = u ρ 2 ∧ u τ 4 = u ρ 4 ∧ u τ 13 = u ρ 13 := by
    simpa using u_rels τ (sw 3 4) (l := [(1, 1), (2, 3), (3, 2), (4, 4), (13, 13)]) (by decide +kernel)
  have u_swap24 : let ρ := τ.relabel (sw 2 4)
      u τ 1 = u ρ 3 ∧ u τ 2 = u ρ 2 ∧ u τ 3 = u ρ 1 ∧ u τ 4 = u ρ 10 ∧ u τ 13 = u ρ 15 := by
    simpa using u_rels τ (sw 2 4) (l := [(1, 3), (2, 2), (3, 1), (4, 10), (13, 15)]) (by decide +kernel)
  have bal_pos : ∀ ρ : SpeciesTree (Fin 5), ρ.clusters ⊆ balanced5 →
      c012 ∈ ρ.clusters → u ρ 8 < u ρ 5 := fun ρ hsub hy => by
    obtain ⟨-, -, -, -, d58, -⟩ := bal5_diffs ρ hsub
    have hy2 := eVal_pow_lt_one ρ (by decide) hy (n := 2) (by decide)
    have hp : 0 < eVal ρ c01 * eVal ρ c012 * eVal ρ c34 := by
      positivity [eVal_pos ρ c01, eVal_pos ρ c012, eVal_pos ρ c34]
    linarith [mul_pos hp (show 0 < 1 - eVal ρ c012 ^ 2 by linarith)]
  simp only [mem_insert, mem_singleton] at hk
  unfold pick
  rcases hk with rfl | rfl | rfl
  · have hm := by_unrootB (fun C =>
      let f g := relabelFamily g C
      let s01 g := decide (f g ⊆ caterpillar5) && !decide (c01 ∈ f g) && !decide (c012 ∈ f g) && decide (c0123 ∈ f g)
      s01 (sw 0 4) || s01 (sw 1 4) || (decide (f (sw 2 4) ⊆ caterpillar5) && decide (c0123 ∈ f (sw 2 4))) ||
      (decide (f (sw 3 4) ⊆ caterpillar5) && !decide (c012 ∈ f (sw 3 4)) && decide (c0123 ∈ f (sw 3 4))) ||
      (decide (C ⊆ caterpillar5) && !decide (c012 ∈ C))) (by decide +kernel) h
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at hm
    rcases hm with ((((⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨h1, h2⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨h1, h2⟩)
    · obtain ⟨r4, r13⟩ : u τ 4 = _ ∧ u τ 13 = _ := by
        simpa using u_rels τ (sw 0 4) (l := [(4, 7), (13, 9)]) (by decide +kernel)
      obtain ⟨-, rlt, -, -, -, -, hst⟩ := cat5_rels (τ.relabel (sw 0 4)) h1
      obtain ⟨e7, -, -, e9⟩ := hst h2 h3
      rw [show tag0 τ = 1 by simp [tag0, r4, r13, e7, e9, rlt h4]]; exact h1
    · obtain ⟨r4, r13⟩ : u τ 4 = _ ∧ u τ 13 = _ := by
        simpa using u_rels τ (sw 1 4) (l := [(4, 6), (13, 14)]) (by decide +kernel)
      obtain ⟨-, rlt, -, -, -, -, hst⟩ := cat5_rels (τ.relabel (sw 1 4)) h1
      obtain ⟨-, e14, e6, -⟩ := hst h2 h3
      rw [show tag0 τ = 2 by simp [tag0, r4, r13, e6, e14, rlt h4, (rlt h4).le]]; exact h1
    · obtain ⟨-, rlt, -, -, -, e1015, -⟩ := cat5_rels (τ.relabel (sw 2 4)) h1
      rw [show tag0 τ = 3 by simp [tag0, u_swap24, e1015, rlt h2]]; exact h1
    · obtain ⟨-, rlt, e413, e12, -⟩ := cat5_rels (τ.relabel (sw 3 4)) h1
      rw [show tag0 τ = 4 by simp [tag0, u_swap34, e413, e12 h2, rlt h3, (rlt h3).le]]; exact h1
    · obtain ⟨-, -, e413, e12, -⟩ := cat5_rels τ h1
      rw [show tag0 τ = 0 by simp [tag0, e413, e12 h2]]; simpa using h1
  · have hm := by_unrootB (fun C =>
      let f g := relabelFamily g C
      let s34 g := decide (f g ⊆ caterpillar5) && !decide (c01 ∈ f g) && decide (c0123 ∈ f g)
      s34 pFlip2 || s34 pFlip || (decide (f (sw 2 4) ⊆ caterpillar5) && decide (c0123 ∈ f (sw 2 4))) ||
      (decide (f (sw 3 4) ⊆ caterpillar5) && !decide (c012 ∈ f (sw 3 4)) && decide (c0123 ∈ f (sw 3 4))) ||
      (decide (C ⊆ caterpillar5) && !decide (c012 ∈ C) && decide (c0123 ∈ C)) ||
      (decide (f pFlip ⊆ balanced5) && !decide (c01 ∈ f pFlip))) (by decide +kernel) h
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at hm
    rcases hm with (((((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨h1, h2⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨h1, h2⟩)
    · obtain ⟨-, rlt, e413, -, e113, -⟩ := cat5_rels (τ.relabel pFlip2) h1
      rw [show tag1 τ = 3 by simp [tag1, u_pFlip2, e113 h2, e413, rlt h3]]; exact h1
    · obtain ⟨-, rlt, e413, -, e113, -⟩ := cat5_rels (τ.relabel pFlip) h1
      rw [show tag1 τ = 4 by simp [tag1, u_pFlip, e113 h2, e413, rlt h3, (rlt h3).le]]; exact h1
    · obtain ⟨-, rlt, -⟩ := cat5_rels (τ.relabel (sw 2 4)) h1
      rw [show tag1 τ = 5 by simp [tag1, u_swap24, rlt h2]]; exact h1
    · obtain ⟨-, rlt, -, e12, -⟩ := cat5_rels (τ.relabel (sw 3 4)) h1
      rw [show tag1 τ = 6 by simp [tag1, u_swap34, e12 h2, rlt h3, (rlt h3).le]]; exact h1
    · obtain ⟨-, rlt, -, e12, -⟩ := cat5_rels τ h1
      rw [show tag1 τ = 7 by simp [tag1, e12 h2, rlt h3]]; simpa using h1
    · have e113 : u (τ.relabel pFlip) 1 = u (τ.relabel pFlip) 13 := by
        rw [u_sub_bal5 (τ.relabel pFlip) h1 1, u_sub_bal5 (τ.relabel pFlip) h1 13]; simp [bal5Poly, h2]; ring
      obtain ⟨e23, e413, -⟩ := bal5_diffs (τ.relabel pFlip) h1
      rw [show tag1 τ = 0 by simp [tag1, u_pFlip, e113, ← e413, e23]]; exact h1
  · have hm := by_unrootB (fun C =>
      let f g := relabelFamily g C
      let s g := decide (f g ⊆ caterpillar5) && decide (c0123 ∈ f g)
      (decide (C ⊆ caterpillar5) && decide (c0123 ∈ C)) || s (sw 3 4) || s pFlip2 || s pFlip ||
      decide (C ⊆ pseudocaterpillar5) || (decide (C ⊆ balanced5) && decide (c012 ∈ C)) ||
      (decide (f pFlip ⊆ balanced5) && decide (c012 ∈ f pFlip))) (by decide +kernel) h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hm
    rcases hm with ((((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | h1) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · rw [show tag2 τ = 0 by simp [tag2, (cat5_rels τ h1).2.1 h2]]; simpa using h1
    · have hlt := (cat5_rels (τ.relabel (sw 3 4)) h1).2.1 h2
      rw [show tag2 τ = 1 by simp [tag2, u_swap34, hlt, hlt.le]]; exact h1
    · obtain ⟨-, rlt, e413, -⟩ := cat5_rels (τ.relabel pFlip2) h1
      rw [show tag2 τ = 2 by simp [tag2, u_pFlip2, e413, rlt h2]]; exact h1
    · obtain ⟨-, rlt, e413, -⟩ := cat5_rels (τ.relabel pFlip) h1
      rw [show tag2 τ = 3 by simp [tag2, u_pFlip, e413, rlt h2, (rlt h2).le]]; exact h1
    · obtain ⟨e23, e413, d58, d78⟩ := pse5_diffs τ h1
      have hz6 : eVal τ c0134 ^ 6 ≤ 1 := pow_le_one₀ (eVal_pos τ _).le
        (exp_le_one_iff.2 (neg_nonpos.2 (by split_ifs with hm'; exacts [(τ.length_pos _ hm' (by decide)).le, le_rfl])))
      have hle := mul_nonneg (mul_pos (eVal_pos τ c01) (eVal_pos τ c34)).le
        (show 0 ≤ 1 - eVal τ c0134 ^ 6 by linarith)
      rw [show tag2 τ = 4 by unfold tag2; split_ifs <;> linarith]; simpa using h1
    · obtain ⟨e23, e413, -⟩ := bal5_diffs τ h1
      rw [show tag2 τ = 5 by unfold tag2; rw [e23, e413]; simp [bal_pos τ h1 h2]]; simpa using h1
    · obtain ⟨e23, e413, e815, e59, -⟩ := bal5_diffs (τ.relabel pFlip) h1
      rw [show tag2 τ = 6 by simp [tag2, u_pFlip, ← e413, e23, ← e815, ← e59, bal_pos (τ.relabel pFlip) h1 h2]]
      exact h1

end

theorem appC_sameRootedMetricTree (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U5 hX σ
  have he' : unroot (σ'.relabel e.symm).clusters = U5 k := by
    rw [SpeciesTree.relabel_clusters, unroot_relabelFamily, ← hU.1, ← unroot_relabelFamily]
    exact he
  have hd := (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).2 h
  have hUr := (SpeciesTree.sameUnrootedMetricTree_relabel_iff σ σ' e.symm).2 hU
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e.symm]
  generalize σ.relabel e.symm = τ at he hd hUr ⊢
  generalize σ'.relabel e.symm = τ' at he' hd hUr ⊢
  have hp : pick k τ = pick k τ' := by unfold pick tag0 tag1 tag2 u; rw [hd]
  have hs1 := pick_spec τ hk he
  have hs2 := pick_spec τ' hk he'
  have hrep : (pick k τ').2 = balanced5 ∨ (pick k τ').2 = caterpillar5 ∨
      (pick k τ').2 = pseudocaterpillar5 := by unfold pick; split <;> (try split) <;> simp
  rw [hp] at hs1
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff τ τ' (pick k τ').1]
  have hdr := (SpeciesTree.unrootedDist_relabel_eq_iff τ τ' (pick k τ').1).2 hd
  have hUrr := (SpeciesTree.sameUnrootedMetricTree_relabel_iff τ τ' (pick k τ').1).2 hUr
  set H := (pick k τ').2
  generalize τ.relabel (pick k τ').1 = ρ at hs1 hdr hUrr ⊢
  generalize τ'.relabel (pick k τ').1 = ρ' at hs2 hdr hUrr ⊢
  have hu : ∀ i, u ρ i = u ρ' i := fun i => by unfold u; rw [hdr]
  have notc : ∀ D : Finset (Fin 5), Dᶜ ∉ H → 2 ≤ #D ∧ 2 ≤ #Dᶜ ∧ D ≠ univ → eVal ρ D = eVal ρ' D :=
    fun D hDH h2 => by
      have hc : Dᶜ ∉ ρ.clusters := fun m => hDH (hs1 m)
      have hc' : Dᶜ ∉ ρ'.clusters := fun m => hDH (hs2 m)
      have hmem : ∀ a : SpeciesTree (Fin 5), Dᶜ ∉ a.clusters → (D ∈ a.clusters ↔ D ∈ unroot a.clusters) :=
        fun a hac => ⟨fun m => mem_unroot.2 (Or.inl ⟨m, h2.2.2⟩), fun m => by
          rcases mem_unroot.1 m with ⟨h1, -⟩ | ⟨h1, -⟩; exacts [h1, absurd h1 hac]⟩
      have hiff : D ∈ ρ.clusters ↔ D ∈ ρ'.clusters := by rw [hmem ρ hc, hUrr.1, ← hmem ρ' hc']
      by_cases hD : D ∈ ρ.clusters
      · have hD' := hiff.1 hD
        have hl : ρ.length D = ρ'.length D := by
          rw [← ρ.unrootedLength_of_compl_notMem hD h2.2.2 hc,
            ← ρ'.unrootedLength_of_compl_notMem hD' h2.2.2 hc']
          exact hUrr.2 D ((hmem ρ hc).1 hD) h2.1 h2.2.1
        simp [eVal, hD, hD', hl]
      · simp [eVal, hD, mt hiff.2 hD]
  have hX := notc c01 (by rcases hrep with h' | h' | h' <;> rw [h'] <;> decide) (by decide)
  have p6 : ∀ {A : Finset (Fin 5)} {c : ℝ},
      c * (1 - eVal ρ A ^ 6) = c * (1 - eVal ρ' A ^ 6) → c ≠ 0 → eVal ρ A = eVal ρ' A :=
    fun heq hc => (pow_left_inj₀ (eVal_pos ρ _).le (eVal_pos ρ' _).le (by decide : 6 ≠ 0)).1
      (by linarith [mul_left_cancel₀ hc heq])
  rcases hrep with h' | h' | h'
  · rw [h'] at hs1 hs2
    obtain ⟨-, -, -, -, d1, e2⟩ := bal5_diffs ρ hs1
    obtain ⟨-, -, -, -, d1', e2'⟩ := bal5_diffs ρ' hs2
    have hxyz : eVal ρ c01 * eVal ρ c012 * eVal ρ c34 =
        eVal ρ' c01 * eVal ρ' c012 * eVal ρ' c34 := by linarith [hu 5, hu 8]
    have hp' : 0 < eVal ρ c01 * eVal ρ c012 * eVal ρ c34 := by
      positivity [eVal_pos ρ c01, eVal_pos ρ c012, eVal_pos ρ c34]
    have hY := (pow_left_inj₀ (eVal_pos ρ _).le (eVal_pos ρ' _).le (by decide : 2 ≠ 0)).1
      (mul_left_cancel₀ hp'.ne' (by rw [hu 8] at e2; rw [← hxyz] at e2'; exact e2.symm.trans e2'))
    have hZ : eVal ρ c34 = eVal ρ' c34 :=
      mul_left_cancel₀ (mul_pos (eVal_pos ρ' c01) (eVal_pos ρ' c012)).ne' (by rwa [hX, hY] at hxyz)
    exact same_of_eVal_eq hs1 hs2 hX hY hZ
  · have hY := notc c012 (by rw [h']; decide) (by decide)
    rw [h'] at hs1 hs2
    obtain ⟨e1, -⟩ := cat5_rels ρ hs1; obtain ⟨e1', -⟩ := cat5_rels ρ' hs2
    rw [hu 2, hu 3, hX, hY] at e1
    exact same_of_eVal_eq hs1 hs2 hX hY
      (p6 (e1.symm.trans e1') (by
        have : 0 < eVal ρ' c01 * eVal ρ' c012 ^ 3 := by positivity [eVal_pos ρ' c01, eVal_pos ρ' c012]
        linarith))
  · have hY := notc c34 (by rw [h']; decide) (by decide)
    rw [h'] at hs1 hs2
    obtain ⟨-, -, e1, -⟩ := pse5_diffs ρ hs1; obtain ⟨-, -, e1', -⟩ := pse5_diffs ρ' hs2
    rw [hu 5, hu 8, hX, hY] at e1
    exact same_of_eVal_eq hs1 hs2 hX hY
      (p6 (e1.symm.trans e1') (by linarith [mul_pos (eVal_pos ρ' c01) (eVal_pos ρ' c34)]))

end ADR11
