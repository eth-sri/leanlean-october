/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinLib.GaleShapley
public import GalvinLib.Konig

/-!
# List colourings from kernels, Galvin's theorem and the Dinitz problem
-/

@[expose] public section

namespace Galvin

open SimpleGraph Finset

/-! ### Kernels -/

/-- Every finite set of vertices has a kernel for the digraph `D`. -/
def HK {α : Type*} (G : SimpleGraph α) (D : α → α → Prop) : Prop :=
  ∀ S : Finset α, ∃ K ⊆ S, (∀ x ∈ K, ∀ y ∈ K, ¬ G.Adj x y) ∧
    ∀ x ∈ S, x ∉ K → ∃ y ∈ K, D x y

theorem LC_aux {α Color : Type*} [Nonempty Color] (G : SimpleGraph α) (D : α → α → Prop)
    [DecidableRel D] (hK : HK G D) :
    ∀ (n : ℕ) (U : Finset α), U.card = n → ∀ L : α → Finset Color,
      (∀ x ∈ U, (U.filter (D x ·)).card < (L x).card) →
      ∃ c : α → Color, (∀ x ∈ U, c x ∈ L x) ∧ ∀ x ∈ U, ∀ y ∈ U, G.Adj x y → c x ≠ c y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn L hL
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨fun _ => Classical.arbitrary _, by simp, by simp⟩
  obtain ⟨κ, hκ⟩ := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hL x₀ hx₀))
  obtain ⟨K, hKS, hKi, hKa⟩ := hK (U.filter (κ ∈ L ·))
  have hKU : K ⊆ U := hKS.trans (filter_subset _ _)
  have hKne : K.Nonempty := by
    rcases K.eq_empty_or_nonempty with h | h
    · obtain ⟨y, hy, -⟩ := hKa x₀ (mem_filter.2 ⟨hx₀, hκ⟩) (by simp [h])
      simp [h] at hy
    · exact h
  have hlt : (U \ K).card < n := by
    rw [← hn]
    exact card_lt_card (sdiff_ssubset hKU hKne)
  obtain ⟨c, hc, hcp⟩ := ih _ hlt (U \ K) rfl (fun x => (L x).erase κ) (by
    intro x hx
    rw [mem_sdiff] at hx
    by_cases hκx : κ ∈ L x
    · rw [card_erase_of_mem hκx]
      obtain ⟨y, hy, hD⟩ := hKa x (mem_filter.2 ⟨hx.1, hκx⟩) hx.2
      have hins : insert y ((U \ K).filter (D x ·)) ⊆ U.filter (D x ·) := by
        intro z hz
        rcases mem_insert.1 hz with rfl | hz
        · exact mem_filter.2 ⟨hKU hy, hD⟩
        · rw [mem_filter] at hz ⊢
          exact ⟨(mem_sdiff.1 hz.1).1, hz.2⟩
      have h1 := card_le_card hins
      rw [card_insert_of_notMem (by simp [hy])] at h1
      have h2 := hL x hx.1
      omega
    · rw [erase_eq_of_notMem hκx]
      exact lt_of_le_of_lt (card_le_card (filter_subset_filter _ sdiff_subset)) (hL x hx.1))
  refine ⟨fun x => if x ∈ K then κ else c x, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · by_cases hxK : x ∈ K
    · simp only [hxK, ite_true]
      exact (mem_filter.1 (hKS hxK)).2
    · simp only [hxK, ite_false]
      exact mem_of_mem_erase (hc x (by simp [hx, hxK]))
  · by_cases hxK : x ∈ K <;> by_cases hyK : y ∈ K <;> simp only [hxK, hyK, ite_true, ite_false]
    · exact (hKi x hxK y hyK hxy).elim
    · intro h
      exact (mem_erase.1 (hc y (by simp [hy, hyK]))).1 h.symm
    · intro h
      exact (mem_erase.1 (hc x (by simp [hx, hxK]))).1 h
    · exact hcp x (by simp [hx, hxK]) y (by simp [hy, hyK]) hxy

/-- **Kernel lemma.** If every finite set of vertices has a kernel and every list is longer than
the out-degree of its vertex, there is a proper list colouring. -/
theorem LC {α Color : Type*} [Fintype α] (G : SimpleGraph α) (D : α → α → Prop)
    [DecidableRel D] (hK : HK G D) (L : α → Finset Color)
    (hL : ∀ x, (univ.filter (D x ·)).card < (L x).card) :
    ∃ c : G.Coloring Color, ∀ x, c x ∈ L x := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨Coloring.mk (fun x => (hα.false x).elim) (fun {x} => (hα.false x).elim),
      fun x => (hα.false x).elim⟩
  have : Nonempty Color := by
    obtain ⟨x⟩ := hα
    obtain ⟨k, -⟩ := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hL x))
    exact ⟨k⟩
  obtain ⟨c, hc, hp⟩ := LC_aux G D hK univ.card univ rfl L (fun x _ => hL x)
  exact ⟨Coloring.mk c (fun {x y} h => hp x (mem_univ x) y (mem_univ y) h),
    fun x => hc x (mem_univ x)⟩

/-! ### Galvin's orientation of the line graph of a bipartite graph -/

variable {V : Type*} {G : SimpleGraph V} {Δ : ℕ}

section Ends
variable {c : G.Coloring (Fin 2)}

theorem ends_ex (c : G.Coloring (Fin 2)) (e : G.edgeSet) : ∃ a b : V, (e : Sym2 V) = s(a, b) ∧ c a = 0 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ x y =>
    have hne : c x ≠ c y := c.valid he
    by_cases hx : c x = 0
    · exact ⟨x, y, rfl, hx⟩
    · refine ⟨y, x, Sym2.eq_swap, ?_⟩
      revert hne hx
      generalize c x = i
      generalize c y = j
      revert i j
      decide

/-- The endpoint of an edge on the side of colour `0`. -/
noncomputable def eA (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V := (ends_ex c e).choose

/-- The endpoint of an edge on the side of colour `1`. -/
noncomputable def eB (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V := (ends_ex c e).choose_spec.choose

theorem ends_eq (c : G.Coloring (Fin 2)) (e : G.edgeSet) : (e : Sym2 V) = s(eA c e, eB c e) :=
  (ends_ex c e).choose_spec.choose_spec.1

theorem eA0 (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (eA c e) = 0 :=
  (ends_ex c e).choose_spec.choose_spec.2

theorem adjE (c : G.Coloring (Fin 2)) (e : G.edgeSet) : G.Adj (eA c e) (eB c e) := by
  have := e.2
  rwa [ends_eq c] at this

theorem eB1 (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (eB c e) = 1 := by
  have h := c.valid (adjE c e)
  rw [eA0] at h
  revert h
  generalize c (eB c e) = i
  revert i
  decide

theorem ends_inj (c : G.Coloring (Fin 2)) {e f : G.edgeSet} (hA : eA c e = eA c f)
    (hB : eB c e = eB c f) : e = f := by
  apply Subtype.ext
  rw [ends_eq c, ends_eq c, hA, hB]

theorem memE (c : G.Coloring (Fin 2)) (e : G.edgeSet) (v : V) :
    v ∈ (e : Sym2 V) ↔ v = eA c e ∨ v = eB c e := by
  rw [ends_eq c, Sym2.mem_iff]

theorem adjE_iff (c : G.Coloring (Fin 2)) {e f : G.edgeSet} :
    G.lineGraph.Adj e f ↔ e ≠ f ∧ (eA c e = eA c f ∨ eB c e = eB c f) := by
  rw [lineGraph_adj_iff_exists]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨v, hv, hw⟩
    rw [ends_eq c, Sym2.mem_iff] at hv
    rw [ends_eq c, Sym2.mem_iff] at hw
    rcases hv with rfl | rfl <;> rcases hw with h | h
    · exact Or.inl h
    · grind [eA0, eB1]
    · grind [eA0, eB1]
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨eA c e, (memE c e _).2 (Or.inl rfl), (memE c f _).2 (Or.inl h)⟩
    · exact ⟨eB c e, (memE c e _).2 (Or.inr rfl), (memE c f _).2 (Or.inr h)⟩

end Ends

section
variable {c : G.Coloring (Fin 2)} {φ : G.lineGraph.Coloring (Fin Δ)}

theorem ends_of_col (c : G.Coloring (Fin 2)) (φ : G.lineGraph.Coloring (Fin Δ))
    {e f : G.edgeSet} (h : φ e = φ f) (h2 : eA c e = eA c f ∨ eB c e = eB c f) : e = f := by
  by_contra hne
  exact φ.valid ((adjE_iff c).2 ⟨hne, h2⟩) h

/-- Galvin's orientation of the line graph. -/
def arc (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (e f : G.edgeSet) : Prop :=
  (eA c e = eA c f ∧ φ f < φ e) ∨ (eB c e = eB c f ∧ φ e < φ f)

/-- Every out-degree of Galvin's orientation is less than `Δ`. -/
theorem cardA [Fintype G.edgeSet] (e : G.edgeSet) [DecidablePred (arc c φ e)] :
    (univ.filter (arc c φ e)).card < Δ := by
  classical
  have hinj : Set.InjOn (fun f : G.edgeSet => φ f) ↑(univ.filter (arc c φ e)) := by
    intro f hf g hg heq
    obtain ⟨-, hf⟩ := mem_filter.1 hf
    obtain ⟨-, hg⟩ := mem_filter.1 hg
    change φ f = φ g at heq
    unfold arc at hf hg
    rcases hf with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hg with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact ends_of_col c φ heq (Or.inl (h1.symm.trans h3))
    · rw [heq] at h2; omega
    · rw [heq] at h2; omega
    · exact ends_of_col c φ heq (Or.inr (h1.symm.trans h3))
  have h : (univ.filter (arc c φ e)).card ≤ (univ.erase (φ e)).card := by
    refine card_le_card_of_injOn (fun f : G.edgeSet => φ f) ?_ hinj
    intro f hf
    obtain ⟨-, hf⟩ := mem_filter.1 hf
    rw [mem_coe, mem_erase]
    refine ⟨?_, mem_univ _⟩
    unfold arc at hf
    exact hf.elim (fun h => h.2.ne) (fun h => h.2.ne')
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h
  have := (φ e).isLt
  omega

/-- Rank of `w` for `m`: the colour of the edge `mw` (smaller colours preferred). -/
noncomputable def rA (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (m w : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, eA c e = m ∧ eB c e = w then φ h.choose else Δ

/-- Rank of `m` for `w`: `Δ` minus the colour of the edge `mw`. -/
noncomputable def rB (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (w m : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, eA c e = m ∧ eB c e = w then Δ - φ h.choose else Δ + 1

theorem rA_ends (e : G.edgeSet) : rA c φ (eA c e) (eB c e) = φ e := by
  have h : ∃ f : G.edgeSet, eA c f = eA c e ∧ eB c f = eB c e := ⟨e, rfl, rfl⟩
  simp only [rA]
  rw [dif_pos h, ends_inj c h.choose_spec.1 h.choose_spec.2]

theorem rB_ends (e : G.edgeSet) : rB c φ (eB c e) (eA c e) = Δ - φ e := by
  have h : ∃ f : G.edgeSet, eA c f = eA c e ∧ eB c f = eB c e := ⟨e, rfl, rfl⟩
  simp only [rB]
  rw [dif_pos h, ends_inj c h.choose_spec.1 h.choose_spec.2]

theorem rA_inj (m : V) :
    ∀ w w', (∃ e : G.edgeSet, eA c e = m ∧ eB c e = w) →
      (∃ e : G.edgeSet, eA c e = m ∧ eB c e = w') → rA c φ m w = rA c φ m w' → w = w' := by
  intro w w' h1 h2 h
  simp only [rA] at h
  rw [dif_pos h1, dif_pos h2] at h
  rw [← h1.choose_spec.2, ← h2.choose_spec.2,
    ends_of_col c φ (Fin.ext h) (Or.inl (h1.choose_spec.1.trans h2.choose_spec.1.symm))]

theorem rB_inj (w : V) :
    ∀ m m', (∃ e : G.edgeSet, eA c e = m ∧ eB c e = w) →
      (∃ e : G.edgeSet, eA c e = m' ∧ eB c e = w) → rB c φ w m = rB c φ w m' → m = m' := by
  intro m m' h1 h2 h
  simp only [rB] at h
  rw [dif_pos h1, dif_pos h2] at h
  have e1 := (φ h1.choose).isLt
  have e2 := (φ h2.choose).isLt
  rw [← h1.choose_spec.1, ← h2.choose_spec.1,
    ends_of_col c φ (Fin.ext (by omega)) (Or.inr (h1.choose_spec.2.trans h2.choose_spec.2.symm))]

/-- Every set of edges has a kernel for Galvin's orientation: a stable matching. -/
theorem harc [Finite V] : HK G.lineGraph (arc c φ) := by
  classical
  intro S
  let E : V → V → Prop := fun m w => ∃ e ∈ S, eA c e = m ∧ eB c e = w
  obtain ⟨μ, hsub, hm, hw, hst⟩ := exists_isStable E (rA c φ) (rB c φ)
    ⟨fun m w w' h1 h2 => rA_inj m w w' ⟨h1.choose, h1.choose_spec.2⟩ ⟨h2.choose, h2.choose_spec.2⟩,
     fun w m m' h1 h2 => rB_inj w m m' ⟨h1.choose, h1.choose_spec.2⟩ ⟨h2.choose, h2.choose_spec.2⟩⟩
  refine ⟨S.filter (fun e => μ (eA c e) (eB c e)), filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [mem_filter] at hx hy
    grind [adjE_iff, ends_inj]
  · intro x hxS hxK
    simp only [mem_filter, hxS, true_and] at hxK
    rcases hst _ _ ⟨x, hxS, rfl, rfl⟩ hxK with ⟨w', hμ, hlt⟩ | ⟨m', hμ, hlt⟩
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      subst hfB
      rw [← hfA] at hμ hlt
      exact ⟨f, mem_filter.2 ⟨hfS, hμ⟩, Or.inl ⟨hfA.symm, by rwa [rA_ends, hfA, rA_ends] at hlt⟩⟩
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      subst hfA
      rw [← hfB] at hμ hlt
      refine ⟨f, mem_filter.2 ⟨hfS, hμ⟩, Or.inr ⟨hfB.symm, ?_⟩⟩
      rw [rB_ends, hfB, rB_ends] at hlt
      simp only [Fin.lt_def] at hlt ⊢
      omega

end

/-! ### Galvin's theorem -/

theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  classical
  obtain ⟨c⟩ := hG
  obtain ⟨φ⟩ := lgcol G ⟨c⟩
  exact LC G.lineGraph (arc c φ) harc lists
    fun e => lt_of_lt_of_le (cardA e) (hLists e)

/-! ### The Dinitz problem -/

theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  classical
  let G := completeBipartiteGraph (Fin n) (Fin n)
  have hb : G.IsBipartiteWith (univ.image (Sum.inl : Fin n → Fin n ⊕ Fin n))
      (univ.image (Sum.inr : Fin n → Fin n ⊕ Fin n)) := by
    simpa using IsBipartiteWith.completeBipartiteGraph (Fin n) (Fin n)
  have hdeg : G.maxDegree ≤ n := by
    refine G.maxDegree_le_of_forall_degree_le n fun v => ?_
    rcases v with i | i
    · exact (isBipartiteWith_degree_le hb (by simp)).trans (card_image_le.trans (by simp))
    · exact (isBipartiteWith_degree_le' hb (by simp)).trans (card_image_le.trans (by simp))
  let L : G.edgeSet → Finset Symbol := fun e => Sym2.lift ⟨fun a b => match a, b with
    | Sum.inl i, Sum.inr j => lists i j
    | Sum.inr j, Sum.inl i => lists i j
    | _, _ => ∅, by rintro (i | i) (j | j) <;> rfl⟩ e
  have hL : ∀ e, G.maxDegree ≤ (L e).card := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      rcases a with i | i <;> rcases b with j | j
      · simp [G, completeBipartiteGraph_adj] at he
      · exact hdeg.trans (hLists i j)
      · exact hdeg.trans (hLists j i)
      · simp [G, completeBipartiteGraph_adj] at he
  obtain ⟨col, hcol⟩ := galvin G (IsBipartite.completeBipartiteGraph _ _) L hL
  have hadj : ∀ i j, G.Adj (Sum.inl i) (Sum.inr j) := fun i j => by simp [G]
  let edge : Fin n → Fin n → G.edgeSet := fun i j => ⟨s(Sum.inl i, Sum.inr j), hadj i j⟩
  refine ⟨fun i j => col (edge i j), fun i j => ?_, fun i j j' hjj => ?_, fun i i' j hii => ?_⟩
  · simpa [L, edge, Sym2.lift_mk] using hcol (edge i j)
  · refine col.valid ?_
    rw [lineGraph_adj_iff_exists]
    refine ⟨fun h => hjj ?_, Sum.inl i, by simp [edge], by simp [edge]⟩
    simpa [edge] using congrArg Subtype.val h
  · refine col.valid ?_
    rw [lineGraph_adj_iff_exists]
    refine ⟨fun h => hii ?_, Sum.inr j, by simp [edge], by simp [edge]⟩
    simpa [edge] using congrArg Subtype.val h

end Galvin
