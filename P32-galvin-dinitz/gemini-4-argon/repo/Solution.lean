module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.Rev
public import Mathlib.Tactic.Tauto

@[expose] public section

open SimpleGraph Finset

namespace ListEdgeColouring

structure PEC {V : Type*} (G : SimpleGraph V) (C : Type*) where
  col : V → V → Option C
  col_symm u v : col u v = col v u
  col_adj {u v γ} : col u v = some γ → G.Adj u v
  col_proper {u v w γ} : col u v = some γ → col u w = some γ → v = w

theorem gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by
  classical
  generalize hn : {p : M × W | E p.1 p.2}.ncard = n
  induction n using Nat.strong_induction_on generalizing E with | _ n ih =>
  let T m w := E m w ∧ ∀ w', E m w' → rm m w ≤ rm m w'
  by_cases hsh : ∃ m₁ m₂ w, rw w m₁ < rw w m₂ ∧ T m₁ w ∧ T m₂ w
  · obtain ⟨m₁, m₂, w, hlt, h₁, h₂⟩ := hsh
    obtain ⟨μ, hsub, hm, hw, hst⟩ := ih _
      (hn ▸ Set.ncard_lt_ncard ⟨fun _ h => h.1, fun h => (@h (m₂, w) h₂.1).2 ⟨rfl, rfl⟩⟩
        (Set.toFinite _))
      (fun m v => E m v ∧ ¬ (m = m₂ ∧ v = w)) rfl
    refine ⟨μ, fun m v h => (hsub m v h).1, hm, hw, fun m v hE hnot => ?_⟩
    by_cases hrem : m = m₂ ∧ v = w
    · obtain ⟨rfl, rfl⟩ := hrem
      refine Or.inr (if hμ₁ : μ m₁ v then ⟨m₁, hμ₁, hlt⟩ else ?_)
      rcases hst m₁ v ⟨h₁.1, fun h => hlt.ne (by rw [h.1])⟩ hμ₁ with ⟨w', hw', hr⟩ | ⟨m', hm', hr⟩
      · have := h₁.2 w' (hsub _ _ hw').1; omega
      · exact ⟨m', hm', hr.trans hlt⟩
    · exact hst m v ⟨hE, hrem⟩ hnot
  · refine ⟨T, fun _ _ h => h.1, fun m _ _ h h' => hrm m (le_antisymm (h.2 _ h'.1) (h'.2 _ h.1)),
      fun m m' w h h' => hrw w (le_antisymm (not_lt.1 fun l => hsh ⟨m', m, w, l, h', h⟩)
        (not_lt.1 fun l => hsh ⟨m, m', w, l, h, h'⟩)), fun m w hE hnot => ?_⟩
    have hex : ∃ k w', E m w' ∧ rm m w' = k := ⟨_, w, hE, rfl⟩
    obtain ⟨w', hw', hk⟩ := Nat.find_spec hex
    have hwT : T m w' := ⟨hw', fun v hv => hk.le.trans (Nat.find_min' hex ⟨v, hv, rfl⟩)⟩
    exact Or.inl ⟨w', hwT, lt_of_le_of_ne (hwT.2 w hE) fun h => hnot (hrm m h ▸ hwT)⟩

theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  classical
  obtain ⟨s⟩ := hG
  have p : PEC G (Fin G.maxDegree) := ⟨fun _ _ => none, by simp, by simp, by simp⟩
  generalize hn : {q : V × V | p.col q.1 q.2 = none}.ncard = n
  induction n using Nat.strong_induction_on generalizing p with | _ n ih =>
  by_cases htot : ∀ u v, G.Adj u v → p.col u v ≠ none
  · have hends (e : G.edgeSet) : ∃ a b, e.1 = s(a, b) ∧ s a = 0 ∧ G.Adj a b := by
      obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with | _ x y =>
      exact if h : s x = 0 then ⟨x, y, rfl, h, he⟩ else
        ⟨y, x, Sym2.eq_swap, by have : s x ≠ s y := s.valid he; omega, he.symm⟩
    choose endA endB hedge hcolA hadj using hends
    have eq_ends {e f} (hA : endA e = endA f) (hB : endB e = endB f) : e = f :=
      Subtype.ext (by simp [hedge, hA, hB])
    choose φ hφ using fun e => Option.ne_none_iff_exists'.mp (htot _ _ (hadj e))
    let D e f := (endA f = endA e ∧ φ f < φ e) ∨ (endB f = endB e ∧ φ e < φ f)
    let rank (g : _ → Fin G.maxDegree) u v : ℕ :=
      match p.col u v with | some γ => g γ | none => G.maxDegree + Fintype.equivFin V v
    have hrank {g} (hg : Function.Injective g) (u) :
        Function.Injective (rank g u) := fun v v' hvv => by
      cases hv : p.col u v <;> cases hv' : p.col u v' <;> simp only [rank, hv, hv'] at hvv <;>
        first | exact (Fintype.equivFin V).injective (Fin.ext (by omega)) |
          exact p.col_proper hv (hg (Fin.ext hvv) ▸ hv')
    suffices ∀ U (L : G.edgeSet → Finset Color),
        (∀ x ∈ U, (filter (D x) U).card < (L x).card) →
        ∃ c : G.edgeSet → Color,
          ∀ x ∈ U, c x ∈ L x ∧ ∀ y ∈ U, G.lineGraph.Adj x y → c x ≠ c y by
      obtain ⟨c, hc⟩ := this univ lists fun e _ =>
        ((card_le_card_of_injOn φ
          (fun f hf => mem_erase.2 ⟨by rcases (mem_filter.1 hf).2 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega,
            mem_univ _⟩)
          fun f hf f' hf' h => by
            rcases (mem_filter.1 hf).2 with ⟨hA, hlt⟩ | ⟨hB, hlt⟩ <;>
              rcases (mem_filter.1 hf').2 with ⟨hA', hlt'⟩ | ⟨hB', hlt'⟩ <;> first | omega | skip
            · exact eq_ends (hA.trans hA'.symm) (p.col_proper (hA ▸ hφ f) (hA' ▸ h ▸ hφ f'))
            · exact eq_ends (p.col_proper (hB ▸ p.col_symm _ _ ▸ hφ f)
                (hB' ▸ h ▸ p.col_symm _ _ ▸ hφ f')) (hB.trans hB'.symm)).trans_lt
          (card_fin G.maxDegree ▸ card_erase_lt_of_mem (mem_univ (φ e)))).trans_le (hLists e)
      simp only [mem_univ, forall_const] at hc
      exact ⟨⟨c, fun h => (hc _).2 _ h⟩, fun x => (hc x).1⟩
    intro U
    induction U using Finset.strongInduction with | H U ihU =>
    intro L hL
    rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · exact ⟨fun x => (card_pos.1 ((φ x).pos.trans_le (hLists x))).choose, by simp⟩
    obtain ⟨κ, hκ⟩ := card_pos.1 (Nat.zero_lt_of_lt (hL x₀ hx₀))
    obtain ⟨μ, hsub, hm, hw, hst⟩ := gale_shapley
      (fun m w => ∃ e ∈ U, κ ∈ L e ∧ endA e = m ∧ endB e = w)
      (rank id) (rank Fin.rev) (hrank Function.injective_id) (hrank Fin.rev_injective)
    let K := U.filter fun e => κ ∈ L e ∧ μ (endA e) (endB e)
    have hKabs {x} (hxU : x ∈ U) (hκx : κ ∈ L x) (hxK : x ∉ K) : ∃ y ∈ K, D x y := by
      rcases hst _ _ ⟨x, hxU, hκx, rfl, rfl⟩ (fun h => hxK (mem_filter.2 ⟨hxU, hκx, h⟩)) with
        ⟨w', hμ, hlt⟩ | ⟨m', hμ, hlt⟩
      · obtain ⟨f, hfU, hfL, hfA, rfl⟩ := hsub _ _ hμ
        exact ⟨f, mem_filter.2 ⟨hfU, hfL, hfA ▸ hμ⟩,
          Or.inl ⟨hfA, by simpa [rank, hfA ▸ hφ f, hφ] using hlt⟩⟩
      · obtain ⟨f, hfU, hfL, rfl, hfB⟩ := hsub _ _ hμ
        exact ⟨f, mem_filter.2 ⟨hfU, hfL, hfB ▸ hμ⟩, Or.inr ⟨hfB, by
          simp [rank, ← p.col_symm (endA _), hfB ▸ hφ f, hφ] at hlt; omega⟩⟩
    obtain ⟨c', hc'⟩ := ihU (U \ K) (sdiff_ssubset (filter_subset _ _)
      (nonempty_iff_ne_empty.2 fun h => by simpa [h] using hKabs hx₀ hκ))
      (fun x => (L x).erase κ) fun x hx => by
        rw [mem_sdiff] at hx
        have := hL x hx.1
        by_cases hκx : κ ∈ L x
        · obtain ⟨y, hy, hD⟩ := hKabs hx.1 hκx hx.2
          exact (card_lt_card ⟨filter_subset_filter _ sdiff_subset,
            fun h => by simpa [K, hD, mem_filter.1 hy] using @h y⟩).trans_le
            (by rw [card_erase_of_mem hκx]; omega)
        · rw [erase_eq_of_notMem hκx]
          exact (card_le_card (filter_subset_filter _ sdiff_subset)).trans_lt this
    simp only [mem_sdiff, mem_erase] at hc'
    refine ⟨fun x => if x ∈ K then κ else c' x, fun x hx => ?_⟩
    dsimp only; split_ifs with hxK
    · refine ⟨(mem_filter.1 hxK).2.1, fun y hy hxy => ?_⟩
      split_ifs with hyK
      · intro _
        obtain ⟨hne, v, hvx, hvy⟩ := hxy
        simp [hedge, K] at hxK hyK hvx hvy
        rcases hvx with rfl | rfl <;> rcases hvy with h | h
        · exact hne (eq_ends h (hm _ _ _ (h ▸ hxK.2.2) hyK.2.2))
        · exact s.valid (hadj y) (by simp [← h, hcolA])
        · exact s.valid (hadj x) (by simp [h, hcolA])
        · exact hne (eq_ends (hw _ _ _ (h ▸ hxK.2.2) hyK.2.2) h)
      · exact (hc' y ⟨hy, hyK⟩).1.1.symm
    · have hx' := hc' x ⟨hx, hxK⟩
      refine ⟨hx'.1.2, fun y hy hxy => ?_⟩
      split_ifs with hyK
      · exact hx'.1.1
      · exact hx'.2 y ⟨hy, hyK⟩ hxy
  · push Not at htot
    have hfree {x y} (hadj : G.Adj x y) (hnone : p.col x y = none) :
        ∃ γ, ∀ u, p.col x u ≠ some γ := by
      by_contra! hcon
      choose g hg using hcon
      exact ((card_fin G.maxDegree ▸ card_le_card_of_injOn g
        (fun γ _ => mem_erase.2 ⟨by rintro rfl; simp [hg] at hnone,
          (G.mem_neighborFinset _ _).2 (p.col_adj (hg γ))⟩)
        (fun γ₁ _ γ₂ _ h => by simpa [← h, hg] using hg γ₂)).trans_lt
        (card_erase_lt_of_mem ((G.mem_neighborFinset _ _).2 hadj))).not_ge
        (G.card_neighborFinset_eq_degree x ▸ G.degree_le_maxDegree x)
    obtain ⟨x, y, hadj, hnone⟩ := htot
    obtain ⟨a, ha⟩ := hfree hadj hnone
    obtain ⟨b, hb⟩ := hfree hadj.symm (p.col_symm x y ▸ hnone)
    let R u v := p.col v u = some (if s v = s y then b else a)
    have hR {u v} (h : p.col v u = some (if s v = s y then b else a)) :
        Relation.ReflTransGen R y u ↔ Relation.ReflTransGen R y v :=
      ⟨(·.tail h), fun
        | .refl => absurd (by simpa using h) (hb u)
        | .tail hw hwv => p.col_proper h hwv ▸ hw⟩
    have hxy : ¬ Relation.ReflTransGen R y x := fun
      | .refl => s.valid hadj rfl
      | .tail _ hwx => ha _ (by simpa [R, s.valid hadj] using hwx)
    let c1 u v := (p.col u v).map
      ⇑(if Relation.ReflTransGen R y u then Equiv.swap a b else 1)
    refine ih _ ?_
      ⟨fun u v => if s(u, v) = s(x, y) then some a else c1 u v, fun u v => by
        rw [Sym2.eq_swap]; congr 1; dsimp [c1]; rw [p.col_symm u v]
        cases h : p.col v u
        · rfl
        have := s.valid (p.col_adj h); have h1 := @hR u v; have h2 := @hR v u
        rw [p.col_symm u v] at h2
        split_ifs at h1 h2 ⊢ <;> first | rfl | omega | simp_all [Equiv.swap_apply_of_ne_of_ne],
      fun h => by
        split_ifs at h with hc
        · rw [← G.mem_edgeSet, hc]; exact hadj
        · exact p.col_adj (Option.map_eq_some_iff.1 h).choose_spec.1,
      fun {u v w δ} h1 h2 => by
        simp only [Sym2.eq_iff] at h1 h2
        split_ifs at h1 h2 <;> first
          | (obtain ⟨_, hc1, rfl⟩ := Option.map_eq_some_iff.1 h1
             exact p.col_proper hc1 (Option.map_injective (Equiv.injective _) h2))
          | obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := ‹_ ∨ _› <;>
              simp_all [c1, Relation.ReflTransGen.refl, ← Equiv.eq_symm_apply,
                hadj.ne, hadj.symm.ne]⟩ rfl
    exact hn ▸ Set.ncard_lt_ncard
      ⟨fun q hq => by dsimp at hq; split_ifs at hq; exact Option.map_eq_none_iff.1 hq,
       fun h => by simpa using @h (x, y) hnone⟩ (Set.toFinite _)

theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  classical
  let G := completeBipartiteGraph (Fin n) (Fin n)
  let L := Sym2.lift ⟨fun | Sum.inl i, Sum.inr j | Sum.inr j, Sum.inl i => lists i j | _, _ => ∅,
    by intro a b; cases a <;> cases b <;> rfl⟩
  obtain ⟨col, hcol⟩ := galvin G
    ⟨⟨Sum.elim (fun _ => 0) (fun _ => 1), fun {a b} h => by cases a <;> cases b <;> simp_all [G]⟩⟩
    (L ·.1) fun ⟨e, he⟩ => (G.maxDegree_le_of_forall_degree_le n fun v =>
      G.card_neighborFinset_eq_degree v ▸
        (card_le_card_of_injOn (Sum.elim id id) (fun _ _ => mem_univ _) fun a ha b hb h => by
          cases v <;> cases a <;> cases b <;> simp_all [G]).trans (card_fin n).le).trans (by
      induction e using Sym2.ind with | _ a b =>
      cases a <;> cases b <;> simp [G, L, hLists] at he ⊢)
  let edge i j : G.edgeSet := ⟨s(.inl i, .inr j), by simp [G]⟩
  refine ⟨fun i j => col (edge i j), fun i j => hcol _,
    fun i j j' hjj => col.valid ⟨by simp [edge, hjj], .inl i, by simp [edge]⟩,
    fun i i' j hii => col.valid ⟨by simp [edge, hii], .inr j, by simp [edge]⟩⟩

end ListEdgeColouring
