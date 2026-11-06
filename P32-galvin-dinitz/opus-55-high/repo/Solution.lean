module

public import Mathlib

@[expose] public section

open Finset SimpleGraph

namespace ListEdgeColouring


theorem gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by
  induction E using WellFoundedLT.induction
  next E ih =>
  let T m := MinimalFor (E m) $ rm m
  by_cases h : ∃ m₁ m₂ w, T m₁ w ∧ T m₂ w ∧ rw w m₁ < rw w m₂
  · have := ih (fun m v => E m v ∧ (m = h.choose_spec.choose → v ≠ h.choose_spec.choose_spec.choose))
      $ by grind [lt_iff_le_not_ge, Pi.le_def, le_Prop_eq, MinimalFor]
    exact ⟨_, by grind, this.choose_spec.2.1, this.choose_spec.2.2.1, fun m v => by by_cases m = h.choose_spec.choose ∧ v = h.choose_spec.choose_spec.choose <;> grind [this.choose_spec.2.2.2 h.choose h.choose_spec.choose_spec.choose ⟨h.choose_spec.choose_spec.choose_spec.1.1, by grind⟩, MinimalFor]⟩
  exact ⟨T, by grind [→ fun m v hE => exists_minimalFor_of_wellFoundedLT (E m) (rm m) ⟨v, hE⟩, MinimalFor]⟩


set_option maxHeartbeats 0 in
theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  classical
  have konig (S : Finset _) : ↑S ⊆ G.edgeSet → ∃ φ : Sym2 V → ℕ, ∀ u v w, s(u, v) ∈ S → s(u, w) ∈ S →
      φ s(u, v) = φ s(u, w) → φ s(u, v) < G.maxDegree ∧ v = w := by
    refine S.induction_on (by simp) fun e S he ih hS => ?_
    have hφ := ih $ by grind
    have {u v} : s(u, v) ∈ S → G.Adj u v := (hS $ mem_insert_of_mem ·)
    have free {x y} : s(x, y) ∉ S → G.Adj x y →
        ∃ a < G.maxDegree, ∀ v, s(x, v) ∈ S → hφ.choose s(x, v) ≠ a := by
      by_contra!
      grind [card_le_card (s := range G.maxDegree) (t := ((G.neighborFinset x).erase y).image (hφ.choose s(x, ·))) $ by grind [mem_neighborFinset], mem_neighborFinset, card_neighborFinset_eq_degree, G.degree_le_maxDegree x]
    obtain ⟨x, y⟩ := e
    have : G.Adj x y := hS $ mem_insert_self ..
    obtain ⟨a⟩ := free he this
    obtain ⟨b⟩ := free (Sym2.eq_swap ▸ he) this.symm
    let H := fromEdgeSet {e ∈ S | hφ.choose e = a ∨ hφ.choose e = b}
    have hH (u v) : H.Adj u v ↔ _ := fromEdgeSet_adj _
    have par {u z} (p : H.Walk u z) : y = z → p.IsPath → u ≠ y → (hφ.choose s(u, p.snd) = a ↔ hG.some u ≠ hG.some y) := by
      induction p
      · grind
      next w z h p _ => by_cases w = y <;> grind [Walk.snd_cons, Walk.cons_isPath_iff, Walk.adj_snd, Walk.getVert_mem_support, Coloring.valid]
    have : ¬ H.Reachable y x := by
      intro h
      grind [Walk.adj_snd, par _ rfl h.some.reverse.toPath.2, Coloring.valid]
    let ψ e := if e = s(x, y) then a else if ∃ v ∈ e, H.Reachable y v then Equiv.swap a b $ hφ.choose e else hφ.choose e
    have : ∀ u v, s(u, v) ∈ S →
        ψ s(u, v) = if H.Reachable y u then Equiv.swap a b $ hφ.choose s(u, v) else hφ.choose s(u, v) := by
      simp [ψ]
      grind [Sym2.eq_swap, Reachable.trans, Adj.reachable]
    exact ⟨ψ, by simp only [Equiv.swap_apply_def] at *; grind [Sym2.eq_iff, Reachable.refl]⟩
  have hι := Countable.exists_injective_nat V
  obtain ⟨φ⟩ := konig G.edgeFinset $ by simp
  simp at *
  let D (e f : G.edgeSet) := ∃ v ∈ e.1, v ∈ f.1 ∧ if hG.some v = 0 then φ f < φ e else φ e < φ f
  have : ∀ f : G.edgeSet, φ f < G.maxDegree := by
    rintro ⟨⟨⟩⟩
    grind [mem_edgeSet]
  have hdeg e : #(univ.filter $ D e) < #(lists e) := by
    grind [card_le_card_of_injOn (s := univ.filter $ D e) (φ ·) (t := (range G.maxDegree).erase $ φ e) (by intro; grind) $ by grind [Set.InjOn, mem_edgeSet, Sym2.mem_iff_exists, Coloring.valid]]
  have hK (S : Finset G.edgeSet) : ∃ K ⊆ S, (∀ x ∈ K, ∀ y ∈ K, ¬ G.lineGraph.Adj x y) ∧
      ∀ x ∈ S, x ∉ K → ∃ y ∈ K, D x y := by
    let E m w := hG.some m = 0 ∧ ∃ e ∈ S, e.1 = s(m, w)
    have hμ := gale_shapley E (fun m w => if G.Adj m w then φ s(m, w) else G.maxDegree + hι.choose w)
      (fun w m => if G.Adj w m then G.maxDegree - φ s(w, m) else G.maxDegree + 1 + hι.choose m)
      (by grind [Function.Injective]) $ by grind [Function.Injective]
    refine ⟨S.filter fun e => ∃ m w, hμ.choose m w ∧ e.1 = s(m, w), filter_subset .., ?_, ?_⟩
    · grind [lineGraph_adj_iff_exists, mem_edgeSet, Coloring.valid]
    · rintro ⟨e, he⟩ hS hK
      obtain ⟨m, w, h⟩ : ∃ m w, e = s(m, w) ∧ hG.some m = 0 := by
        cases e
        grind [Sym2.eq_swap, hG.some.valid he]
      rcases hμ.choose_spec.2.2.2 m w (by grind) $ by grind with
        h | h <;> obtain ⟨-, f, _⟩ := hμ.choose_spec.1 _ _ h.choose_spec.1 <;> grind [mem_edgeSet, Coloring.valid]
  have kernel (U : Finset G.edgeSet) : ∀ L : G.edgeSet → Finset Color, (∀ x ∈ U, #(U.filter $ D x) < #(L x)) →
      ∃ c : G.edgeSet → Color, ∀ x ∈ U, c x ∈ L x ∧ ∀ y ∈ U, G.lineGraph.Adj x y → c x ≠ c y := by
    refine U.strongInductionOn fun U ih L hL => ?_
    rcases U.eq_empty_or_nonempty with rfl | h
    · exact ⟨fun e => (card_pos.1 (hdeg e).pos).choose, by simp⟩
    have hκ := card_pos.1 (hL _ h.choose_spec).pos
    have hK' := hK $ U.filter (hκ.choose ∈ L ·)
    have := ih (U \ hK'.choose) (by grind) (L · |>.erase hκ.choose)
      fun x hx => by
        by_cases hκ.choose ∈ L x
        · have := hK'.choose_spec.2.2 x (by simp_all) $ by simp_all
          grind [card_le_card (s := (U \ hK'.choose).filter $ D x) (t := (U.filter (D x)).erase this.choose) $ by grind]
        · simp [*]
          exact (card_le_card $ filter_subset_filter _ sdiff_subset).trans_lt $ by grind
    exact ⟨fun x => if x ∈ hK'.choose then hκ.choose else this.choose x, by grind⟩
  obtain ⟨c⟩ := kernel univ lists $ by grind
  exact ⟨⟨c, by simp_all⟩, by simp_all⟩

theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  classical
  have := galvin _ (IsBipartite.completeBipartiteGraph ..)
    (fun e => lists.uncurry (edgeSet_completeBipartiteGraph.subset e.2).choose) fun e => (maxDegree_le_of_forall_degree_le _ _ fun v => by
      simp [degree, neighborFinset_eq_filter, card_filter, -sum_boole]
      grind).trans $ hLists ..
  refine ⟨fun i j => this.choose ⟨s(.inl i, .inr j), by simp⟩, ?_,
    fun i j j' hj => this.choose.valid ?_, fun i i' j hi => this.choose.valid ?_⟩ <;> simp_all [lineGraph_adj_iff_exists]
  grind

end ListEdgeColouring
