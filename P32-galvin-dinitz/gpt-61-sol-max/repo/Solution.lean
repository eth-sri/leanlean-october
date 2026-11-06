/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Stable matchings, Galvin's theorem, and the Dinitz problem

The shared stable-matching argument works directly with edge endpoint maps. It supplies the
kernels for the list-colouring lemma. Hall's theorem decomposes regular integral matrices
into supported permutations, giving the initial edge colouring required by Galvin's argument.
For the Dinitz problem that initial colouring is simply addition modulo `n`.
-/
open Finset SimpleGraph Classical
namespace ListEdgeColouring
section

variable {α β γ ρ Color : Type*} [Fintype α] [LinearOrder ρ]
  (a : α → β) (b : α → γ) (r s : α → ρ)

/-- Strict preference at either endpoint; smaller ranks are preferred. -/
abbrev Pref e f :=
  a e = a f ∧ r f < r e ∨ b e = b f ∧ s f < s e

/-- Equal ranks at a common endpoint determine the edge.
With the endpoint maps themselves as ranks, `NoTie a b a b S` says that `S` is a matching. -/
abbrev NoTie (s : α → Color) (S : Finset α := univ) := ∀ e ∈ S, ∀ f ∈ S,
  r e = r f ∧ a e = a f ∨ s e = s f ∧ b e = b f → e = f

/-- Every finite bipartite preference system has a stable matching. The ranks need only
be injective among edges sharing an endpoint. -/
theorem stable (hinj : NoTie a b r s) (S : Finset α) :
    ∃ K ⊆ S, NoTie a b a b K ∧
      ∀ e ∈ S, ∃ f ∈ K, e = f ∨ Pref a b r s e f := by
  induction S using Finset.strongInduction with
  | H S ih =>
    -- Proposals are the best remaining edges at the first endpoint.
    let T := S.filter fun e => ∀ f ∈ S, a e = a f → r e ≤ r f
    have top e he := Finset.exists_min_image (S.filter (a e = a ·)) r
      ⟨e, mem_filter.mpr ⟨he, rfl⟩⟩
    rcases Classical.em (∃ e ∈ T, ∃ f ∈ T, b e = b f ∧ s e < s f) with ⟨e, he, f, hf⟩ | h
    · -- Two proposals compete at the second endpoint: delete the less preferred one.
      apply (ih (S.erase f) (erase_ssubset (by grind))).imp
      grind
    · use T
      grind

/-- Galvin's argument for edges presented by their two endpoint maps. -/
theorem listEdgeColoring
    (L : α → Finset Color) {n : ℕ} (φ : α → Fin n)
    (hφ : NoTie a b φ φ)
    (hL : ∀ e, n ≤ (L e).card) :
    ∃ c : α → Color, (∀ e, c e ∈ L e) ∧ NoTie a b c c := by
  -- Reverse the initial colour order at the second endpoint.
  let ψ := Fin.rev ∘ φ
  let D e := univ.filter (Pref a b φ ψ e)
  -- Outneighbours have distinct initial colours, all different from that of the edge itself.
  have H e : (D e).card < (L e).card := by
    calc
      _ ≤ (univ.erase (φ e)).card := by
        apply card_le_card_of_injOn φ <;> intro <;> grind
      _ < n := by simpa using Nat.pred_lt_self (φ e).pos
      _ ≤ _ := hL e
  -- The kernel lemma, generalized to a finite vertex set for strong induction.
  have aux (U : Finset α) : ∀ L : α → Finset Color,
      (∀ x ∈ U, (U ∩ D x).card < (L x).card) →
      ∃ c : α → Color, (∀ x ∈ U, c x ∈ L x) ∧ NoTie a b c c U := by
    induction U using Finset.strongInduction with
    | H U ih =>
      intro L hL
      rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
      · use fun e => (card_pos.mp (Nat.zero_lt_of_lt (H e))).choose
        grind
      obtain ⟨κ, hκ⟩ := card_pos.mp (Nat.zero_lt_of_lt (hL x₀ hx₀))
      -- Give κ to a stable matching of edges whose lists contain κ.
      obtain ⟨K, hKS, hKi, hKa⟩ := stable a b φ ψ
        (by grind) (U.filter (κ ∈ L ·))
      obtain ⟨c, hc⟩ := ih (U \ K) (by grind [sdiff_ssubset])
        (fun x => (L x).erase κ) (by
          -- Absorption removes an outneighbour whenever erasing κ shortens this list.
          grind [sdiff_inter_right_comm, card_union_eq_card_add_card,
            Finset.disjoint_left, erase_eq_of_notMem])
      use fun x => if x ∈ K then κ else c x
      grind
  simpa using aux univ L (by simpa)

end

/-- **Gale–Shapley (1962).** For a bipartite acceptability relation `E` between finite sets `M`
and `W`, with strict preferences given by injective rank functions (`rm m w < rm m w'` means that
`m` prefers `w` to `w'`), there is a stable matching. -/
public theorem gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by
  cases nonempty_fintype (M × W)
  apply (stable Prod.fst Prod.snd
    (Function.uncurry rm) (Function.uncurry (Function.swap rw))
    (by grind)
    (univ.filter (Function.uncurry E))).imp' (Function.curry ∘ Membership.mem)
  grind

/-- **Galvin's theorem (1995).** If every edge of a finite bipartite graph `G` has a list of at
least `Δ(G)` colours, then `G` has a proper edge colouring choosing every colour from the list of
its edge. -/
public theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  -- Diagonal padding makes every row and column sum equal to the maximum degree.
  let M : V → V → ℕ := G.adjMatrix ℕ + Matrix.diagonal (G.maxDegree - G.degree ·)
  have hr : ∀ i, ∑ j, M i j = G.maxDegree := by
    simp [M, Matrix.diagonal_apply, sum_add_distrib, ← G.neighborFinset_eq_filter,
      G.degree_le_maxDegree]
  have hc : ∀ j, ∑ i, M i j = G.maxDegree := by
    simpa [M, Matrix.diagonal_apply, sum_add_distrib, G.adj_comm] using hr
  -- Subtract supported perfect matchings from the regular integral matrix.
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin G.maxDegree → Equiv.Perm V,
      ∀ i j, 0 < M i j → ∃ t, σ t i = j := by
    -- Only the two sum identities are needed for this induction.
    generalize G.maxDegree = k at hr hc ⊢
    clear_value M
    induction k generalizing M with
    | zero =>
      simp_all
    | succ k ih =>
      let f i := univ.filter (M i · ≠ 0)
      -- Weighted Hall: compare the same supported entries by rows and by columns.
      have hf A : #A ≤ #(A.biUnion f) := by
        refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos k)
        calc A.card * k.succ = ∑ p ∈ A ×ˢ univ, M p.1 p.2 := by simp [sum_product, hr]
          _ ≤ ∑ p ∈ univ ×ˢ A.biUnion f, M p.1 p.2 := sum_le_sum_of_ne_zero (by grind)
          _ = #(A.biUnion f) * k.succ := by
            simp [sum_product, sum_comm, hc]
      obtain ⟨g, hg, hg'⟩ := HallMarriageTheorem.hall_hard_inductive hf
      let σ := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
      -- Subtract a supported permutation and decompose the remaining regular matrix.
      refine (ih (fun i j => M i j - if σ i = j then 1 else 0) ?_ ?_).imp'
        (Fin.cases σ) (by simp [Fin.exists_fin_succ]; grind)
      all_goals
        intro i
        rw [sum_tsub_distrib _ (by grind)]
        simp [hr, hc, -sum_boole] <;> simp [← σ.eq_symm_apply]
  obtain ⟨c⟩ := hG
  have ends : ∀ e : G.edgeSet,
      ∃ a b, e.val = s(a, b) ∧ c a < c b := by
    rintro ⟨⟨x, y⟩, he⟩
    grind [c.valid he, Sym2.eq_swap]
  choose a b he hab using ends
  choose φ hφ using fun e => hσ (a e) (b e)
    (by simp [M, ← mem_edgeSet, ← he e])
  obtain ⟨f, hf⟩ := listEdgeColoring a b lists φ
    (by grind [Equiv.apply_eq_iff_eq]) hLists
  use Coloring.mk f (by grind [lineGraph_adj_iff_exists])
  exact hf.1

/-- **The Dinitz problem** (Galvin 1995). If every cell of an `n × n` array has a list of at least
`n` symbols, there is a choice of one symbol from each list with all symbols in each row distinct
and all symbols in each column distinct. -/
public theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  -- Addition modulo n is a proper initial colouring of the cells.
  apply (listEdgeColoring Prod.fst Prod.snd
    (Function.uncurry lists)
    (Function.uncurry HAdd.hAdd)
    (by aesop)
    (by grind)).imp' Function.curry
  grind

end ListEdgeColouring
