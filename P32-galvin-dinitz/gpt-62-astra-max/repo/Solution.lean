/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Stable matchings, Galvin's theorem, and the Dinitz problem

Model an edge or acceptable pair as a contract between its two endpoints. Stable
matchings are kernels on these contracts. A proper edge colouring orders the
contracts at the two ends in opposite directions; the resulting kernels select
independent classes for the list colouring.
-/

@[expose] public section

namespace ListEdgeColouring

open Finset SimpleGraph Function

section Contracts

variable {X A B C R : Type*} [LinearOrder R] (a : X → A) (b : X → B) (r s : X → R)

/-- The two ends of a contract can each prefer another contract at that end. -/
def Arc (x y : X) :=
  (a x = a y ∧ r y < r x) ∨ (b x = b y ∧ s y < s x)

/-- If the first choices on the left conflict on the right, delete the worse one.
The better one, even if it is not ultimately chosen, ensures the deletion is safe. -/
theorem stable (S : Finset X) :
    ∃ K ⊆ S, (∀ x ∈ K, ∀ y ∈ K, ¬Arc a b r s x y) ∧
      ∀ x ∈ S, x ∉ K → ∃ y ∈ K, Arc a b r s x y := by
  classical
  induction S using Finset.eraseInduction with | _ S ih
  let T := S.filter fun x => ∀ y ∈ S, a x = a y → r x ≤ r y
  by_cases! h : ∀ x ∈ T, ∀ y ∈ T, ¬Arc a b r s x y
  · refine ⟨T, filter_subset .., h, fun x hx hn => ?_⟩
    obtain ⟨y, hy, hm⟩ := exists_min_image (S.filter (a · = a x)) r ⟨x, by grind⟩
    use y; grind [Arc]
  obtain ⟨x, hx, y, hy, h⟩ := h
  obtain ⟨K, hK, hi, ha⟩ := ih x (by grind)
  use K; grind [Arc]

/-- A colouring separates edges at either end. -/
def Proper (f : X → C) :=
  ∀ x y, f x = f y → a x = a y ∨ b x = b y → x = y

/-- An ordinary `n`-edge-colouring gives a list colouring. Orient towards lower colours
on the left and higher colours on the right: the outgoing colours are all distinct. -/
theorem listColor [Finite X] {n : ℕ}
    (t : X → Fin n) (ht : Proper a b t) (L : X → Finset C) (hL : ∀ x, n ≤ #(L x)) :
    ∃ f, (∀ x, f x ∈ L x) ∧ Proper a b f := by
  classical
  let s x := (t x).rev
  obtain ⟨_, _⟩ := exists_wellFoundedLT C
  choose K sub ind absorb using stable a b t s
  -- S i consists of the edges listing i that no earlier kernel has claimed.
  -- Well-founded recursion lets us give K (S i) colour i.
  have eqn := WellFoundedLT.fix_eq fun (i : C) prev =>
    (Set.toFinite {x | i ∈ L x ∧ ∀ j h, x ∉ K (prev j h)}).toFinset
  generalize WellFoundedLT.fix (α := C) _ = S at eqn
  simp [Finset.ext_iff] at eqn
  -- An edge that never gets coloured has a different out-neighbour for each list colour,
  -- with distinct original ranks other than its own. There are too few such ranks.
  have total x : ∃ i, x ∈ K (S i) := by
    by_contra! hn
    have h : #(L x) ≤ #(univ.erase (t x)) := by
      apply card_le_card_of_forall_subsingleton
        (fun i k => ∃ y ∈ K (S i), Arc a b t s x y ∧ t y = k) <;>
        grind [Arc, Proper, Set.Subsingleton]
    simp at h
    grind [Fin.pos (t x)]
  choose c hc using total
  exact ⟨c, by grind [Proper, Arc]⟩

end Contracts

/-- An integral matrix with all margins `n` is covered by `n` permutation matrices.
Hall's condition follows by summing the weights out of the rows in `t`. -/
theorem cover {V : Type*} [Fintype V] (n : ℕ) (w : V → V → ℕ)
    (hw : ∀ i, ∑ j, w i j = n ∧ ∑ j, w j i = n) :
    ∃ p : Fin n → Equiv.Perm V, ∀ i j, w i j ≠ 0 → ∃ k, p k i = j := by
  classical
  induction n generalizing w with
  | zero => simp_all [sum_eq_zero_iff]
  | succ n ih =>
    obtain ⟨g, hg, hg'⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective fun i j => w i j ≠ 0).mp fun t => by
        have bound j : ∑ i ∈ t, w i j ≤ if ∃ i ∈ t, w i j ≠ 0 then n + 1 else 0 := by
          split
          · rw [← (hw j).2]; gcongr; simp
          · simp_all
        simpa [sum_comm (t := t), ← sum_filter, hw] using
          sum_le_sum (s := univ) (fun j _ => bound j)
    -- Remove one copy of this permutation matrix: all margins drop by one.
    let σ := Equiv.ofBijective g hg.bijective_of_finite
    obtain ⟨p, hp⟩ := ih (fun i j => w i j - if σ i = j then 1 else 0) fun i => by
      simp (disch := grind) only [sum_tsub_distrib]
      simp [hw, ← σ.eq_symm_apply (x := i)]
    use Fin.cons σ p
    simp [Fin.exists_fin_succ]
    grind

/-- Stable matching for a finite bipartite acceptability relation. -/
theorem gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Injective (rm m))
    (hrw : ∀ w, Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by
  obtain ⟨K, hK, hi, ha⟩ := stable Prod.fst Prod.snd (uncurry rm) (fun p => rw p.2 p.1)
    (Set.toFinite {p | uncurry E p}).toFinset
  use fun m w => (m, w) ∈ K
  grind [Arc, Injective, Set.Finite.mem_toFinset]

/-- **Galvin's theorem.** Pad the adjacency matrix on the diagonal to make it regular.
Its permutation cover gives a proper colouring of the edges directed from left to right. -/
theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ #(lists e)) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  classical
  obtain ⟨c⟩ := hG
  let w := G.adjMatrix ℕ + Matrix.diagonal (G.maxDegree - G.degree ·)
  obtain ⟨p, hp⟩ := cover G.maxDegree w fun i => by
    simp [w, Matrix.diagonal, sum_add_distrib, G.adj_comm _ i, ← neighborFinset_eq_filter,
      G.degree_le_maxDegree i]
  have ends : ∀ e : G.edgeSet, ∃ x y, e.val = s(x, y) ∧ c x < c y := by
    rintro ⟨⟨x, y⟩, he⟩
    grind [Sym2.eq_swap, c.valid he]
  choose a b hab hlt using ends
  -- Label an edge by a permutation taking its left endpoint to its right endpoint.
  choose t ht using fun e => hp (a e) (b e) (by
    simp [w, ← mem_edgeSet, ← hab e])
  obtain ⟨f, hf, hf'⟩ := listColor a b t (by
    grind [Proper, Equiv.apply_eq_iff_eq]) lists hLists
  exact ⟨Coloring.mk f (by grind [Proper, lineGraph_adj_iff_exists]), hf⟩

/-- **Dinitz problem.** The cyclic Latin square is the ordinary colouring of the cells. -/
theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ #(lists i j)) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  obtain ⟨f, hf, h⟩ := listColor Prod.fst Prod.snd (fun p => p.1 + p.2)
    (by grind [Proper, add_left_inj, add_right_inj]) (uncurry lists)
    (Prod.rec hLists)
  exact ⟨curry f, by grind [Proper]⟩

end ListEdgeColouring
