module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Minimal

@[expose] public section

namespace ListEdgeColouring

open Finset

local grind_pattern card_le_card => #s, #t
attribute [local grind =] MinimalFor Function.Injective SimpleGraph.adj_comm
  SimpleGraph.EdgeLabeling.mk Sym2.hrec Set.mem_ofPred Set.MapsTo Set.InjOn erase_eq_of_notMem
  SimpleGraph.degree SimpleGraph.mem_neighborFinset SimpleGraph.lineGraph_adj_iff_exists
  SimpleGraph.top_adj Equiv.apply_eq_iff_eq Fintype.card_prod

theorem gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by
  let top m := MinimalFor (E m) (rm m)
  by_cases h : ∃ m₂ m₁ w, top m₂ w ∧ top m₁ w ∧ rw w m₁ < rw w m₂
  · obtain ⟨m₂, m₁, w, h⟩ := h
    exact Exists.imp (by grind) (gale_shapley
      (Function.curry (· ∈ Set.ofPred (Function.uncurry E) \ {(m₂, w)})) rm rw hrm hrw)
  have _ m := forall_exists_index.mp (exists_minimalFor_of_wellFoundedLT (E m) (rm m))
  exact ⟨top, by grind⟩
termination_by Set.ncard (Function.uncurry E)
decreasing_by
  exact Set.ncard_sdiff_singleton_lt_of_mem h.left.prop

open Classical in
lemma bipartite_galvin {α Color} [Fintype α] (U : Finset _) Δ (L : _ → _)
    (hD : ∀ x : α, #{y | (x, y) ∈ U} ≤ Δ ∧ #{y | (y, x) ∈ U} ≤ Δ)
    (hL : ∀ p ∈ U, Δ ≤ #(L p)) :
    ∃ c : U → Color, ∀ p, c p ∈ L p.val ∧
      ∀ q, c p = c q → (p.val.fst = q.val.fst ↔ p.val.snd = q.val.snd) := by
  let B₀
    | Sum.inl m, Sum.inr w | Sum.inr w, Sum.inl m => if (m, w) ∈ U then 1 else 0
    | _, _ => 0
  let B x y := if x = y then Δ - ∑ z, B₀ x z else B₀ x y
  have hB z : ∑ y, B z y = Δ ∧ ∑ x, B x z = Δ := by
    cases z <;> simp +zetaDelta [Fintype.sum_sum_type, hD]
  obtain ⟨Φ⟩ : ∃ Φ : _ → _ → _, ∀ x y, 0 < B x y → Φ x y < Δ ∧
      ∀ x' y', 0 < B x' y' → Φ x y = Φ x' y' → (x = x' ↔ y = y') := by
    clear_value B
    clear hD hL
    induction Δ generalizing B
    · exact ⟨0, by grind [sum_eq_zero_iff]⟩
    rename_i d ih
    obtain ⟨f, hf⟩ := Iff.mp (Fintype.all_card_le_filter_rel_iff_exists_injective
      (0 < B · ·)) fun S => by
      refine Nat.le_of_mul_le_mul_right ?_ d.succ_pos
      rw [← sum_const_nat fun x _ => And.left (hB x), ← sum_const_nat fun y _ => And.right (hB y),
        sum_comm, ← Fintype.sum_subset ?_]
      · gcongr <;> simp
      grind [sum_eq_zero_iff]
    obtain ⟨Φ'⟩ := ih (fun x y => B x y - if y = f x then 1 else 0) <|
      (Finite.surjective_of_injective hf.left).forall.mpr fun _ => by
        constructor <;> rw [sum_tsub_distrib _ (by grind)] <;> simp [hf.left.eq_iff, hB]
    exact ⟨fun x y => if y = f x then d else Φ' x y, by grind⟩
  let rm p := if p ∈ U then Φ (Sum.inl p.fst) (Sum.inr p.snd) else Δ + Fintype.equivFin _ p
  let arc p q := (rm q < rm p ∧ p.fst = q.fst) ∨ (rm p < rm q ∧ p.snd = q.snd)
  replace hL p (hp : p ∈ U) : #(U.filter (arc p)) < #(L p) :=
    lt_of_le_of_lt (card_le_card_of_injOn (t := erase (range Δ) (rm p)) rm
      (by grind) (by grind)) (by grind)
  generalize U = V at hL ⊢
  induction V using strongInductionOn generalizing L
  rename_i V ih
  rcases V.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨nofun, nofun⟩
  obtain ⟨κ⟩ := card_pos.mp (pos_of_gt (hL p₀ hp₀))
  obtain ⟨μ⟩ := gale_shapley (Function.curry fun p => p ∈ V ∧ κ ∈ L p) (Function.curry rm)
    (Function.swap (Function.curry (Δ + Fintype.card α ^ 2 - rm ·))) (by grind) (by grind)
  unfold Function.curry at *
  obtain ⟨c'⟩ := ih (V.filter (¬ Function.uncurry μ ·)) (by grind) ((erase · κ) ∘ L) fun p _ => by
    by_cases κ ∈ L p
    · obtain ⟨q, hq⟩ : ∃ q, μ q.fst q.snd ∧ arc p q := by
        cases p
        grind
      grind [card_erase_of_mem (V.mem_filter.mpr ⟨by grind, hq.right⟩)]
    grind
  exact ⟨fun p => if _ : μ p.val.fst p.val.snd then κ else c' ⟨p, by grind⟩, by grind⟩

theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ #(lists e)) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  classical
  obtain ⟨⟨s⟩⟩ := hG
  obtain ⟨c⟩ := bipartite_galvin {p | G.Adj p.fst p.snd ∧ s p.fst = 0} G.maxDegree
    (fun p => if h : G.Adj p.fst p.snd then lists ⟨Quot.mk _ p, h⟩ else ∅)
    (by
      intro x
      grind [G.degree_le_maxDegree x])
    (by grind)
  refine ⟨⟨SimpleGraph.EdgeLabeling.mk
    (fun x y _ => c ⟨if s x = 0 then (x, y) else (y, x), by grind⟩) (by grind), ?_⟩, ?_⟩
  · rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    grind
  rintro ⟨⟨⟩⟩
  dsimp [DFunLike.coe]
  grind

theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ #(lists i j)) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  obtain ⟨c⟩ := bipartite_galvin univ n (Function.uncurry lists) (by simp) (by grind)
  exact ⟨Function.curry (c ⟨·, mem_univ _⟩), by grind⟩

end ListEdgeColouring
