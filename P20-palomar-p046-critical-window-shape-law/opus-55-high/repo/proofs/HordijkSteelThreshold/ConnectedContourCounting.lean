module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Tactic

public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Insert an out-and-back excursion at a visited vertex. -/
theorem walk_insert_excursion {r : V} (p : G.Walk r r) {u v : V}
    (hu : u ∈ p.support) (huv : G.Adj u v) :
    ∃ q : G.Walk r r, q.length = p.length + 2 ∧
      q.support.toFinset = insert v p.support.toFinset := by
  let q := (p.takeUntil u hu).append
    ((Walk.cons huv $ Walk.cons huv.symm Walk.nil).append $ p.dropUntil u hu)
  refine ⟨q, ?_, ?_⟩
  · have h := congrArg Walk.length (p.take_spec hu)
    simp only [Walk.length_append] at h
    simp only [q, Walk.length_append, Walk.length_cons, Walk.length_nil]
    omega
  · ext x
    have h : x ∈ p.support ↔ x ∈ (p.takeUntil u hu).support ∨
        x ∈ (p.dropUntil u hu).support := by
      conv_lhs => rw [← p.take_spec hu]
      exact Walk.mem_support_append_iff _ _
    aesop

/-- A cut-crossing property constructs a covering closed walk of optimal tree-tour length.
The property will be supplied by connectedness of the actual contour. -/
theorem finite_connected_covering_tour (C : Finset V) (r : V) (hr : r ∈ C)
    (hcross : ∀ S : Finset V, S ⊆ C → r ∈ S → S ≠ C →
      ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ G.Adj u v) :
    ∃ p : G.Walk r r, p.support.toFinset = C ∧ p.length = 2 * (C.card - 1) := by
  have extend : ∀ k : ℕ, ∀ p : G.Walk r r,
      p.support.toFinset ⊆ C →
      p.length = 2 * (p.support.toFinset.card - 1) →
      (C \ p.support.toFinset).card = k →
      ∃ q : G.Walk r r, q.support.toFinset = C ∧ q.length = 2 * (C.card - 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro p hp hl hk
      by_cases he : p.support.toFinset = C
      · grind
      · have hrp := List.mem_toFinset.mpr p.start_mem_support
        obtain ⟨u, hu, v, hv, hvs, huv⟩ := hcross _ hp hrp he
        obtain ⟨q, hql, hqs⟩ := walk_insert_excursion G p (List.mem_toFinset.mp hu) huv
        grind
  exact extend _ Walk.nil (by simp_all) (by simp) rfl

variable [Fintype V] [DecidableRel G.Adj]

/-- Specifying both endpoints cannot increase the degree-based walk count. -/
theorem card_walks_le_degree_pow (d : ℕ) (hd : ∀ v, (G.neighborFinset v).card ≤ d)
    (n : ℕ) (u v : V) : (G.finsetWalkLength n u v).card ≤ d ^ n := by
  induction n generalizing u v with
  | zero =>
    simp only [finsetWalkLength]
    grind
  | succ n ih =>
    refine Finset.card_biUnion_le.trans $ (Finset.sum_le_card_nsmul _ _ (d ^ n) fun w _ => by
      simpa using ih w v).trans ?_
    simpa [pow_succ', SimpleGraph.neighborFinset] using Nat.mul_le_mul_right _ $ hd u

end HordijkSteelThreshold
