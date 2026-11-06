module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.OrderedPositions

/-!
# Coordinate conditions for the two transfer-action orientations

The inequalities here use the unique increasing integer coordinates of the actual states.
They supply the ordinary-coordinate side of the cyclic gap reindexing.
-/

@[expose] public section



namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

section

variable {N n : ℕ}
include N n

theorem interlacedLE_positions_iff  (x y : State N n) :
    InterlacedLE x.1 y.1 ↔
      (∀ k, positions x k ≤ positions y k) ∧
      ∀ k l : Fin n, k.val + 1 = l.val → positions y k ≤ positions x l := by
  rcases x with ⟨s, hs⟩
  rcases y with ⟨t, ht⟩
  subst n
  change (∃ h : s.card = t.card,
    (∀ k , s.orderEmbOfFin rfl k ≤ t.orderEmbOfFin h.symm k) ∧
    ∀ k l , k.val + 1 = l.val → t.orderEmbOfFin h.symm k ≤ s.orderEmbOfFin rfl l) ↔ _
  simp only [positions]
  constructor
  · grind
  · simp_all

theorem interlacedLE_positions_succ_iff  (x y : State N (n + 1)) :
    InterlacedLE x.1 y.1 ↔
      (∀ k, positions x k ≤ positions y k) ∧
      ∀ k : Fin n, positions y k.castSucc ≤ positions x k.succ := by
  rw [interlacedLE_positions_iff]
  constructor
  · simp_all
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j hij => ?_⟩
    
    let k : Fin n := ⟨i.val,  by  omega ⟩
    have hik : k.castSucc = i := Fin.ext rfl
    have hjk : k.succ = j := Fin.ext hij
    simpa only [hik, hjk] using h2 k

/-- In the ordinary row, the lower interlacing orientation is exactly the gap inequalities. -/
theorem ordered_mem_gapTuples_iff  {x y : Fin (n + 1) → ℤ}
    (hx : x ∈ orderedTuples N (n + 1)) (hy : y ∈ orderedTuples N (n + 1)) :
    y ∈ gapTuples N x ↔ (∀ k, y k ≤ x k) ∧ ∀ k : Fin n, x k.castSucc ≤ y k.succ := by
  constructor
  · intro hg
    refine ⟨fun k => ((mem_gapTuples.mp hg) k).2, fun k => ?_⟩
    
    simpa only [cyclicPredecessorPositions_succ] using  ((mem_gapTuples.mp hg) k.succ).1 
  · rintro ⟨hu, hl⟩
    apply mem_gapTuples.mpr
    intro k
    refine ⟨?_, hu k⟩
    induction k using Fin.cases with
    | zero =>
      simp_all <;> grind
    | succ k =>
      simp_all

theorem interlacedLE_iff_positions_mem_gapTuples  (x y : State N (n + 1)) :
    InterlacedLE y.1 x.1 ↔ positions y ∈ gapTuples N (positions x) := by
  rw [interlacedLE_positions_succ_iff,
    ordered_mem_gapTuples_iff (positions_mem_orderedTuples x) (positions_mem_orderedTuples y)]

/-- Applying the same predecessor shift to both tuples preserves pointwise order. -/
theorem cyclicPredecessorPositions_le_iff  (x y : Fin (n + 1) → ℤ) :
    (∀ k, cyclicPredecessorPositions N x k ≤ cyclicPredecessorPositions N y k) ↔
      ∀ k, x k ≤ y k := by
  constructor
  · intro h k
    have h' := h (finRotate (n + 1) k)
    simp only [cyclicPredecessorPositions, Equiv.symm_apply_apply] at h'
    omega
  · simp_all [cyclicPredecessorPositions]

/-- The upper interlacing orientation becomes a gap tuple after moving the last point back N. -/
theorem ordered_shift_mem_gapTuples_iff  {x y : Fin (n + 1) → ℤ}
    (hx : x ∈ orderedTuples N (n + 1)) (hy : y ∈ orderedTuples N (n + 1)) :
    cyclicPredecessorPositions N y ∈ gapTuples N x ↔
      (∀ k, x k ≤ y k) ∧ ∀ k : Fin n, y k.castSucc ≤ x k.succ := by
  rw [mem_gapTuples]
  constructor
  · intro h
    refine ⟨cyclicPredecessorPositions_le_iff x y |>.mp  fun k => (h k).1 , fun k => ?_⟩
    
    simpa only [cyclicPredecessorPositions_succ] using  (h k.succ).2 
  · rintro ⟨hl, hu⟩
    
    intro k
    refine ⟨((cyclicPredecessorPositions_le_iff (N := N) x y).mpr hl) k, ?_⟩
    induction k using Fin.cases with
    | zero =>
      simp_all <;> grind
    | succ k =>
      simp_all

theorem interlacedLE_iff_shift_positions_mem_gapTuples  (x y : State N (n + 1)) :
    InterlacedLE x.1 y.1 ↔
      cyclicPredecessorPositions N (positions y) ∈ gapTuples N (positions x) := by
  rw [interlacedLE_positions_succ_iff,
    ordered_shift_mem_gapTuples_iff (positions_mem_orderedTuples x) (positions_mem_orderedTuples y)]

end

end PottsDiscontinuity.BetheAnsatz
