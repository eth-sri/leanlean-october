module

public import PottsDiscontinuity.BetheAnsatz.OrderedPositions

/-!
# Reindexing cyclic gap tuples into the two ordinary orientations

The sign of the first coordinate separates the two copies of the diagonal as well.
The inverse shift is explicit; all residues remain distinct throughout the reindexing.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable {n : ℕ} (N : ℕ) (y : Fin (n + 1) → ℤ) (k : Fin (n + 1))

include N y in
/-- Inverse of the predecessor shift, on the integer cover. -/
def cyclicSuccessorPositions :
    Fin (n + 1) → ℤ :=
  fun k => y (finRotate _ k) + if finRotate _ k = 0 then ↑N else 0

@[simp] theorem cyclicPredecessor_successor :
    cyclicPredecessorPositions N (cyclicSuccessorPositions N y) = y := by
  funext k
  simp only [cyclicPredecessorPositions, cyclicSuccessorPositions, Equiv.apply_symm_apply,
    add_sub_cancel_right]

@[simp] theorem cyclicSuccessor_predecessor :
    cyclicSuccessorPositions N (cyclicPredecessorPositions N y) = y := by
  funext k
  simp only [cyclicPredecessorPositions, cyclicSuccessorPositions, Equiv.symm_apply_apply,
    sub_add_cancel]

theorem cyclicPredecessorPositions_injective {n N : ℕ} :
    Function.Injective (cyclicPredecessorPositions (n := n) N) :=
  Function.LeftInverse.injective (cyclicSuccessor_predecessor N)

@[simp] theorem cyclicSuccessorPositions_castSucc (k : Fin n) :
    cyclicSuccessorPositions N y k.castSucc = y k.succ := by
  have hr : finRotate _ k.castSucc = k.succ := finRotate_of_lt k.isLt
  simp only [cyclicSuccessorPositions, hr, Fin.succ_ne_zero, ↓reduceIte, add_zero]

@[simp] theorem cyclicSuccessorPositions_last :
    cyclicSuccessorPositions N y (Fin.last n) = y 0 + N := by
  simp only [cyclicSuccessorPositions, finRotate_last, ↓reduceIte]

theorem cyclicPredecessor_residue :
    cyclicPredecessorPositions N y k % N = y ((finRotate (n + 1)).symm k) % N := by
  unfold cyclicPredecessorPositions
  split_ifs <;> simp

theorem cyclicSuccessor_residue :
    cyclicSuccessorPositions N y k % N = y (finRotate (n + 1) k) % N := by
  unfold cyclicSuccessorPositions
  split_ifs <;> simp

theorem cyclicPredecessor_residue_injective_iff :
    Function.Injective (fun k => cyclicPredecessorPositions N y k % N) ↔
      Function.Injective (fun k => y k % N) := by
  simp_rw [cyclicPredecessor_residue]
  constructor
  · intro h i j he
    apply (finRotate _).injective
    apply h
    grind
  · intro h
    exact h.comp (finRotate _).symm.injective

theorem cyclicSuccessor_residue_injective_iff :
    Function.Injective (fun k => cyclicSuccessorPositions N y k % N) ↔
      Function.Injective (fun k => y k % N) := by
  simp_rw [cyclicSuccessor_residue]
  constructor
  · intro h i j he
    apply (finRotate _).symm.injective
    apply h
    grind
  · intro h
    exact h.comp (finRotate _).injective

end

section
variable {N n : ℕ} {x y : Fin (n + 1) → ℤ} (hx : x ∈ orderedTuples N (n + 1))
    (hy : y ∈ distinctGapTuples N x)

theorem orderedTuples_residue_injective {y : Fin n → ℤ}
    (hy : y ∈ orderedTuples N n) : Function.Injective (fun k => y k % N) := by
  intro i j he
  change y i % N = y j % N at he
  have hi := (mem_orderedTuples.mp hy).1 i
  have hj := (mem_orderedTuples.mp hy).1 j
  rw [Int.emod_eq_of_lt hi.1 hi.2, Int.emod_eq_of_lt hj.1 hj.2] at he
  exact (mem_orderedTuples.mp hy).2.injective he

/-- Weak monotonicity plus distinct residues implies strict monotonicity. -/
theorem strictMono_of_monotone_residues {m N : ℕ} {y : Fin m → ℤ}
    (hy : Monotone y) (hi : Function.Injective (fun k => y k % N)) : StrictMono y := by
  intro i j hij
  refine lt_of_le_of_ne (hy hij.le) ?_
  intro he
  solve_by_elim [hij.ne]

/-- Rotating the first point to the end preserves order when the tuple spans at most N. -/
theorem cyclicSuccessor_monotone {y : Fin (n + 1) → ℤ}
    (hy : Monotone y) (hspan : y (Fin.last n) - y 0 ≤ N) :
    Monotone (cyclicSuccessorPositions N y) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro k
  rw [cyclicSuccessorPositions_castSucc]
  by_cases hk : k.succ = Fin.last n
  · rw [hk, cyclicSuccessorPositions_last]
    omega
  · obtain ⟨l, hl⟩ := Fin.exists_castSucc_eq.mpr hk
    rw [← hl, cyclicSuccessorPositions_castSucc]
    solve_by_elim [hy]

include hx hy in
theorem nonnegative_gapTuple_ordered (h0 : 0 ≤ y 0) :
    y ∈ orderedTuples N (n + 1) := by
  obtain ⟨hg, hi⟩ := mem_filter.mp hy
  have hm := gapTuples_monotone hg
  refine mem_orderedTuples.mpr ⟨fun k => ⟨h0.trans (hm (Fin.zero_le k)), ?_⟩,
    strictMono_of_monotone_residues hm hi⟩
  exact ((mem_gapTuples.mp hg) k).2.trans_lt ((mem_orderedTuples.mp hx).1 k).2

include hx hy in
theorem negative_gapTuple_successor_ordered (h0 : y 0 < 0) :
    cyclicSuccessorPositions N y ∈ orderedTuples N (n + 1) := by
  obtain ⟨hg, hi⟩ := mem_filter.mp hy
  have hxm := (mem_orderedTuples.mp hx).2
  have hb0 := gapTuples_global_bounds hxm hg 0
  have hbl := gapTuples_global_bounds hxm hg (Fin.last n)
  refine mem_orderedTuples.mpr ⟨?_, strictMono_of_monotone_residues (cyclicSuccessor_monotone (gapTuples_monotone hg) (by omega)) ((cyclicSuccessor_residue_injective_iff N y).mpr hi)⟩
  intro k
  by_cases hk : k = Fin.last n
  · rw [hk, cyclicSuccessorPositions_last]
    have hxlast := ((mem_orderedTuples.mp hx).1 (Fin.last n)).1
    omega
  · obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.mpr hk
    rw [cyclicSuccessorPositions_castSucc]
    have hyb := (mem_gapTuples.mp hg) l.succ
    rw [cyclicPredecessorPositions_succ] at hyb
    have hxlo := ((mem_orderedTuples.mp hx).1 l.castSucc).1
    have hxhi := ((mem_orderedTuples.mp hx).1 l.succ).2
    omega

end

variable {N n : ℕ} {x : Fin (n + 1) → ℤ} (hx : x ∈ orderedTuples N (n + 1))
include hx

/-- The nonnegative-first gap tuples are exactly the ordinary lower orientation. -/
theorem nonnegative_distinctGapTuples :
    (distinctGapTuples N x).filter (fun y => 0 ≤ y 0) =
      (orderedTuples N (n + 1)).filter (fun y => y ∈ gapTuples N x) := by
  ext y
  simp only [mem_filter]
  constructor
  · rintro ⟨hy, h0⟩
    exact ⟨nonnegative_gapTuple_ordered hx hy h0, (mem_filter.mp hy).1⟩
  · rintro ⟨hy, hg⟩
    exact ⟨mem_filter.mpr ⟨hg, orderedTuples_residue_injective hy⟩,
      ((mem_orderedTuples.mp hy).1 0).1⟩

/-- The negative-first gap tuples are precisely the shifted ordinary upper orientation. -/
theorem negative_distinctGapTuples :
    (distinctGapTuples N x).filter (fun y => ¬ 0 ≤ y 0) =
      ((orderedTuples N (n + 1)).filter
        (fun y => cyclicPredecessorPositions N y ∈ gapTuples N x)).image
          (cyclicPredecessorPositions N) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hg, h0⟩ := mem_filter.mp hy
    refine mem_image.mpr ⟨cyclicSuccessorPositions N y, ?_, cyclicPredecessor_successor N y⟩
    exact mem_filter.mpr ⟨negative_gapTuple_successor_ordered hx hg (lt_of_not_ge h0),
      by simpa using (mem_filter.mp hg).1⟩
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    obtain ⟨ho, hg⟩ := mem_filter.mp hz
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hg, ?_⟩, ?_⟩
    · exact (cyclicPredecessor_residue_injective_iff N z).mpr (orderedTuples_residue_injective ho)
    · simp_all

/-- The exact finite cyclic-gap reindexing, for an arbitrary complex summand.
The diagonal has one representative in each of these disjoint sign classes. -/
theorem sum_distinctGapTuples_reindex (F : (Fin (n + 1) → ℤ) → ℂ) :
    (∑ y ∈ distinctGapTuples N x, F y) =
      (∑ y ∈ (orderedTuples N (n + 1)).filter (fun y => y ∈ gapTuples N x), F y) +
      ∑ y ∈ (orderedTuples N (n + 1)).filter
        (fun y => cyclicPredecessorPositions N y ∈ gapTuples N x),
          F (cyclicPredecessorPositions N y) := by
  rw [← Finset.sum_filter_add_sum_filter_not (distinctGapTuples N x) (fun y => 0 ≤ y 0) F,
    nonnegative_distinctGapTuples hx, negative_distinctGapTuples hx,
    Finset.sum_image cyclicPredecessorPositions_injective.injOn]

end PottsDiscontinuity.BetheAnsatz
