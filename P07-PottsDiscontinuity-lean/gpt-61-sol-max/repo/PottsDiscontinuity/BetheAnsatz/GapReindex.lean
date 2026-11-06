module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.OrderedPositions

/-!
# Reindexing cyclic gap tuples into the two ordinary orientations

The sign of the first coordinate separates the two copies of the diagonal as well.
The inverse shift is explicit; all residues remain distinct throughout the reindexing.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Inverse of the predecessor shift, on the integer cover. -/
def cyclicSuccessorPositions {n : ℕ} (N : ℕ) (y : Fin (n + 1) → ℤ) :
    Fin (n + 1) → ℤ :=
  fun k => y (finRotate (n + 1) k) + if finRotate (n + 1) k = 0 then (N : ℤ) else 0

section

variable {n : ℕ} (N : ℕ) (y : Fin (n + 1) → ℤ)


@[simp] theorem cyclicPredecessor_successor  :
    cyclicPredecessorPositions N (cyclicSuccessorPositions N y) = y := by
  funext k
  simp only [cyclicPredecessorPositions, cyclicSuccessorPositions, Equiv.apply_symm_apply,
    add_sub_cancel_right]

@[simp] theorem cyclicSuccessor_predecessor  :
    cyclicSuccessorPositions N (cyclicPredecessorPositions N y) = y := by
  grind [cyclicPredecessorPositions, cyclicSuccessorPositions]

end

theorem cyclicPredecessorPositions_injective {n N : ℕ} :
    Function.Injective (cyclicPredecessorPositions (n := n) N) :=
  Function.LeftInverse.injective (cyclicSuccessor_predecessor N)

section

variable {n : ℕ} (N : ℕ) (y : Fin (n + 1) → ℤ)
include N y

@[simp] theorem cyclicSuccessorPositions_castSucc  (k : Fin n) :
    cyclicSuccessorPositions N y k.castSucc = y k.succ := by
  simp_all [cyclicSuccessorPositions]

@[simp] theorem cyclicSuccessorPositions_last  :
    cyclicSuccessorPositions N y (Fin.last n) = y 0 + N := by
  simp_all [cyclicSuccessorPositions]

theorem cyclicPredecessor_residue  (k : Fin (n + 1)) :
    cyclicPredecessorPositions N y k % (N : ℤ) = y ((finRotate (n + 1)).symm k) % (N : ℤ) := by
  unfold cyclicPredecessorPositions
  split_ifs <;> simp

theorem cyclicSuccessor_residue  (k : Fin (n + 1)) :
    cyclicSuccessorPositions N y k % (N : ℤ) = y (finRotate (n + 1) k) % (N : ℤ) := by
  unfold cyclicSuccessorPositions
  split_ifs <;> simp

theorem cyclicPredecessor_residue_injective_iff  :
    Function.Injective (fun k => cyclicPredecessorPositions N y k % (N : ℤ)) ↔
      Function.Injective  fun k => y k % (N : ℤ)  := by
  simp_rw [cyclicPredecessor_residue]
  constructor
  · intro h i j he
    apply (finRotate (n + 1)).injective
    apply h
    simpa only [Equiv.symm_apply_apply] using he
  · intro h
    exact h.comp (finRotate (n + 1)).symm.injective

theorem cyclicSuccessor_residue_injective_iff  :
    Function.Injective (fun k => cyclicSuccessorPositions N y k % (N : ℤ)) ↔
      Function.Injective  fun k => y k % (N : ℤ)  := by
  simp_rw [cyclicSuccessor_residue]
  constructor
  · intro h i j he
    apply (finRotate (n + 1)).symm.injective
    apply h
    simpa only [Equiv.apply_symm_apply] using he
  · intro h
    exact h.comp (finRotate (n + 1)).injective

end

theorem orderedTuples_residue_injective {N n : ℕ} {y : Fin n → ℤ}
    (hy : y ∈ orderedTuples N n) : Function.Injective  fun k => y k % (N : ℤ)  := by
  intro i j he
  change y i %  N  = y j % (N ) at he
  have hi := (mem_orderedTuples.mp hy).1 i
  have hj := (mem_orderedTuples.mp hy).1 j
  rw [Int.emod_eq_of_lt hi.1 hi.2, Int.emod_eq_of_lt hj.1 hj.2] at he
  exact (mem_orderedTuples.mp hy).2.injective he

/-- Weak monotonicity plus distinct residues implies strict monotonicity. -/
theorem strictMono_of_monotone_residues {m N : ℕ} {y : Fin m → ℤ}
    (hy : Monotone y) (hi : Function.Injective  fun k => y k % (N : ℤ) ) : StrictMono y := by
  intro i j hij
  refine lt_of_le_of_ne (hy hij.le) ?_
  intro he
  exact hij.ne (hi (congrArg (fun z  => z % (N : ℤ)) he))

section

variable {N n : ℕ}
include N n

/-- Rotating the first point to the end preserves order when the tuple spans at most N. -/
theorem cyclicSuccessor_monotone  {y : Fin (n + 1) → ℤ}
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
    exact hy (by change l.val ≤ l.val + 1; omega)

section

variable {x y : Fin (n + 1) → ℤ} (hx : x ∈ orderedTuples N (n + 1)) (hy : y ∈ distinctGapTuples N x)
include hx hy

theorem nonnegative_gapTuple_ordered   (h0 : 0 ≤ y 0) :
    y ∈ orderedTuples N (n + 1) := And.casesOn (mem_filter.mp hy) fun hg hi =>
                                     have hm := gapTuples_monotone hg;
                                     mem_orderedTuples.mpr
                                       ⟨fun k =>
                                         ⟨LE.le.trans h0 (hm (Fin.zero_le k)),
                                           LE.le.trans_lt (mem_gapTuples.mp hg k).right ((mem_orderedTuples.mp hx).left k).right⟩,
                                         strictMono_of_monotone_residues hm hi⟩

theorem negative_gapTuple_successor_ordered   (h0 : y 0 < 0) :
    cyclicSuccessorPositions N y ∈ orderedTuples N (n + 1) := by
  obtain ⟨hg, hi⟩ := mem_filter.mp hy
  have hxm := (mem_orderedTuples.mp hx).2
  have hb0 := gapTuples_global_bounds hxm hg 0
  have hbl := gapTuples_global_bounds hxm hg (Fin.last n)
  
  
  refine mem_orderedTuples.mpr ⟨?_, strictMono_of_monotone_residues (cyclicSuccessor_monotone (N := N) (gapTuples_monotone hg) (by omega)) ((cyclicSuccessor_residue_injective_iff N y).mpr hi)⟩
  intro k
  by_cases hk : k = Fin.last n
  · simp_all <;> grind
  · obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.mpr hk
    rw [cyclicSuccessorPositions_castSucc]
    have hyb := (mem_gapTuples.mp hg) l.succ
    rw [cyclicPredecessorPositions_succ] at hyb
    have hxlo := ((mem_orderedTuples.mp hx).1 l.castSucc).1
    have hxhi := ((mem_orderedTuples.mp hx).1 l.succ).2
    constructor <;> omega

end

section

variable {x : Fin (n + 1) → ℤ} (hx : x ∈ orderedTuples N (n + 1))
include hx

/-- The nonnegative-first gap tuples are exactly the ordinary lower orientation. -/
theorem nonnegative_distinctGapTuples   :
    (distinctGapTuples N x).filter  fun y => 0 ≤ y 0  =
      (orderedTuples N (n + 1)).filter  fun y => y ∈ gapTuples N x  := by
  ext y
  simp only [mem_filter]
  constructor
  · rintro ⟨hy, h0⟩
    exact ⟨nonnegative_gapTuple_ordered hx hy h0, (mem_filter.mp hy).1⟩
  · rintro ⟨hy, hg⟩
    exact ⟨mem_filter.mpr ⟨hg, orderedTuples_residue_injective hy⟩,
      ((mem_orderedTuples.mp hy).1 0).1⟩

/-- The negative-first gap tuples are precisely the shifted ordinary upper orientation. -/
theorem negative_distinctGapTuples   :
    (distinctGapTuples N x).filter (fun y => ¬ 0 ≤ y 0) =
      ((orderedTuples N (n + 1)).filter
         fun y => cyclicPredecessorPositions N y ∈ gapTuples N x ).image
          (cyclicPredecessorPositions N) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hg, h0⟩ := mem_filter.mp hy
    refine mem_image.mpr ⟨cyclicSuccessorPositions N y, ?_, cyclicPredecessor_successor N y⟩
    exact mem_filter.mpr ⟨negative_gapTuple_successor_ordered hx hg (lt_of_not_ge h0),
      by simpa only [cyclicPredecessor_successor] using (mem_filter.mp hg).1⟩
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    obtain ⟨ho, hg⟩ := mem_filter.mp hz
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hg, ?_⟩, ?_⟩
    · exact (cyclicPredecessor_residue_injective_iff N z).mpr (orderedTuples_residue_injective ho)
    · simp_all

/-- The exact finite cyclic-gap reindexing, for an arbitrary complex summand.
The diagonal has one representative in each of these disjoint sign classes. -/
theorem sum_distinctGapTuples_reindex   (F : (Fin (n + 1) → ℤ) → ℂ) :
     ∑ y ∈ distinctGapTuples N x, F y  =
       ∑ y ∈ (orderedTuples N (n + 1)).filter  fun y => y ∈ gapTuples N x , F y  +
      ∑ y ∈ (orderedTuples N (n + 1)).filter
         fun y => cyclicPredecessorPositions N y ∈ gapTuples N x ,
          F (cyclicPredecessorPositions N y) := by
  rw [← Finset.sum_filter_add_sum_filter_not (distinctGapTuples N x) (fun y => 0 ≤ y 0) F,
    nonnegative_distinctGapTuples hx, negative_distinctGapTuples hx,
    Finset.sum_image (cyclicPredecessorPositions_injective (N := N) (n := n)).injOn]

end

end

end PottsDiscontinuity.BetheAnsatz
