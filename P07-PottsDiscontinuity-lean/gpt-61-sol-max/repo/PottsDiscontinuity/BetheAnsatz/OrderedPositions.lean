module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.GapGeometry

/-!
# Finite ordered integer coordinates for row states

This is the finite reindexing between an actual n-particle row state and its unique
strictly increasing coordinates in `[0,N)`. Its inverse uses the coordinates themselves,
with no arbitrary choice of enumeration.
-/

@[expose] public section

open Finset Classical

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

/-- All increasing n-tuples of integer positions in the zero-based row. -/
def orderedTuples (N n : ℕ)  :=
  (Fintype.piFinset  fun _ : Fin n => Ico (0 : ℤ) N ).filter StrictMono

@[simp] theorem mem_orderedTuples {N n : ℕ} {y : Fin n → ℤ} :
    y ∈ orderedTuples N n ↔ (∀ k, 0 ≤ y k ∧ y k < N) ∧ StrictMono y := by
  grind +locals

theorem positions_mem_orderedTuples {N n : ℕ} (x : State N n) :
    positions x ∈ orderedTuples N n := by
  refine mem_orderedTuples.mpr ⟨?_, positions_strictMono x⟩
  
  
  unfold positions
  omega

/-- A coordinate viewed in `Fin N`, using the proved bounds of the ordered tuple. -/
def tuplePosition {N n : ℕ} (y : Fin n → ℤ) (hy : y ∈ orderedTuples N n) (k : Fin n) : Fin N :=
  ⟨(y k).toNat, by simp_all⟩

section

variable {N n : ℕ} (y : Fin n → ℤ) (hy : y ∈ orderedTuples N n)


@[simp] theorem tuplePosition_val_int  (k : Fin n) : (tuplePosition y hy k).val = y k := by
  grind +locals

theorem tuplePosition_strictMono  : StrictMono (tuplePosition y hy) := by
  intro i j hij
  have h := (mem_orderedTuples.mp hy).2 hij
  have hi := tuplePosition_val_int y hy i
  have hj := tuplePosition_val_int y hy j
  grind

end

/-- The row state represented by a bounded increasing integer tuple. -/
def stateOfTuple {N n : ℕ} (y : Fin n → ℤ) (hy : y ∈ orderedTuples N n) : State N n :=
  ⟨univ.image (tuplePosition y hy), by
    rw [card_image_of_injective _ (tuplePosition_strictMono y hy).injective, card_univ, Fintype.card_fin]⟩

section

variable {N n : ℕ}


@[simp] theorem positions_stateOfTuple  (y : Fin n → ℤ)
    (hy : y ∈ orderedTuples N n) : positions (stateOfTuple y hy) = y := funext fun k =>
                                                                          Eq.mpr
                                                                            (congrArg (fun _a => ↑↑(_a k) = y k)
                                                                              (Eq.symm
                                                                                (orderEmbOfFin_unique (stateOfTuple y hy).property (fun k => mem_image.mpr (Exists.intro k ⟨mem_univ k, rfl⟩))
                                                                                  (tuplePosition_strictMono y hy))))
                                                                            (tuplePosition_val_int y hy k)

theorem positions_injective  : Function.Injective (positions (N := N) (n := n)) := by
  intro x y he
  have hemb : (x.1.orderEmbOfFin x.2 : Fin n → Fin N) = y.1.orderEmbOfFin y.2 := by
    funext k
    apply Fin.ext
    have h := congrFun he k
    unfold positions at h
    exact_mod_cast h
  apply Subtype.ext
  rw [← image_orderEmbOfFin_univ x.1 x.2, ← image_orderEmbOfFin_univ y.1 y.2, hemb]



/-- Reindex a sum over the actual sector by its unique increasing coordinate tuples. -/
theorem sum_states_eq_sum_orderedTuples  (F : (Fin n → ℤ) → ℂ) :
     ∑ x : State N n, F (positions x)  = ∑ y ∈ orderedTuples N n, F y := by
  apply Finset.sum_bij  fun x _ => positions x 
  · intro x _
    exact positions_mem_orderedTuples x
  · intro x _ y _ he
    exact positions_injective he
  · intro y hy
    exact ⟨stateOfTuple y hy, mem_univ _, positions_stateOfTuple y hy⟩
  · intro x _
    rfl

end

end PottsDiscontinuity.BetheAnsatz
