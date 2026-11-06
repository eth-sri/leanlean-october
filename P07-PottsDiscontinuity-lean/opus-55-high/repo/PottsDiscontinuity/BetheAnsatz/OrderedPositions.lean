module

public import PottsDiscontinuity.BetheAnsatz.GapGeometry

/-!
# Finite ordered integer coordinates for row states

This is the finite reindexing between an actual n-particle row state and its unique
strictly increasing coordinates in `[0,N)`. Its inverse uses the coordinates themselves,
with no arbitrary choice of enumeration.
-/

public section

open Finset Classical

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

/-- All increasing n-tuples of integer positions in the zero-based row. -/
def orderedTuples (N n : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset (fun _ : Fin n => Ico (0 : ℤ) N)).filter StrictMono

section
variable {N n : ℕ}
@[simp] theorem mem_orderedTuples {y : Fin n → ℤ} :
    y ∈ orderedTuples N n ↔ (∀ k, 0 ≤ y k ∧ y k < N) ∧ StrictMono y := by
  simp only [orderedTuples, mem_filter, Fintype.mem_piFinset, mem_Ico]

theorem positions_mem_orderedTuples (x : State N n) :
    positions x ∈ orderedTuples N n := by
  refine mem_orderedTuples.mpr ⟨?_, positions_strictMono x⟩
  simp [positions]

/-- A coordinate viewed in `Fin N`, using the proved bounds of the ordered tuple. -/
def tuplePosition (y : Fin n → ℤ) (hy : y ∈ orderedTuples N n) (k : Fin n) : Fin N :=
  ⟨(y k).toNat, by simp_all⟩
end

section
variable {N n : ℕ} (y : Fin n → ℤ) (hy : y ∈ orderedTuples N n)
@[simp] theorem tuplePosition_val_int (k : Fin n) : (tuplePosition y hy k).val = y k :=
  Int.toNat_of_nonneg ((mem_orderedTuples.mp hy).1 k).1

theorem tuplePosition_strictMono  : StrictMono (tuplePosition y hy) := by
  intro i j hij
  have h := (mem_orderedTuples.mp hy).2 hij
  grind [tuplePosition_val_int, tuplePosition]

/-- The row state represented by a bounded increasing integer tuple. -/
def stateOfTuple  : State N n :=
  ⟨univ.image (tuplePosition y hy), by
    rw [card_image_of_injective _ (tuplePosition_strictMono y hy).injective, card_univ, Fintype.card_fin]⟩

@[simp] theorem positions_stateOfTuple  : positions (stateOfTuple y hy) = y := by
  have hsort : tuplePosition y hy =
      (stateOfTuple y hy).1.orderEmbOfFin (stateOfTuple y hy).2 :=
    Finset.orderEmbOfFin_unique _ (fun k => mem_image.mpr ⟨k, mem_univ k, rfl⟩)
      (tuplePosition_strictMono y hy)
  funext k
  change (((stateOfTuple y hy).1.orderEmbOfFin (stateOfTuple y hy).2 k).val : ℤ) = y k
  rw [← hsort]
  exact tuplePosition_val_int y hy k
end

section
variable {N n : ℕ}
include n
theorem positions_injective  : Function.Injective (positions (N := N) (n := n)) := by
  intro x y he
  have hemb : (x.1.orderEmbOfFin x.2 : Fin n → Fin N) = y.1.orderEmbOfFin y.2 := by
    funext k
    apply Fin.ext
    have h := congrFun he k
    simp_all [positions]
  apply Subtype.ext
  rw [← image_orderEmbOfFin_univ x.1 x.2, ← image_orderEmbOfFin_univ y.1 y.2, hemb]


/-- Reindex a sum over the actual sector by its unique increasing coordinate tuples. -/
theorem sum_states_eq_sum_orderedTuples (F : (Fin n → ℤ) → ℂ) :
    (∑ x : State N n, F (positions x)) = ∑ y ∈ orderedTuples N n, F y := by
  apply Finset.sum_bij (fun x _ => positions x)
  · grind [positions_mem_orderedTuples]
  · grind [positions_injective]
  · intro y hy
    exact ⟨stateOfTuple y hy, mem_univ _, positions_stateOfTuple y hy⟩
  simp
end

end PottsDiscontinuity.BetheAnsatz
