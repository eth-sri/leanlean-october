module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
Adapted from Vilin97/homotopy-groups-lean, commit
c66523531ff172d7f41913d94e56921e790a1b47; isolated geometry for Lean 4.28.0.
-/
public import RequestProject.TopologicalSingular.SimplexFaceCoordinates

@[expose] public section

/-!
# Retraction of a simplex onto a horn

For a chosen face `i` of a simplex, subtract the least barycentric coordinate away from `i`
from every coordinate away from `i`, and transfer the removed mass to coordinate `i`.  The
result lies in the horn obtained by deleting face `i`: at least one of the other coordinates is
zero.  This gives an explicit continuous retraction of the simplex onto that horn.

The straight-line homotopy to this retraction fixes the horn pointwise.  In particular, on the
missing face it fixes the whole boundary.  This is the geometric reduction used to replace one
face of a normalized simplex boundary by its attaching map through all the other faces.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace FiniteChains.TopologicalSingular

variable {d : ℕ}

variable (i : Fin (d + 2))

variable (z : stdSimplex ℝ (Fin (d + 2)))

/-- The least barycentric coordinate away from `i`. -/
def simplexHornMin :=
  Finset.univ.inf' Finset.univ_nonempty fun j : Fin _ ↦ z.1 (i.succAbove j)

theorem simplexHornMin_nonneg : 0 ≤ simplexHornMin i z := by
  apply Finset.le_inf' Finset.univ_nonempty
  intro j hj
  apply z.2.1

theorem simplexHornMin_le (j : Fin _) :
    simplexHornMin i z ≤ z.1 (i.succAbove j) :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem exists_simplexHornMin_eq :
    ∃ j : Fin _, simplexHornMin i z = z.1 (i.succAbove j) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j ↦ z.1 (i.succAbove j)) <;> aesop

/-- The least coordinate away from the chosen face varies continuously. -/
theorem continuous_simplexHornMin :
    Continuous (simplexHornMin i) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun j _ ↦ (continuous_apply (i.succAbove j)).comp continuous_subtype_val)

variable (z : stdSimplex ℝ (Fin (d + 2)))

/-- Barycentric coordinates of the retraction onto the horn opposite face `i`. -/
def simplexHornRetractCoords : Fin (d + 2) → ℝ :=
  i.insertNth (z.1 i + (d + 1) * simplexHornMin i z)
    (fun j ↦ z.1 (i.succAbove j) - simplexHornMin i z)

@[simp]
theorem simplexHornRetractCoords_same :
    simplexHornRetractCoords i z i = z.1 i + (d + 1) * simplexHornMin i z := by
  simp [simplexHornRetractCoords]

@[simp]
theorem simplexHornRetractCoords_succAbove (j : Fin _) :
    simplexHornRetractCoords i z (i.succAbove j) =
      z.1 (i.succAbove j) - simplexHornMin i z := by
  simp [simplexHornRetractCoords]

theorem simplexHornRetractCoords_nonneg (k : Fin _) :
    0 ≤ simplexHornRetractCoords i z k := by
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
  · rw [simplexHornRetractCoords_same]
    exact add_nonneg (z.2.1 i)
      (mul_nonneg (by positivity) (simplexHornMin_nonneg i z))
  · simp_all [simplexHornRetractCoords_succAbove, simplexHornMin_le]

theorem sum_simplexHornRetractCoords :
    ∑ k, simplexHornRetractCoords i z k = 1 := by
  rw [Fin.sum_univ_succAbove _ i]
  have hz := z.2.2; rw [Fin.sum_univ_succAbove _ i] at hz; norm_num at hz ⊢; linarith

/-- The explicit retraction of a simplex onto the horn obtained by deleting face `i`. -/
def simplexHornRetract :
    C(stdSimplex ℝ (Fin (d + 2)), stdSimplex ℝ (Fin (d + 2))) where
  toFun z := ⟨simplexHornRetractCoords i z,
    simplexHornRetractCoords_nonneg i z, sum_simplexHornRetractCoords i z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
    · simp only [simplexHornRetractCoords_same]
      apply Continuous.add
      · exact (continuous_apply i).comp continuous_subtype_val
      · exact continuous_const.mul (continuous_simplexHornMin i)
    · simp only [simplexHornRetractCoords_succAbove]
      exact ((continuous_apply (i.succAbove j)).comp continuous_subtype_val).sub
        (continuous_simplexHornMin i)

@[simp]
theorem simplexHornRetract_apply_coe
    (z : stdSimplex ℝ (Fin _)) (k : Fin _) :
    (simplexHornRetract i z).1 k = simplexHornRetractCoords i z k :=
  rfl

/-- The horn opposite `i`, described as the points having a zero coordinate away from `i`. -/
def simplexHorn : Set (stdSimplex ℝ (Fin (d + 2))) :=
  {z | ∃ j : Fin _, z.1 (i.succAbove j) = 0}

variable {z : stdSimplex ℝ (Fin (d + 2))} (hz : z ∈ simplexHorn i)
include hz

theorem simplexHornMin_eq_zero_of_mem :
    simplexHornMin i z = 0 := by
  obtain ⟨j, hj⟩ := hz
  grind [simplexHornMin_le, simplexHornMin_nonneg]

theorem simplexHornRetract_eq_self_of_mem :
    simplexHornRetract i z = z := by
  apply Subtype.ext
  funext k
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
  · simp_all [simplexHornRetractCoords, simplexHornMin_eq_zero_of_mem]
  · simp_all [simplexHornRetractCoords, simplexHornMin_eq_zero_of_mem]

end FiniteChains.TopologicalSingular
