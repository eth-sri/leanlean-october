/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CellBelowEquiv
public import Mathlib.Data.Finset.Sort
public import VaughtConjecture.Knight.VisibleOrderInterpolation
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import Mathlib.Data.Fintype.Lattice
public import VaughtConjecture.Knight.FiniteProfileControllers
public import VaughtConjecture.Knight.SlotControllerFamily
public import VaughtConjecture.Knight.FreshSourceSlots
public import VaughtConjecture.Knight.SourceBlockPadding
public import VaughtConjecture.Knight.FreeDiagonal
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.SourcePrefixRows
public import VaughtConjecture.Knight.ScopedSourcePrefixLayer
public import VaughtConjecture.Knight.OrderedFaceBoundaryRows
public import VaughtConjecture.Knight.FiniteOffset

@[expose] public section

namespace VaughtConjecture.Knight.SourceLayerCarrier

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (Q : Type*) [Fintype Q] (k : ℕ)

variable (hk : 0 < k) (hA : k ≤ A.card)

noncomputable def scheme : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := D.card + Fintype.card Q
  cell := Fin.addCases D.cell (fun _ => (A, k))
  cell_mem c := by
    refine Fin.addCases ?_ ?_ c
    · intro d; simpa [Fin.addCases_left] using D.cell_mem d
    · intro q
      simp only [Fin.addCases_right]
      exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, hk, hA⟩

noncomputable def enumeration : (Cell D ⊕ Q) ≃ Cell (scheme D Q k hk hA) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin Q)).trans finSumFinEquiv

noncomputable def toCell (d : Cell D ⊕ Q) : Cell (scheme D Q k hk hA) :=
  enumeration D Q k hk hA d

noncomputable def toOcc (d : Cell (scheme D Q k hk hA)) : Cell D ⊕ Q :=
  (enumeration D Q k hk hA).symm d

@[simp] theorem toOcc_toCell (d : Cell D ⊕ Q) :
    toOcc D Q k hk hA (toCell D Q k hk hA d) = d :=
  (enumeration D Q k hk hA).symm_apply_apply d

@[simp] theorem toCell_toOcc (d : Cell (scheme D Q k hk hA)) :
    toCell D Q k hk hA (toOcc D Q k hk hA d) = d :=
  (enumeration D Q k hk hA).apply_symm_apply d

def index : Cell D ⊕ Q → Finset ι × ℕ
  | .inl d => D.cell d
  | .inr _ => (A, k)

theorem cell_toCell (d : Cell D ⊕ Q) :
    (scheme D Q k hk hA).cell (toCell D Q k hk hA d) = index D Q k d := by
  cases d with
  | inl d =>
    change Fin.addCases D.cell (fun _ => (A, k)) (Fin.castAdd (Fintype.card Q) d) = D.cell d
    exact Fin.addCases_left d
  | inr q =>
    change Fin.addCases D.cell (fun _ => (A, k))
      (Fin.natAdd D.card (Fintype.equivFin Q q)) = (A, k)
    simp

theorem cell_eq (d : Cell (scheme D Q k hk hA)) :
    (scheme D Q k hk hA).cell d = index D Q k (toOcc D Q k hk hA d) := by
  rw [← cell_toCell, toCell_toOcc]

theorem old_order : StrictMono (fun d : Cell D => toCell D Q k hk hA (.inl d)) :=
  Fin.strictMono_castAdd _

theorem old_occurrence (d : Cell (scheme D Q k hk hA))
    (hd : (scheme D Q k hk hA).cell d ≠ (A, k)) :
    ∃ x : Cell D, d = toCell D Q k hk hA (.inl x) := by
  cases he : toOcc D Q k hk hA d with
  | inl x => exact ⟨x, by rw [← he, toCell_toOcc]⟩
  | inr q => exact False.elim (hd (by rw [cell_eq, he]; rfl))

/-- A lower domain not containing the added index consists precisely of old cells. -/
noncomputable def inheritedEquiv (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, k) J) :
    D.below J ≃ (scheme D Q k hk hA).below J :=
  CellScheme.belowEquivOfIndex (fun d => toCell D Q k hk hA (.inl d))
    (old_order D Q k hk hA).injective (fun d => cell_toCell D Q k hk hA (.inl d))
    (fun d hd => by
      obtain ⟨x, hx⟩ := old_occurrence D Q k hk hA d (fun he => hJ (he ▸ hd))
      exact ⟨x, hx.symm⟩)

noncomputable def controller (q : Q) :
    SourcePrefixLayer.Controller (scheme D Q k hk hA) k :=
  ⟨toCell D Q k hk hA (.inr q), cell_toCell D Q k hk hA (.inr q)⟩

theorem inheritedEquiv_cell (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, k) J) (d : D.below J) :
    (scheme D Q k hk hA).cell (inheritedEquiv D Q k hk hA J hJ d).1 = D.cell d.1 :=
  cell_toCell _ _ _ _ _ (.inl d.1)

section AppendMap

variable {D} {E : CellScheme A}

/-- Extend an occurrence embedding by the identity on a new full-scope layer. -/
noncomputable def appendMap (f : Cell D ↪ Cell E) : Cell (scheme D Q k hk hA) ↪ Cell (scheme E Q k hk hA) :=
  ⟨fun d => toCell E Q k hk hA (Sum.map f id (toOcc D Q k hk hA d)),
    fun _ _ h => (enumeration D Q k hk hA).symm.injective
      ((Sum.map_injective.mpr ⟨f.injective, Function.injective_id⟩)
        ((enumeration E Q k hk hA).injective h))⟩

@[simp] theorem appendMap_toCell (f : Cell D ↪ Cell E) (d : Cell D ⊕ Q) :
    appendMap Q k hk hA f (toCell D Q k hk hA d) = toCell E Q k hk hA (Sum.map f id d) := by
  change toCell E Q k hk hA (Sum.map f id (toOcc D Q k hk hA (toCell D Q k hk hA d))) = _
  rw [toOcc_toCell]

theorem appendMap_index (f : Cell D ↪ Cell E) (hf : ∀ d, E.cell (f d) = D.cell d)
    (d : Cell (scheme D Q k hk hA)) :
    (scheme E Q k hk hA).cell (appendMap Q k hk hA f d) = (scheme D Q k hk hA).cell d := by
  obtain ⟨d, rfl⟩ := (enumeration D Q k hk hA).surjective d
  change (scheme E Q k hk hA).cell (appendMap Q k hk hA f (toCell D Q k hk hA d)) =
    (scheme D Q k hk hA).cell (toCell D Q k hk hA d)
  rw [appendMap_toCell, cell_toCell, cell_toCell]
  cases d with
  | inl d => exact hf d
  | inr _ => rfl

theorem appendMap_exhaustive (f : Cell D ↪ Cell E) {J : ℕ}
    (hf : ∀ d : Cell E, E.grade d ≤ J → ∃ c, f c = d)
    (d : Cell (scheme E Q k hk hA)) (hd : (scheme E Q k hk hA).grade d ≤ J) :
    ∃ c, appendMap Q k hk hA f c = d := by
  obtain ⟨d, rfl⟩ := (enumeration E Q k hk hA).surjective d
  change (scheme E Q k hk hA).grade (toCell E Q k hk hA d) ≤ J at hd
  rcases d with d | q
  · obtain ⟨c, rfl⟩ := hf d (by simpa only [CellScheme.grade, cell_toCell, index] using hd)
    exact ⟨toCell D Q k hk hA (.inl c), appendMap_toCell Q k hk hA f _⟩
  · exact ⟨toCell D Q k hk hA (.inr q), appendMap_toCell Q k hk hA f _⟩

end AppendMap

theorem grade_bound {J : ℕ} (hD : ∀ d : Cell D, D.grade d ≤ J) (hkJ : k ≤ J)
    (d : Cell (scheme D Q k hk hA)) : (scheme D Q k hk hA).grade d ≤ J := by
  rw [CellScheme.grade, cell_eq]
  cases toOcc D Q k hk hA d with
  | inl d => exact hD d
  | inr _ => exact hkJ

end VaughtConjecture.Knight.SourceLayerCarrier
