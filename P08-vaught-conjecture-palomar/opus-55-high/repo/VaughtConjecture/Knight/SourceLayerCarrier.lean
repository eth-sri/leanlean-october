/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Sort
public import VaughtConjecture.Knight.VisibleOrderInterpolation
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import Mathlib.Data.Fintype.Lattice
public import VaughtConjecture.Knight.FiniteProfileControllers
public import VaughtConjecture.Knight.SlotControllerFamily
public import VaughtConjecture.Knight.FreshSourceSlots
public import VaughtConjecture.Knight.SourceBlockPadding
public import VaughtConjecture.Knight.FreeDiagonal
public import VaughtConjecture.Knight.SlackCutPasting
public import VaughtConjecture.Knight.SourcePrefixRows
public import VaughtConjecture.Knight.SourcePrefixLayer
public import VaughtConjecture.Knight.AmalgamatedBoundaryRows
public import VaughtConjecture.Knight.FiniteOffset

/-! # Appending a full-scope layer above an actual lower inventory

Unlike the first-grade carrier, inherited owners may already have full scope.
Strictly smaller grade, not proper scope, keeps every new controller out of
their lower domains. All inherited occurrences and their enumeration survive.
-/

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
    · intro d; simpa only [Fin.addCases_left] using D.cell_mem d
    · intro q
      simp only [Fin.addCases_right]
      exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, hk, hA⟩

noncomputable def enumeration : (Cell D ⊕ Q) ≃ Cell (scheme D Q k hk hA) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin Q)).trans finSumFinEquiv

noncomputable def toCell (d : Cell D ⊕ Q) : Cell (scheme D Q k hk hA) :=
  enumeration D Q k hk hA d

noncomputable def toOcc (d : Cell (scheme D Q k hk hA)) : Cell D ⊕ Q :=
  (enumeration D Q k hk hA).symm d

@[simp] theorem toOcc_toCell d :
    toOcc D Q k hk hA (toCell D Q k hk hA d) = d :=
  (enumeration D Q k hk hA).symm_apply_apply d

@[simp] theorem toCell_toOcc d :
    toCell D Q k hk hA (toOcc D Q k hk hA d) = d :=
  (enumeration D Q k hk hA).apply_symm_apply d

def index : Cell D ⊕ Q → Finset ι × ℕ
  | .inl d => D.cell d
  | .inr _ => (A, k)

theorem cell_toCell d :
    (scheme D Q k hk hA).cell (toCell D Q k hk hA d) = index D Q k d := by
  cases d with
  | inl d =>
    change Fin.addCases D.cell (fun _ => (A, k)) (Fin.castAdd (Fintype.card Q) d) = D.cell d
    exact Fin.addCases_left d
  | inr q =>
    change Fin.addCases D.cell (fun _ => (A, k))
      (Fin.natAdd D.card (Fintype.equivFin Q q)) = (A, k)
    exact Fin.addCases_right (Fintype.equivFin Q q)

theorem cell_eq (d : Cell (scheme D Q k hk hA)) :
    (scheme D Q k hk hA).cell d = index D Q k (toOcc D Q k hk hA d) := by
  rw [← cell_toCell, toCell_toOcc]

theorem old_order : StrictMono (fun d => toCell D Q k hk hA (.inl d)) :=
  Fin.strictMono_castAdd _

theorem old_occurrence (d : Cell (scheme D Q k hk hA))
    (hd : (scheme D Q k hk hA).cell d ≠ (A, k)) :
    ∃ x, d = toCell D Q k hk hA (.inl x) := by
  cases he : toOcc D Q k hk hA d with
  | inl x => exact ⟨x, by rw [← he, toCell_toOcc]⟩
  | inr q => exact False.elim (hd (by rw [cell_eq, he]; rfl))

noncomputable def controller (q : Q) :
    SourcePrefixLayer.Controller (scheme D Q k hk hA) k :=
  ⟨toCell D Q k hk hA (.inr q), cell_toCell D Q k hk hA (.inr q)⟩

end VaughtConjecture.Knight.SourceLayerCarrier
