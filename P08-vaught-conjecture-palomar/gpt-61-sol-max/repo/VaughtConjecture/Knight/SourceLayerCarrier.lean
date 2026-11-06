/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import Mathlib.Data.Finset.Sort
import VaughtConjecture.Knight.VisibleOrderInterpolation
import VaughtConjecture.Knight.SourceBlockLocalityTransport
import Mathlib.Data.Fintype.Lattice
import VaughtConjecture.Knight.FiniteProfileControllers
import VaughtConjecture.Knight.SlotControllerFamily
import VaughtConjecture.Knight.SeparatedGradeOneCoding
import VaughtConjecture.Knight.MixedGradeInterpolation
import VaughtConjecture.Knight.FreeDiagonal
import VaughtConjecture.Knight.SourceBlockPadding
import VaughtConjecture.Knight.SlackCutPasting
import VaughtConjecture.Knight.SourcePrefixRows
import VaughtConjecture.Knight.SourcePrefixLayer
import VaughtConjecture.Knight.AmalgamatedBoundaryRows
import VaughtConjecture.Knight.FiniteOffset

/-! # Appending a full-scope layer above an actual lower inventory

Unlike the first-grade carrier, inherited owners may already have full scope.
Strictly smaller grade, not proper scope, keeps every new controller out of
their lower domains. All inherited occurrences and their enumeration survive.
-/

namespace VaughtConjecture.Knight.SourceLayerCarrier

open AmalgamationPlan   

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

local notation "scheme₀" => scheme D Q k hk hA

variable {D Q k hk hA} in
noncomputable def enumeration : (Cell D ⊕ Q) ≃ Cell (scheme₀) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin Q)).trans finSumFinEquiv

local notation "enumeration₀" => enumeration (D := D) (Q := Q) (k := k) (hk := hk) (hA := hA)

noncomputable def toCell d :=
  enumeration₀ d

noncomputable def toOcc d :=
  (enumeration₀).symm d

local notation "toCell₀" => toCell D Q k hk hA

local notation "toOcc₀" => toOcc D Q k hk hA

@[simp] theorem toOcc_toCell d :
    toOcc₀ (toCell₀ d) = d :=
  (enumeration₀).symm_apply_apply d

variable {D Q k hk hA} in
@[simp] theorem toCell_toOcc d :
    toCell₀ (toOcc₀ d) = d :=
  (enumeration₀).apply_symm_apply d

def index : Cell D ⊕ Q → GradedIndex ι
  | .inl d => D.cell d
  | .inr _ => (A, k)

theorem cell_toCell d :
    (scheme₀).cell (toCell₀ d) = index D Q k d := by
  cases d with
  | inl d =>
    change Fin.addCases D.cell (fun _ => (A, k)) (Fin.castAdd (Fintype.card Q) d) = D.cell d
    exact Fin.addCases_left d
  | inr q =>
    change Fin.addCases D.cell (fun _ => (A, k))
      (Fin.natAdd D.card (Fintype.equivFin Q q)) = (A, k)
    exact Fin.addCases_right (Fintype.equivFin Q q)

theorem cell_eq d :
    (scheme₀).cell d = index D Q k (toOcc₀ d) := by
  rw [← cell_toCell, toCell_toOcc]

variable {Q k} in
variable {D hk hA} in
theorem old_order : StrictMono (fun d => toCell₀ (.inl d)) :=
  Fin.strictMono_castAdd _

theorem old_occurrence d
    (hd : (scheme₀).cell d ≠ (A, k)) :
    ∃ x , d = toCell₀ (.inl x) := by
  cases he : toOcc₀ d with
  | inl x => grind [toCell_toOcc]
  | inr q => exact False.elim (hd (by rw [cell_eq, he]; rfl))

noncomputable def controller (q : Q) :
    SourcePrefixLayer.Controller (scheme₀) k :=
  ⟨toCell₀ (.inr q), cell_toCell D Q k hk hA (.inr q)⟩

