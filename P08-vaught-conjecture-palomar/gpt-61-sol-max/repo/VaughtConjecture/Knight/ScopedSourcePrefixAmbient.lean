
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.ScopedSourcePrefixLayer
import VaughtConjecture.Knight.CapFirstScalar

/-! # Arbitrary target-local ambients of a scoped prefix layer

Retained proper owners can have grades above the new controller. Extract one
active source row from an arbitrary lawful full-target ambient.
The existing grade-chart theorem supplies its actual locality witness; clipping
that witness reads every occurrence at the original cap, not merely the top
grade or the original boundary. This is Plan 29's ambient receipt, not a
replacement-section or prescribed-owner alignment theorem.
-/

namespace VaughtConjecture.Knight.ScopedSourcePrefixAmbient

open    SourcePrefixLayer ScopedSourcePrefixLayer


variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
variable (F : ScopedSourcePrefixLayer.Data D k X)

local notation "below₀" => D.below (A, k)

def occurrence (a : Controller D k) : below₀ :=
  ⟨a.1, by rw [a.2]; exact GradedLe.refl _⟩

theorem exists_active_source (seed : Controller D k)
    {q : below₀ → ExtOrd} (hq : RespectsSemanticsBelow F.rows (A, k) q)
    (d : below₀) (hd : D.grade d.1 = k)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hactive : γ ≤ q d) :
    ∃ a τ,
      γ ≤ q (occurrence a) ∧ Witness (gTop k) τ ∧
      (BoundedBy τ γ) ∧ τ F.ceiling = γ ∧
      (∀ x , τ (F.profile a x.1) = min (q x) γ) := by
  obtain ⟨C⟩ := AmbientGradeCharts.exists_chart hq
    ⟨occurrence seed, seed.2⟩
  have hc  := hactive.trans (C.dominates d hd)
  let a : Controller D k := ⟨C.owner.1, C.index⟩
  let τ  := fun x => min (C.shift x) γ
  have hread (x : below₀) : τ (F.profile a x.1) = min (q x) γ := by
    have he := F.row_new a (C.occurrence x x.2.2)
    
    exact (congrArg (fun z => min (C.shift z) γ) he.symm).trans
      (C.read_under_cap hc x x.2.2)
  refine ⟨a, τ, hc, FreeDiagonal.clip_witness C.witness hγ,
    fun _ => min_le_right _ _, ?_, hread⟩
  have he := hread C.owner
  rw [F.profile_diagonal a] at he
  exact he.trans (min_eq_right hc)

/-- The first grid cut reaching the output cap is constructed from the finite
grid. Minimality is only among GRID cuts; unused points inside a strip need not
lie strictly below the output cap. -/
def exists_first_cut {τ} (hτ : Witness (gTop k) τ)
    {γ} (hb : γ ≠ ⊥) (hbound : BoundedBy τ γ) (hC : τ F.ceiling = γ) :=
  CapFirstScalar.first_cut F.grid hτ.bot hb hbound hC
    F.ceiling_mem F.grid_visible F.grid_bound


