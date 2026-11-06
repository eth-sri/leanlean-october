/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopedSourcePrefixLayer
public import VaughtConjecture.Knight.CapFirstScalar

/-! # Arbitrary target-local ambients of a scoped prefix layer

Retained proper owners can have grades above the new controller. Extract one
active source row from an arbitrary lawful full-target ambient.
The existing grade-chart theorem supplies its actual locality witness; clipping
that witness reads every occurrence at the original cap, not merely the top
grade or the original boundary. This is Plan 29's ambient receipt, not a
replacement-section or prescribed-owner alignment theorem.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.ScopedSourcePrefixAmbient

open Transform Value ExtOrd SourcePrefixLayer ScopedSourcePrefixLayer

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
  (F : ScopedSourcePrefixLayer.Data D k X)

theorem exists_active_source (seed : Controller D k)
    {q : D.below (A, k) → ExtOrd} (hq : RespectsSemanticsBelow F.rows (A, k) q)
    (d : D.below (A, k)) (hd : D.grade d.1 = k)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hactive : γ ≤ q d) :
    ∃ (a : Controller D k) (τ : ExtOrd → ExtOrd),
      Witness (gTop k) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : D.below (A, k), τ (F.profile a x.1) = min (q x) γ := by
  obtain ⟨C⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨seed.1, by rw [seed.2]; exact GradedLe.refl _⟩, seed.2⟩
  have hc : γ ≤ q C.owner := hactive.trans (C.dominates d hd)
  refine ⟨⟨C.owner.1, C.index⟩, fun x => min (C.shift x) γ,
    FreeDiagonal.clip_witness C.witness hγ, fun _ => min_le_right _ _, fun x => ?_⟩
  exact (congrArg (fun z => min (C.shift z) γ)
    (F.row_new ⟨C.owner.1, C.index⟩ (C.occurrence x x.2.2)).symm).trans
    (C.read_under_cap hc x x.2.2)
