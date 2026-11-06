/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourcePrefixLayer
public import VaughtConjecture.Knight.CapFirstScalar

/-! # The actual capped ambient of a common-prefix layer

Extract one active source row from an arbitrary lawful full-target ambient.
The existing grade-chart theorem supplies its actual locality witness; clipping
that witness reads every occurrence at the original cap, not merely the top
grade or the original boundary. This is Plan 29's ambient receipt, not a
replacement-section or prescribed-owner alignment theorem.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.SourcePrefixAmbient

open Transform Value ExtOrd SourcePrefixLayer

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
  (F : Data D k X)

def occurrence (d : Cell D) : D.below (A, k) :=
  ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), F.max_grade d⟩

theorem exists_active_source (seed : Controller D k)
    {q : D.below (A, k) → ExtOrd} (hq : RespectsSemanticsBelow F.rows (A, k) q)
    (d : D.below (A, k)) (hd : D.grade d.1 = k)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hactive : γ ≤ q d) :
    ∃ (a : Controller D k) (τ : ExtOrd → ExtOrd),
      Witness (gTop k) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : D.below (A, k), τ (F.profile a x.1) = min (q x) γ := by
  obtain ⟨C⟩ := AmbientGradeCharts.exists_chart hq ⟨occurrence F seed.1, seed.2⟩
  have hc : γ ≤ q C.owner := hactive.trans (C.dominates d hd)
  refine ⟨⟨C.owner.1, C.index⟩, fun x => min (C.shift x) γ,
    FreeDiagonal.clip_witness C.witness hγ, fun _ => min_le_right _ _, fun x => ?_⟩
  exact (congrArg (fun z => min (C.shift z) γ)
    (F.row_new ⟨C.owner.1, C.index⟩ (C.occurrence x (F.max_grade x.1))).symm).trans
    (C.read_under_cap hc x (F.max_grade x.1))
