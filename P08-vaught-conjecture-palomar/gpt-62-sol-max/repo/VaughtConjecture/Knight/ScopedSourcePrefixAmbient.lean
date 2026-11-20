/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopedSourcePrefixLayer
public import VaughtConjecture.Knight.CapFirstScalar

@[expose] public section

namespace VaughtConjecture.Knight.ScopedSourcePrefixAmbient

open Transform Value ExtOrd SourcePrefixLayer ScopedSourcePrefixLayer

noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

def atGrade (d : Cell D) (hd : D.grade d ≤ k) : D.below (A, k) :=
  ⟨d, D.scope_subset d, hd⟩

variable (F : ScopedSourcePrefixLayer.Data D k X)

theorem exists_active_source (seed : Controller D k) {q : D.below (A, k) → ExtOrd}
    (hq : RespectsSemanticsBelow F.rows (A, k) q)
    (d : D.below (A, k)) (hd : D.grade d.1 = k)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hactive : γ ≤ q d) :
    ∃ (a : Controller D k) (τ : ExtOrd → ExtOrd),
      Witness (gTop k) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : D.below (A, k), τ (F.profile a x.1) = min (q x) γ := by
  obtain ⟨C⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨seed.1, seed.2.symm ▸ GradedLe.refl _⟩, seed.2⟩
  have hc : γ ≤ q C.owner := hactive.trans (C.dominates d hd)
  refine ⟨⟨C.owner.1, C.index⟩, fun x => min (C.shift x) γ,
    FreeDiagonal.clip_witness C.witness hγ, fun _ => min_le_right _ _, fun x => ?_⟩
  have he := F.row_new ⟨C.owner.1, C.index⟩ (C.occurrence x x.2.2)
  exact (congrArg (fun z => min (C.shift z) γ) he.symm).trans (C.read_under_cap hc x x.2.2)

end

end VaughtConjecture.Knight.ScopedSourcePrefixAmbient
