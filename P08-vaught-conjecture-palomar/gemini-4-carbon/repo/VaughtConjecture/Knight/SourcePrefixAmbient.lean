/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourcePrefixLayer
public import VaughtConjecture.Knight.CapFirstScalar

/-! # Arbitrary target-local ambients of common-prefix layers -/

@[expose] public section

namespace VaughtConjecture.Knight.ScopedSourcePrefixAmbient
open Transform Value ExtOrd SourcePrefixLayer ScopedSourcePrefixLayer
noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
variable (F : ScopedSourcePrefixLayer.Data D k X)

def occurrence (a : Controller D k) : D.below (A, k) :=
  ⟨a.1, by rw [a.2]; exact GradedLe.refl _⟩

theorem exists_active_source (seed : Controller D k)
    {q : D.below (A, k) → ExtOrd} (hq : RespectsSemanticsBelow F.rows (A, k) q)
    (d : D.below (A, k)) (hd : D.grade d.1 = k)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hactive : γ ≤ q d) :
    ∃ (a : Controller D k) (τ : ExtOrd → ExtOrd),
      γ ≤ q (occurrence a) ∧ Witness (gTop k) τ ∧
      (∀ x, τ x ≤ γ) ∧ τ F.ceiling = γ ∧
      (∀ x : D.below (A, k), τ (F.profile a x.1) = min (q x) γ) := by
  obtain ⟨C⟩ := AmbientGradeCharts.exists_chart hq ⟨occurrence seed, seed.2⟩
  have hc : γ ≤ q C.owner := hactive.trans (C.dominates d hd)
  let a : Controller D k := ⟨C.owner.1, C.index⟩
  let τ : ExtOrd → ExtOrd := fun x => min (C.shift x) γ
  have hread (x : D.below (A, k)) : τ (F.profile a x.1) = min (q x) γ :=
    (congrArg (fun z => min (C.shift z) γ) (F.row_new a (C.occurrence x x.2.2)).symm).trans
      (C.read_under_cap hc x x.2.2)
  refine ⟨a, τ, hc, FreeDiagonal.clip_witness C.witness hγ, fun _ => min_le_right _ _, ?_, hread⟩
  have he := hread C.owner
  rw [F.profile_diagonal a] at he
  exact he.trans (min_eq_right hc)



end
end VaughtConjecture.Knight.ScopedSourcePrefixAmbient

namespace VaughtConjecture.Knight.SourcePrefixAmbient
open Transform Value ExtOrd SourcePrefixLayer
noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
variable (F : Data D k X)

def occurrence (d : Cell D) : D.below (A, k) :=
  ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), F.max_grade d⟩

theorem exists_active_source (seed : Controller D k)
    {q : D.below (A, k) → ExtOrd} (hq : RespectsSemanticsBelow F.rows (A, k) q)
    (d : D.below (A, k)) (hd : D.grade d.1 = k)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hactive : γ ≤ q d) :
    ∃ (a : Controller D k) (τ : ExtOrd → ExtOrd),
      γ ≤ q (occurrence F a.1) ∧ Witness (gTop k) τ ∧
      (∀ x, τ x ≤ γ) ∧ τ F.ceiling = γ ∧
      (∀ x : D.below (A, k), τ (F.profile a x.1) = min (q x) γ) :=
  ScopedSourcePrefixAmbient.exists_active_source F.toScoped seed hq d hd hγ hactive



end
end VaughtConjecture.Knight.SourcePrefixAmbient
