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

@[expose] public section

namespace VaughtConjecture.Knight.SourcePrefixAmbient

open Transform Value ExtOrd SourcePrefixLayer
noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
variable (F : Data D k X)

/-- Select an active controller in any atlas whose controller rows read its profiles. -/
theorem cappedProfile {sem : Semantics D} (e : X ≃ Controller D k) (seed : X)
    {profile : Controller D k → Cell D → ExtOrd}
    (row : ∀ c (y : D.below (D.cell c.1)), sem.E c.1 y = profile c y.1)
    {q} (hq : RespectsSemanticsBelow sem (A, k) q)
    d (hd : D.grade d.1 = k)
    {γ} (hγ : SelfVis k γ) (hactive : γ ≤ q d) :
    ∃ a τ, Witness (gTop k) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : D.below (A, k), τ (profile (e a) x.1) = min (q x) γ := by
  obtain ⟨C⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨(e seed).1, by rw [(e seed).2]; exact GradedLe.refl _⟩, (e seed).2⟩
  let c : Controller D k := ⟨C.owner.1, C.index⟩
  refine ⟨e.symm c, fun z => min (C.shift z) γ, FreeDiagonal.clip_witness C.witness hγ,
    fun _ => min_le_right _ _, fun x => ?_⟩
  rw [e.apply_symm_apply]
  exact (congrArg (fun z => min (C.shift z) γ) (row c (C.occurrence x x.2.2)).symm).trans
    (C.read_under_cap (hactive.trans (C.dominates d hd)) x x.2.2)

end
end VaughtConjecture.Knight.SourcePrefixAmbient
