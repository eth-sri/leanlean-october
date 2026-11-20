/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.GradeSplice

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section FullScope

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- Same-scope grade extension for any semantics and any scope. Only the
grade tail is capped; the prescribed lower-grade part stays literal. -/
theorem bountiful_same_scope (sem : Semantics D) {B : Finset ι} {i j : ℕ}
    (h : GradedLe (B, i) (B, j))
    (p : D.below (B, i) → ExtOrd) (q : D.below (B, j) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow sem (B, i) p) (hq : RespectsSemanticsBelow sem (B, j) q)
    (hγ : SelfVis j γ)
    (hag : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ r : D.below (B, j) → ExtOrd, RespectsSemanticsBelow sem (B, j) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, r (CellScheme.below.mono h d) = p d := by
  let u : D.below (B, j) → ExtOrd := fun d => min (q d) γ
  have hu : RespectsSemanticsBelow sem (B, j) u := hq.cap hγ
  have hcap : ∀ d, min (p d) γ =
      min (u (GradeTailRestoration.lowerIncl (BJ := (B, j)) h.2 d)) γ := by
    intro d
    change min (p d) γ = min (min (q (CellScheme.below.mono h d)) γ) γ
    simp_all
  refine ⟨GradeTailRestoration.splice u p,
    GradeTailRestoration.splice_respects h.2 hu hp (fun _ _ => min_le_right _ _) hcap,
    ?_, fun d => GradeTailRestoration.splice_low u p (CellScheme.below.mono h d) d.2.2⟩
  intro d
  exact (GradeTailRestoration.splice_cap h.2 hcap d).trans (by
    dsimp only [u]
    rw [min_assoc, min_self])

end FullScope

end VaughtConjecture.Knight
