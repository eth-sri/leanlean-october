
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CappedCore
import VaughtConjecture.Knight.GradeSplice

/-! # Bountifulness between full-scope pairs holds for every semantics

For a cell scheme on `A` and any semantics on it, the instances of Knight's bountifulness
(Def. 2.5.14, `Semantics.IsBountiful`) at pairs `⟨A,i⟩ ≤ ⟨A,j⟩` of **full scope** hold
unconditionally (`bountiful_full_scope`): the extension is `p` on the cells of grade `≤ i` and
`q ∧ γ` on the rest.  Locality at a cell of grade `> i` is the capped locality of `q`
(`TransformsTo.capped`), which agrees with `p` below the cap by the agreement hypothesis;
availability never crosses the grade boundary, since a witness has the grade of its request.

Consequently the content of bountifulness lies entirely in the pairs `⟨C,i⟩ ≺ ⟨B,j⟩` with
`C ⊊ B`; for a scheme assembled over a proper part this is the relabelling obligation of
`Knight/FiniteAssembly.lean`, and its reduction to grade one
(`Family.relabel_iff_gradeOne`) is by this theorem.  Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open Transform  

/-- `TransformsTo` is invariant under propositional equality of its three functions. -/
theorem transformsTo_congr {D : Type*} {g g' : D → ℕ} {p p' q q' : D → ExtOrd} (hg : g = g')
    (hp : p = p') (hq : q = q') (h : TransformsTo g p q) : TransformsTo g' p' q' := by
  subst hg hp hq; exact h

section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

theorem dite_of_pos {c} [Decidable c] {α : Sort*} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := by simp [h]
theorem dite_of_neg {c} [Decidable c] {α : Sort*} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := by simp [h]

/-- Same-scope grade extension for any semantics and any scope. Only the
grade tail is capped; the prescribed lower-grade part stays literal. -/
theorem bountiful_same_scope sem {B} {i j}
    (h : GradedLe (B, i) (B, j))
    p q γ
    (hp : RespectsSemanticsBelow sem (B, i) p) (hq : RespectsSemanticsBelow sem (B, j) q)
    (hγ : SelfVis j γ)
    (hag : ∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ r : BelowLabels D (B, j), RespectsSemanticsBelow sem (B, j) r ∧
      (CappedEq r q γ) ∧
      ∀ d, r (CellScheme.below.mono h d) = p d := by
  let u  := fun d => min (q d) γ
  have hu  := hq.cap hγ
  have hcap : ∀ d, min (p d) γ =
      min (u (GradeTailRestoration.lowerIncl (BJ := (B, j)) h.2 d)) γ := by
    grind [VaughtConjecture.Knight.GradeTailRestoration.lowerIncl, VaughtConjecture.Knight.CellScheme.below.mono]
  refine ⟨GradeTailRestoration.splice u p,
    GradeTailRestoration.splice_respects h.2 hu hp (fun _ _ => min_le_right _ _) hcap,
    ?_, fun d => GradeTailRestoration.splice_low u p (CellScheme.below.mono h d) d.2.2⟩
  intro d
  exact (GradeTailRestoration.splice_cap h.2 hcap d).trans (by
    aesop)


