/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedCore
public import VaughtConjecture.Knight.GradeSplice

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

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- `TransformsTo` is invariant under propositional equality of its three functions. -/
theorem transformsTo_congr {D : Type*} {g g' : D → ℕ} {p p' q q' : D → ExtOrd} (hg : g = g')
    (hp : p = p') (hq : q = q') (h : TransformsTo g p q) : TransformsTo g' p' q' := by
  simp_all

section FullScope

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

theorem dite_of_pos {c : Prop} [Decidable c] {α : Sort*} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := by simp_all

/-- Same-scope grade extension for any semantics and any scope. Only the
grade tail is capped; the prescribed lower-grade part stays literal. -/
theorem bountiful_same_scope (sem : Semantics D) {B : Finset ι} {i j : ℕ}
    (h : GradedLe (B, i) (B, j))
    (p : D.SectionAt (B, i)) (q : D.SectionAt (B, j)) (γ : ExtOrd)
    (hp : sem.Lawful p) (hq : sem.Lawful q)
    (hγ : SelfVis j γ)
    (hag : CappedEq (q ∘ CellScheme.below.mono h) p γ) :
    ∃ r : D.SectionAt (B, j), sem.Lawful r ∧
      CappedEq r q γ ∧
      ∀ d, r (CellScheme.below.mono h d) = p d := by
  let u := fun d => min (q d) γ
  have hu := hq.cap hγ
  have hcap : CappedEq p (u ∘ GradeTailRestoration.lowerIncl (BJ := (B, j)) h.2) γ := by
    intro d
    change min (p d) γ = min (min (q (CellScheme.below.mono h d)) γ) γ
    rw [min_assoc, min_self]
    exact (hag d).symm
  refine ⟨GradeTailRestoration.splice u p,
    GradeTailRestoration.splice_respects h.2 hu hp (fun _ _ => min_le_right _ _) hcap,
    ?_, fun d => GradeTailRestoration.splice_low u p (CellScheme.below.mono h d) d.2.2⟩
  intro d
  exact (GradeTailRestoration.splice_cap h.2 hcap d).trans (by
    grind)

end FullScope

end VaughtConjecture.Knight
