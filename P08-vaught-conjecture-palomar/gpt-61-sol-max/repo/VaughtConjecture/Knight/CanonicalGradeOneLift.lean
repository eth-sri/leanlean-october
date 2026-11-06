
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalFieldOwnerLift

/-! # Literal grade-one lifting on the canonical complete-field catalogue

The maximizing owner is constructed from actual prescribed availability.
Arbitrary distinct prescribed values and literal top are allowed. Every new
controller's original cap is retained, including controllers distinguished by
fields outside the physical grade-one boundary.
-/

namespace VaughtConjecture.Knight.CanonicalGradeOneLift
open    CanonicalFieldLayer CanonicalFieldOwnerLift
open CoatomBoundaryExtension


variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (X : Type*) [Fintype X] (occ : Cell D → X)
variable (hA : 1 ≤ A.card) (hproper : AvoidsValue D.scope A)
variable (hg : BoundedBy D.grade 1) (hinj : Function.Injective occ)

include hinj

/-- Positive original-cap lifting from an actual proper grade-one face. The
ambient is arbitrary on the actual full grade-one target; only OLD face
lifting clauses are consumed. The inactive branch also covers literal top cap. -/
theorem exists_positive_lift {C : Finset ι}
    (hfull : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    {p : BelowLabels D (C, 1)} (hp : RespectsSemanticsBelow sem (C, 1) p)
    {q : target sem 1 X occ (by decide) hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem 1 X occ (by decide) hA hproper hg) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e , min (p e) γ =
      min (q (oldTarget sem 1 X occ (by decide) hA hproper hg e.1)) γ)
    {U V O : GradedIndex ι}
    (hcover : ∀ d , GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hCU : GradedLe (C, 1) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d , GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hCU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ 1) (hV : V.2 ≤ 1) :
    ∃ r : target sem 1 X occ (by decide) hA → ExtOrd,
      RespectsSemanticsBelow (rows sem 1 X occ (by decide) hA hproper hg) (A, 1) r ∧
      (∀ e , r (oldTarget sem 1 X occ (by decide) hA hproper hg e.1) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp hfull
  have hdom (e : D.below (C, 1)) : p e ≤ p c :=
    hmax e (Nat.le_antisymm (hg e.1) (D.grade_pos e.1))
  by_cases hactive : γ < p c
  · have hc : D.grade c.1 = 1 := congrArg Prod.snd hci
    have hcle : GradedLe (D.cell c.1) (C, 1) := by rw [hci]; exact GradedLe.refl _
    
    have hpc  := hp.mono hcle
    have hcU  := hcle.trans hCU
    have hleftc : CappedLift sem hcU := by simpa only [hci] using hleft
    obtain ⟨r, hr, hread, hcap⟩ := exists_owner_capped_lift sem 1 X occ (by decide) hA
      hproper hg hinj c.1 hc hpc hq hγ hγb (fun e => hag ⟨e.1, e.2.trans hcle⟩)
      hactive hcover hcU hOU hOV hinter hleftc hright hU hV
    refine ⟨r, hr, ?_, hcap⟩
    intro e
    have he : GradedLe (D.cell e.1) (D.cell c.1) := by rw [hci]; exact e.2
    exact (hread ⟨e.1, he⟩).trans (min_eq_left (hdom e))
  · refine ⟨fun d => min (q d) γ, hq.cap hγ, ?_, ?_⟩
    · grind
    · simp_all


