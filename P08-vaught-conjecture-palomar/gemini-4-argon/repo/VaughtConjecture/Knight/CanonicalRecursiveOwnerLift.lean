/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
public import VaughtConjecture.Knight.CanonicalOwnerBoundary
public import VaughtConjecture.Knight.RetunedCutDecoding

/-! # Constructed active-owner capped lifting on the recursive successor

Owner alignment and old-face completion run on the current boundary cut.
The complete persistent field inventory is retained before recursive prefix
completion. Arbitrary target-local ambient caps survive at every coordinate.
Literal lower restoration is the next composition step.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveOwnerLift
open Transform Value ExtOrd SharpWitnessComposition CoatomBoundaryExtension CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A)
  (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

theorem exists_owner_capped_lift
    (c : Cell (cut (D := D) n)) (hc : (cut (D := D) n).grade c = n + 4)
    {p : (cut (D := D) n).below ((cut (D := D) n).cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow (cutRows sem n) ((cut (D := D) n).cell c) p)
    {q : CanonicalRecursiveAmbient.target sem n hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem n hA hproper P) (A, n + 4) q)
    {γ : ExtOrd} (hγ : SelfVis (n + 4) γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e, min (p e) γ = min (q (oldTarget sem n hA e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell (cut (D := D) n),
      GradedLe ((cut (D := D) n).cell d) U ∨ GradedLe ((cut (D := D) n).cell d) V)
    (hcU : GradedLe ((cut (D := D) n).cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell (cut (D := D) n), GradedLe ((cut (D := D) n).cell d) U →
      GradedLe ((cut (D := D) n).cell d) V → GradedLe ((cut (D := D) n).cell d) O)
    (hleft : CappedLift (cutRows sem n) hcU) (hright : CappedLift (cutRows sem n) hOV)
    (hU : U.2 ≤ n + 4) (hV : V.2 ≤ n + 4) :
    ∃ r : CanonicalRecursiveAmbient.target sem n hA → ExtOrd,
      RespectsSemanticsBelow (rows sem n hA hproper P) (A, n + 4) r ∧
      (∀ e, r (oldTarget sem n hA e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  have hactive : γ ≤ q (oldTarget sem n hA c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, hτ, hbound, hambient⟩ :=
    CanonicalRecursiveAmbient.exists_capped_source sem n hA hproper P hq
      (oldTarget sem n hA c) ((congrArg Prod.snd (oldTarget_cell sem n hA c)).trans hc)
      hγ hactive
  exact RetunedCutDecoding.owner_capped_lift (occurrence (D := D) n) c hc
    (GradeCutBoundary.grade_bound D (n + 4)) hp hq (fun d => d.2.2) (oldTarget sem n hA)
    hγ hγb hag hpc hcover hcU hOU hOV hinter hleft hright hU hV
    a.property.2 a.property.1 hτ hbound
    ((data sem n hA hproper P).profile_respects (controller sem n hA a))
    (source_short sem n hA hproper P a)
    (fun d => source_boundary sem n hA hproper P a (occurrence (D := D) n d))
    hambient (CanonicalRecursiveCutPrefix.exists_section sem n hA hproper P a)
