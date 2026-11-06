/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedCutPrefix
public import VaughtConjecture.Knight.CanonicalOwnerBoundary
public import VaughtConjecture.Knight.RetunedCutDecoding

/-! # Constructed active-owner capped lifting on the recursive seed

Owner alignment and old-face completion run on the current boundary cut.
The complete persistent field inventory is retained before recursive prefix
completion. Arbitrary target-local ambient caps survive at every coordinate.
Literal lower restoration is the next composition step.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalSeedOwnerLift
open Transform Value ExtOrd SharpWitnessComposition CoatomBoundaryExtension CanonicalRecursiveSeedRows CanonicalSeedCutPrefix

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 3 ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A)

theorem exists_owner_capped_lift
    (c : Cell (cut (D := D))) (hc : (cut (D := D)).grade c = 3)
    {p : (cut (D := D)).below ((cut (D := D)).cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow (cutRows sem) ((cut (D := D)).cell c) p)
    {q : CanonicalSeedAmbient.target sem hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem hA hproper) (A, 3) q)
    {γ : ExtOrd} (hγ : SelfVis 3 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e, min (p e) γ = min (q (oldTarget sem hA e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell (cut (D := D)),
      GradedLe ((cut (D := D)).cell d) U ∨ GradedLe ((cut (D := D)).cell d) V)
    (hcU : GradedLe ((cut (D := D)).cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell (cut (D := D)), GradedLe ((cut (D := D)).cell d) U →
      GradedLe ((cut (D := D)).cell d) V → GradedLe ((cut (D := D)).cell d) O)
    (hleft : CappedLift (cutRows sem) hcU) (hright : CappedLift (cutRows sem) hOV)
    (hU : U.2 ≤ 3) (hV : V.2 ≤ 3) :
    ∃ r : CanonicalSeedAmbient.target sem hA → ExtOrd,
      RespectsSemanticsBelow (rows sem hA hproper) (A, 3) r ∧
      (∀ e, r (oldTarget sem hA e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  have hactive : γ ≤ q (oldTarget sem hA c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, hτ, hbound, hambient⟩ :=
    CanonicalSeedAmbient.exists_capped_source sem hA hproper hq
      (oldTarget sem hA c) ((congrArg Prod.snd (oldTarget_cell sem hA c)).trans hc)
      hγ hactive
  exact RetunedCutDecoding.owner_capped_lift (occurrence (D := D)) c hc
    (GradeCutBoundary.grade_bound D 3) hp hq (fun d => d.2.2) (oldTarget sem hA)
    hγ hγb hag hpc hcover hcU hOU hOV hinter hleft hright hU hV
    a.property.2 a.property.1 hτ hbound
    ((data sem hA hproper).profile_respects (controller sem hA a))
    (source_short sem hA hproper a)
    (fun d => source_boundary sem hA hproper a (occurrence (D := D) d))
    hambient (CanonicalSeedCutPrefix.exists_section sem hA hproper a)
