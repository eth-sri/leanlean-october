/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.PaddedOwnerRepair

/-! # Constructed active-owner capped lifting on the recursive successor

Owner alignment and old-face completion run on the current boundary cut.
The complete persistent field inventory is retained before recursive prefix
completion. Arbitrary target-local ambient caps survive at every coordinate.
Literal lower restoration is the next composition step.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveOwnerLift
open Transform Value ExtOrd SharpWitnessComposition CoatomBoundaryExtension
open CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 1 ≤ A.card)
variable (hproper : D.AvoidsScope A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

theorem exists_owner_capped_lift
    (c : Cell (cut (D := D) n)) (hc : (cut (D := D) n).grade c = n + 1)
    {p : (cut (D := D) n).RowDomain c → ExtOrd}
    (hp : (cutRows sem n).Lawful p)
    {q}
    (hq : RespectsSemanticsBelow (rows sem n hA hproper P) (A, n + 1) q)
    {γ} (hγ : SelfVis (n + 1) γ) (hγb : γ ≠ ⊥)
    (hag : CappedEq p (q ∘ oldTarget sem n hA ∘ Subtype.val) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O}
    (hcover : ∀ d : Cell (cut (D := D) n),
      GradedLe ((cut (D := D) n).cell d) U ∨ GradedLe ((cut (D := D) n).cell d) V)
    (hcU : GradedLe ((cut (D := D) n).cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell (cut (D := D) n), GradedLe ((cut (D := D) n).cell d) U →
      GradedLe ((cut (D := D) n).cell d) V → GradedLe ((cut (D := D) n).cell d) O)
    (hleft : CappedLift (cutRows sem n) hcU) (hright : CappedLift (cutRows sem n) hOV)
    (hU : U.2 ≤ n + 1) (hV : V.2 ≤ n + 1) :
    ∃ r,
      RespectsSemanticsBelow (rows sem n hA hproper P) (A, n + 1) r ∧
      (∀ e, r (oldTarget sem n hA e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      CappedEq r q γ := by
  have hactive : γ ≤ q (oldTarget sem n hA c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, hτ, hbound, hambient⟩ :=
    CanonicalRecursiveAmbient.exists_capped_source sem n hA hproper P hq
      (oldTarget sem n hA c) ((congrArg Prod.snd (oldTarget_cell sem n hA c)).trans hc)
      hγ hactive
  let inc := fun e : (cut (D := D) n).RowDomain c => oldTarget sem n hA e.1
  refine PrivateRowFactorization.repairOwner ⟨c,GradedLe.refl _⟩ rfl hc inc
    (a.property.1.toBelow _) hp hq (t := fun d => source sem n hA hproper P a d.1)
    (fun e => source_boundary sem n hA hproper P a _) (fun e => CanonicalPairedProfiles.inventory_coded _ _ a.property.2 _)
    (fun d => source_short sem n hA hproper P a d.1) hτ hγ (bot_lt_iff_ne_bot.mpr hγb) hpc
    (fun d => (min_eq_left (hbound _)).trans (hambient d)) (fun e => (hag e).symm) ?_
  intro b hb v hv heq
  have hvis := CanonicalPairedInverse.grid_visible (n+1) b
  obtain ⟨u,hu,hpre,hr⟩ := extend_boundary hcover hcU hOU hOV hinter hleft hright a.property.1
    hv (selfVis_mono hvis hU) (selfVis_mono hvis hV) heq
  obtain ⟨w,hw,hread,hcap⟩ := CanonicalRecursiveCutPrefix.exists_section sem n hA hproper P a hu hb (fun d => (hpre d).symm)
  exact ⟨_,hw,fun e => (hread e.1).trans (hr e),fun d => hcap d.1⟩

end
end VaughtConjecture.Knight.CanonicalRecursiveOwnerLift
