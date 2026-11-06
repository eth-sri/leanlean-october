/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.ScopedSourcePrefixAmbient

/-! # Arbitrary ambient extraction on the recursive seed

Actual availability chooses a source row; its clipped locality witness reads
the entire target-local cap vector. No canonical-ambient hypothesis or supplied
serving controller is used. Higher proper owners outside the target stay in
the carrier without entering this domain.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CanonicalSeedAmbient

open Transform Value ExtOrd SourcePrefixRows CanonicalRecursiveSeedRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)

private def seed : Profile sem :=
  CanonicalRecursiveInventory.encode sem 0 (p := fun _ => ⊥)
    ((RespectsSemantics.bot sem).toBelow (A, 3)) (fun _ => bot_ne_top)

abbrev target := (carrier sem hA).below (A, 3)

/-- An arbitrary active ambient has a genuine source-family representation
at the original cap, with a constructed first reaching grid cut. -/
theorem exists_capped_source {q : target sem hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem hA hp) (A, 3) q)
    (d : target sem hA)
    (hd : (carrier sem hA).grade d.1 = 3)
    {γ : ExtOrd} (hγ : SelfVis 3 γ) (hb : γ ≠ ⊥) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem) (τ : ExtOrd → ExtOrd) (h : ExtOrd),
      Witness (gTop 3) τ ∧ (∀ x, τ x ≤ γ) ∧
      τ (ceiling (D := D)) = γ ∧
      h ∈ grid (D := D) ∧ SelfVis 3 h ∧ ⊥ < h ∧
      h ≤ ceiling (D := D) ∧ τ h = γ ∧
      (∀ z ∈ grid (D := D), z < h → τ z < γ) ∧
      (∀ x : target sem hA,
        τ (source sem hA hp a x.1) = min (q x) γ) ∧
      RespectsSemanticsBelow (rows sem hA hp) (A, 3)
        (fun x => τ (source sem hA hp a x.1)) := by
  let F := data sem hA hp
  obtain ⟨c, τ, _, hτ, hbound, hC, hread⟩ := ScopedSourcePrefixAmbient.exists_active_source F
    (controller sem hA (seed sem)) hq d hd hγ hactive
  let a := member sem hA hp c
  have ha : controller sem hA a = c :=
    (controllerEquiv sem hA hp).apply_symm_apply c
  have hr (x : target sem hA) :
      τ (source sem hA hp a x.1) = min (q x) γ := by
    change τ (F.profile (controller sem hA a) x.1) = _
    rw [ha]
    exact hread x
  obtain ⟨h, hh, hv, hpos, hc, he, hm⟩ :=
    ScopedSourcePrefixAmbient.exists_first_cut F hτ hb hbound hC
  refine ⟨a, τ, h, hτ, hbound, hC, hh, hv, hpos, hc, he, hm, hr, ?_⟩
  have hf : (fun x : target sem hA =>
      τ (source sem hA hp a x.1)) =
      (fun x => min (q x) γ) := funext hr
  rw [hf]
  exact hq.cap hγ

