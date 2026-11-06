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

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalSeedAmbient

open Transform Value ExtOrd SourcePrefixRows CanonicalRecursiveSeedRows

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 3 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev target := (carrier sem hA).below (A, 3)

theorem exists_capped_source {q : target sem hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem hA hp) (A, 3) q)
    (d : target sem hA) (hd : (carrier sem hA).grade d.1 = 3)
    {γ : ExtOrd} (hγ : SelfVis 3 γ) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem) (τ : ExtOrd → ExtOrd),
      Witness (gTop 3) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : target sem hA, τ (source sem hA hp a x.1) = min (q x) γ := by
  obtain ⟨c, τ, hτ, hbound, hread⟩ := ScopedSourcePrefixAmbient.exists_active_source
    (data sem hA hp)
    (controller sem hA (CanonicalRecursiveInventory.encode sem 0 (p := fun _ => ⊥)
      ((RespectsSemantics.bot sem).toBelow (A, 3)) (fun _ => bot_ne_top)))
    hq d hd hγ hactive
  have ha : controller sem hA (member sem hA hp c) = c :=
    (controllerEquiv sem hA hp).apply_symm_apply c
  refine ⟨member sem hA hp c, τ, hτ, hbound, fun x => ?_⟩
  change τ ((data sem hA hp).profile (controller sem hA (member sem hA hp c)) x.1) = _
  rw [ha]
  exact hread x
