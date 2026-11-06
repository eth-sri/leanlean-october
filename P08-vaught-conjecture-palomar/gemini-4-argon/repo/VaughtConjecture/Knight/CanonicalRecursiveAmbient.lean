/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.ScopedSourcePrefixAmbient

/-! # Arbitrary ambient extraction on the recursive successor

Actual availability chooses a source row; its clipped locality witness reads
the entire target-local cap vector. No canonical-ambient hypothesis or supplied
serving controller is used. Higher proper owners outside the target stay in
the carrier without entering this domain.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveAmbient

open Transform Value ExtOrd SourcePrefixRows CanonicalRecursiveSuccessorRows

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
  (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

abbrev target := (carrier sem n hA).below (A, n + 4)

theorem exists_capped_source {q : target sem n hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 4) q)
    (d : target sem n hA) (hd : (carrier sem n hA).grade d.1 = n + 4)
    {γ : ExtOrd} (hγ : SelfVis (n + 4) γ) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem n) (τ : ExtOrd → ExtOrd),
      Witness (gTop (n + 4)) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : target sem n hA, τ (source sem n hA hp P a x.1) = min (q x) γ := by
  obtain ⟨c, τ, hτ, hbound, hread⟩ := ScopedSourcePrefixAmbient.exists_active_source
    (data sem n hA hp P)
    (controller sem n hA (CanonicalRecursiveInventory.encode sem (n + 1) (p := fun _ => ⊥)
      ((RespectsSemantics.bot sem).toBelow (A, n + 4)) (fun _ => bot_ne_top)))
    hq d hd hγ hactive
  have ha : controller sem n hA (member sem n hA hp c) = c :=
    (controllerEquiv sem n hA hp).apply_symm_apply c
  refine ⟨member sem n hA hp c, τ, hτ, hbound, fun x => ?_⟩
  change τ ((data sem n hA hp P).profile (controller sem n hA (member sem n hA hp c)) x.1) = _
  rw [ha]
  exact hread x
