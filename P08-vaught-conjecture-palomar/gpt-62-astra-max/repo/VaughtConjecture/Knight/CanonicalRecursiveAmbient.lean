/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.SourcePrefixAmbient

/-! # Arbitrary ambient extraction on the recursive successor

Actual availability chooses a source row; its clipped locality witness reads
the entire target-local cap vector. No canonical-ambient hypothesis or supplied
serving controller is used. Higher proper owners outside the target stay in
the carrier without entering this domain.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveAmbient

open Transform Value ExtOrd SourcePrefixRows CanonicalRecursiveSuccessorRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 1 ≤ A.card)
variable (hp : D.AvoidsScope A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

private def seed : Profile sem n :=
  CanonicalRecursiveInventory.encode sem (n + 1) (p := fun _ => ⊥)
    ((RespectsSemantics.bot sem).toBelow (A, (n + 1))) (fun _ => bot_ne_top)

abbrev target := (carrier sem n hA).below (A, (n + 1))

/-- An arbitrary active ambient has a genuine source-family representation
at the original cap, with a constructed first reaching grid cut. -/
theorem exists_capped_source {q : target sem n hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem n hA hp P) (A, (n + 1)) q)
    (d : target sem n hA)
    (hd : (carrier sem n hA).grade d.1 = (n + 1))
    {γ : ExtOrd} (hγ : SelfVis (n + 1) γ) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem n) (τ : ExtOrd → ExtOrd),
      Witness (gTop (n + 1)) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : target sem n hA,
        τ (source sem n hA hp P a x.1) = min (q x) γ :=
  SourcePrefixAmbient.cappedProfile (controllerEquiv sem n hA hp) (seed sem n)
    (data sem n hA hp P).row_new hq d hd hγ hactive

end
end VaughtConjecture.Knight.CanonicalRecursiveAmbient
