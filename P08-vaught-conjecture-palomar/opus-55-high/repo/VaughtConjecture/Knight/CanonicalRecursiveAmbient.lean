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

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveAmbient

open Transform Value ExtOrd SourcePrefixRows CanonicalRecursiveSuccessorRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

private def seed : Profile sem n :=
  CanonicalRecursiveInventory.encode sem (n + 1) (p := fun _ => ⊥)
    ((RespectsSemantics.bot sem).toBelow (A, (n + 4))) (fun _ => bot_ne_top)

abbrev target := (carrier sem n hA).below (A, (n + 4))

/-- An arbitrary active ambient has a genuine source-family representation
at the original cap, with a constructed first reaching grid cut. -/
theorem exists_capped_source {q : target sem n hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem n hA hp P) (A, (n + 4)) q)
    d
    (hd : (carrier sem n hA).grade d.1 = (n + 4))
    {γ} (hγ : SelfVis (n + 4) γ) (hb : γ ≠ ⊥) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem n) (τ : ExtOrd → ExtOrd) (h : ExtOrd),
      Witness (gTop (n + 4)) τ ∧ (∀ x, τ x ≤ γ) ∧
      τ (ceiling (D := D) n) = γ ∧
      h ∈ grid (D := D) n ∧ SelfVis (n + 4) h ∧ ⊥ < h ∧
      h ≤ ceiling (D := D) n ∧ τ h = γ ∧
      (∀ z ∈ grid (D := D) n, z < h → τ z < γ) ∧
      (∀ x,
        τ (source sem n hA hp P a x.1) = min (q x) γ) ∧
      RespectsSemanticsBelow (rows sem n hA hp P) (A, (n + 4))
        (fun x => τ (source sem n hA hp P a x.1)) := by
  let F := data sem n hA hp P
  obtain ⟨c, τ, _, hτ, hbound, hC, hread⟩ := ScopedSourcePrefixAmbient.exists_active_source F
    (controller sem n hA (seed sem n)) hq d hd hγ hactive
  let a := member sem n hA hp c
  have ha : controller sem n hA a = c :=
    (controllerEquiv sem n hA hp).apply_symm_apply c
  have hr (x : target sem n hA) :
      τ (source sem n hA hp P a x.1) = min (q x) γ := by
    change τ (F.profile (controller sem n hA a) x.1) = _
    rw [ha]
    exact hread x
  obtain ⟨h, hh, hv, hpos, hc, he, hm⟩ :=
    ScopedSourcePrefixAmbient.exists_first_cut F hτ hb hbound hC
  refine ⟨a, τ, h, hτ, hbound, hC, hh, hv, hpos, hc, he, hm, hr, ?_⟩
  have hf : (fun x =>
      τ (source sem n hA hp P a x.1)) =
      (fun x => min (q x) γ) := funext hr
  rw [hf]
  exact hq.cap hγ

end
end VaughtConjecture.Knight.CanonicalRecursiveAmbient
