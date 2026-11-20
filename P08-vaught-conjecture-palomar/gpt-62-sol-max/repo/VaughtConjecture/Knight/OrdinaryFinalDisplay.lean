/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalRepair
public import VaughtConjecture.Knight.MixedRowDecoding

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryFinalDisplay

open Transform Value ExtOrd CappedDonor CappedDonor.Ref SharpWitnessComposition

open OrdinaryFinalCatalogue

noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}

variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

/-- Each owner is short, or its whole row is evaluated on catalogue fields. -/
abbrev FieldOwners := ∀ a (c : D.below (A, N)),
  (∀ d, Short (D.grade c.1) (F.sem.E c.1 d)) ∨
  (∀ d : D.below (D.cell c.1), ∃ f, F.lower a d.1 = a.val f)

private theorem decode
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : ∀ z ∈ F.grid, Short N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : FieldOwners R F) (a : Member R) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop N) δ) (hb : ∀ f, δ (a.val f) = ⊥ ↔ a.val f = ⊥) :
    RespectsSemanticsBelow F.rows (A, N) (fun d => δ (F.source a d.1)) := by
  apply F.decoded_respects hsupport (fun b f => hfields b f ▸ member_short R b f) hgrid a hδ
  apply map_respects_of_short_or_reflecting (F.lower_lawful a) (fun d => d.2.2) hδ
  intro c
  rcases howners a c with hs | ho
  · exact Or.inl hs
  · right
    intro d
    obtain ⟨f, hf⟩ := ho d
    change δ (F.lower a d.1) = ⊥ ↔ F.lower a d.1 = ⊥
    simpa only [hf] using hb f

/-- Decode the selected complete source on the **actual** installed carrier.
The long-row alternative only concerns values at its real arguments. -/
theorem exists_actual_display
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (hgrid : ∀ z ∈ F.grid, Short N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : OrdinaryFinalDisplay.FieldOwners R F)
    (req : Cell P.scheme ↪ Cell D) (priv : Cell C.scheme ↪ Cell D)
    (hreq : ∀ a d, F.lower a (req d) = a.val (.req d))
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d)) :
    ∃ (a : OrdinaryFinalCatalogue.Member R) (δ : ExtOrd → ExtOrd),
      RespectsSemanticsBelow F.rows (A, N) (fun d => δ (F.source a d.1)) ∧
      (∀ d : Cell P.scheme, δ (F.source a (F.old (req d))) = R.p d) ∧
      (∀ d : Cell C.scheme, δ (F.source a (F.old (priv d))) = R.vact d) ∧
      δ (F.source a (F.added a true)) = ⊤ := by
  obtain ⟨a, δ, hδ, hP, hC, hg, hreflect⟩ := exists_actual_member_reflecting R
  refine ⟨a, δ, decode R F hfields hgrid hsupport howners a hδ hreflect, ?_, ?_, ?_⟩
  · intro d
    rw [F.source_old, hreq]
    exact hP d
  · intro d
    rw [F.source_old, hpriv]
    exact hC d
  · rwa [F.source_own_marked, hgate, hfields]

/-- Every private prescription, including literal top, has a lawful physical extension. -/
theorem exists_private_display
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : ∀ z ∈ F.grid, Short N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : FieldOwners R F) (priv : Cell C.scheme ↪ Cell D)
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    {p : C.scheme.below (effC N N) → ExtOrd} (hp : RespectsSemanticsBelow C.rows (effC N N) p) :
    ∃ (r : Cell F.carrier → ExtOrd), RespectsSemanticsBelow F.rows (A, N) (fun d => r d.1) ∧
      ∀ d : C.scheme.below (effC N N), r (F.old (priv d.1)) = p d := by
  obtain ⟨a, ha, hp'⟩ := exists_private_admitted (R := R) hp
  obtain ⟨b, δ, hδ, hr, hb⟩ := exists_member_decoder R ha
  refine ⟨δ ∘ F.source b, decode R F hfields hgrid hsupport howners b hδ hb, fun d => ?_⟩
  rw [Function.comp_apply, F.source_old, hpriv, hr, hp']

end

end VaughtConjecture.Knight.OrdinaryFinalDisplay
