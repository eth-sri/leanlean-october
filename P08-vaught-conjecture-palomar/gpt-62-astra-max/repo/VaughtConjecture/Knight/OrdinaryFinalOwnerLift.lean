/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalRepair
public import VaughtConjecture.Knight.PaddedOwnerRepair
public import VaughtConjecture.Knight.OrdinaryFinalReadback

/-! # Original-cap owner lifting on the ordinary final physical layer

From arbitrary lawful private prescriptions and target-local ambients, actual
availability/locality select the serving chart. Private-owner factorization,
ordinary catalogue repair, and supported inversion construct a new physical
section. Every installed coordinate retains the original external cap, and the
private prescription is read back capped at its active owner.

The cap identity is proved before lawfulness of the composite image. Only
bounded commutation is used for the composite; unrestricted faithful witness
composition is not asserted. Literal restoration above a proper owner remains
a separate predecessor-lifting step.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryFinalOwnerLift
open Transform Value ExtOrd CappedDonor CappedDonor.Ref SharpWitnessComposition
open OrdinaryFinalCatalogue OrdinaryFinalReadback
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))
variable (priv : Cell C.scheme ↪ Cell D)
variable (hprivGrade : ∀ d, D.grade (priv d) = C.scheme.grade d)

/-- All original auxiliary caps are retained against an arbitrary lawful
ambient. The output reads the prescription capped at the chosen active owner. -/
theorem exists_owner_capped_lift
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    (c : C.ClippedCells N) (hi : C.scheme.cell c.1 = effC N N) (hc : C.scheme.grade c.1 = N)
    {p : C.scheme.below (effC N N) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC N N) p)
    {q : F.carrier.below (A, N) → ExtOrd}
    (hq : RespectsSemanticsBelow F.rows (A, N) q)
    {γ : ExtOrd} (hγ : SelfVis N γ) (hpos : ⊥ < γ)
    (hpc : γ < p c)
    (hag : ∀ d, min (q (privAt R F priv hprivGrade d.1)) γ = min (p d) γ) :
    F.rows.FaceLift (fun d : C.ClippedCells N => privAt R F priv hprivGrade d.1)
      (fun d => min (p d) (p c)) q γ := by
  let c' := privAt R F priv hprivGrade c.1
  have hc' : F.carrier.grade c'.1 = N :=
    (congrArg Prod.snd (F.old_index (priv c.1))).trans ((hprivGrade c.1).trans hc)
  have hreach : γ ≤ q c' := min_eq_right_iff.mp
    ((hag c).trans (min_eq_right hpc.le))
  obtain ⟨a, σ, hσ, hb, hchart⟩ := F.exists_cap_chart hq c' hc' (seed R) hγ hreach
  have hfieldShort : ∀ b f, Short N (F.fields b f) := by
    intro b f
    rw [hfields]
    exact member_short R b f
  have hgridShort : ∀ z ∈ F.grid, Short N z := by
    rw [hgrid]
    exact fun _ hz => CanonicalFieldLayer.grid_short N (Field P C) hz
  refine PrivateRowFactorization.repairOwner c hi hc _ (a.property.2.priv.toBelow _) hp hq
    (t := fun d => F.source a d.1) (fun d => (F.source_old a _).trans (hpriv a _))
    (fun d => CanonicalPairedProfiles.inventory_coded _ _ a.property.1 _)
    (fun d => F.source_short hsupport hfieldShort hgridShort a d.1 d.2.2) hσ hγ hpos hpc
    (fun d => (min_eq_left (hb _)).trans (hchart d)) hag ?_
  intro b hb v hv heq
  obtain ⟨a',κ,_,hlaw,hpre,hr⟩ := OrdinaryFinalRepair.exists_source_repair R F hfields hgrid
    hsupport priv hpriv a hv (hgrid ▸ PairedSlotComparison.sourceGrid_endpoint hb)
    heq
  exact ⟨_,hlaw,hr,hpre⟩

end
end VaughtConjecture.Knight.OrdinaryFinalOwnerLift
