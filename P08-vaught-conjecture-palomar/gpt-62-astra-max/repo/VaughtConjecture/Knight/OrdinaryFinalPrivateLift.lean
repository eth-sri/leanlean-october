/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalOwnerLift
public import VaughtConjecture.Knight.OrdinaryFinalBottom
public import VaughtConjecture.Knight.FinalGateTransport
public import VaughtConjecture.Knight.PlacedFaceRestoration

/-! # Literal private-face lifting on the ordinary final physical layer

The private original face is identified occurrence by occurrence. An active
maximal prescribed owner supplies the capped physical repair; the predecessor's
lower-grade lift restores every remaining private value literally, including
distinct invisible values and top. Inactive owners and bottom caps are handled
separately. Every auxiliary retains the original external cap.

This proves the one private-face lifting clause under explicit predecessor
source, face, and lower-lifting hypotheses. It does not construct the global
scope predecessor or assert bountifulness for the whole request plan.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryFinalPrivateLift
open Transform Value ExtOrd CappedDonor CappedDonor.Ref CoatomBoundaryExtension
open OrdinaryFinalCatalogue OrdinaryFinalReadback
open SharpWitnessComposition
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A S : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))
variable (place : Fin N ↪ ι) (hS : Finset.univ.image place = S)
variable (hSA : S ⊆ A) (hne : S ≠ A)
variable (E : ExactSemanticFace (PointImageSemantics.rows C.scheme place hS C.rows) F.sem)

include hne in
/-- All-cap private-face lifting, including independent bottom supply and
literal top. The only lifting premise belongs to the predecessor below N. -/
theorem private_lift
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : ∀ a (c : D.below (A, N)),
      (∀ d : D.RowDomain c.1, Short (D.grade c.1) (F.sem.E c.1 d)) ∨
      (∀ d : D.RowDomain c.1, ∃ f : Field P C, F.lower a d.1 = a.val f))
    (hpriv : ∀ a d, F.lower a (E.map d) = a.val (.priv d))
    (hlift : CappedLift F.sem
      (show GradedLe (S, N - 1) (A, N - 1) from ⟨hSA, le_rfl⟩)) :
    CappedLift F.rows (show GradedLe (S, N) (A, N) from ⟨hSA, le_rfl⟩) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero F.positive.ne'
  apply PlacedFace.successor (S := C) (F.inheritedFace hSA hne E) le_rfl (min_le_left _ _) hSA
    (F.lower_lift _ (Nat.lt_succ_self _) hlift)
  · intro p hp
    obtain ⟨b,δ,hv,hread⟩ := OrdinaryFinalBottom.exists_private_display R F hfields
      (by rw [hgrid]; exact fun _ => CanonicalFieldLayer.grid_short (k+1) (Field P C)) hsupport howners E.map hpriv hp
    exact ⟨_,hv,hread⟩
  · intro c hi hc p q hp hq γ hγ hpos hpc hag
    exact OrdinaryFinalOwnerLift.exists_owner_capped_lift R F E.map (fun d => congrArg Prod.snd (E.index d))
      hfields hgrid hsupport hpriv c hi hc hp hq hγ hpos hpc hag

end
end VaughtConjecture.Knight.OrdinaryFinalPrivateLift
