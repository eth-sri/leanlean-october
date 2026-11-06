/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedIteration
public import VaughtConjecture.Knight.LowOnlyPaddedPairLift
public import VaughtConjecture.Knight.CanonicalCodingSupport

/-! # Coding and literal ordered faces of the recursive padded LOW carrier

Each recursive output retains both original semantic faces, with their actual
ordered occurrences and exhaustive lower domains. Coding is derived from the
canonical fields and supported native grid, not merely from shortness. Under
the two-original scope cover, completeness holds through the installed height.
No bountifulness of higher outputs is claimed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedInstallation
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedStepRows
open AmalgamationPlan CoatomBoundaryExtension
noncomputable section

section Fields
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

theorem field_coded {j} a d :
    IsCodedLabel j (F.fields j a d) := by
  rcases mem_codedAlphabet_iff.mp
      (CanonicalPairedProfiles.inventory_coded (Field P C) j a.property.1 d)
      with hb | ⟨b, i, _, hi, he⟩
  · exact Or.inl hb
  · exact Or.inr ⟨b, i, hi, he⟩

end Fields

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem initial_coded : (initial I F hroot hA hB hC).rows.IsCoded := by
  let J := LowOnlyPaddedSuccessor.input I F hroot hA hB hC
  apply CanonicalCodingSupport.layer J.lower
    (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
    2 (by decide) hA J.separation J.lowerRows J.rows
    (RelativeLadderLayer.coded I.boundary I.rows (by omega)
      (field I) (F.fields 1) (proper I hB hC) I.coded) J.inherited_row
  rintro ⟨a, v⟩ d
  cases v with
  | some v => exact Empty.elim v
  | none =>
    change IsCodedLabel 2 ((LowOnlyPaddedSuccessor.rows I F hroot hA hB hC).E
      (LowOnlyPaddedSuccessor.leaf I F hroot hA hB hC a) d)
    rw [LowOnlyPaddedSuccessor.leaf_row]
    exact CanonicalCodingSupport.supported
      (fun _ hz => CanonicalCodingSupport.grid _ _ hz) (field_coded F a)
      (LowOnlyPaddedSuccessor.source_supported I F hroot hA hB hC a d.1)

section Successor
variable {I F hroot hA hB hC} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem successor_coded (hc : P.rows.IsCoded) : (successor P hk hnext).rows.IsCoded := by
  apply CanonicalCodingSupport.layer P.carrier (F.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I F hroot hA hB hC (by omega))
    P.rows (rows P hk hnext) hc (inherited_row P hk hnext)
  intro a d
  change IsCodedLabel (k + 1) ((rows P hk hnext).E (controller P hnext a).1 d)
  have he := (data P hk hnext).row_new (controller P hnext a) d
  exact he.symm ▸ CanonicalCodingSupport.supported
    (fun _ hz => CanonicalCodingSupport.grid _ _ hz) (field_coded F a)
    (source_supported P hk hnext a d.1)

def successor_face {T} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows P.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (successor P hk hnext).rows :=
  SeparatedLayerFace.face P.carrier (F.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I F hroot hA hB hC (by omega))
    P.rows (rows P hk hnext) (inherited_row P hk hnext) G hT

end Successor

theorem build_coded t ht :
    (build I F hroot hA hB hC t ht).rows.IsCoded := by
  induction t with
  | zero => exact initial_coded I F hroot hA hB hC
  | succ t ih => exact successor_coded _ _ _ (ih (by omega))

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    (t : ℕ) → (ht : t + 2 ≤ A.card) →
      ExactSemanticFace oldRows (build I F hroot hA hB hC t ht).rows
  | 0, _ => LowOnlyPaddedFaces.face I F hroot hA hB hC G hT
  | t + 1, ht => successor_face (build I F hroot hA hB hC t (by omega))
      (by omega) ht (face G hT t (by omega)) hT

theorem face_map {T} {E} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T)
    t ht d :
    (face I F hroot hA hB hC G hT t ht).map d =
      (build I F hroot hA hB hC t ht).baseMap
        (RelativeLadderLayer.old I.boundary (by omega) (G.map d)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    exact congrArg (old (build I F hroot hA hB hC t (by omega)) (by omega)) (ih (by omega))

section
variable (t : ℕ) (ht : t + 2 ≤ A.card)

def donorFace  :
    ExactSemanticFace I.leftRows (build I F hroot hA hB hC t ht).rows :=
  face I F hroot hA hB hC I.leftFace hB.not_ge t ht

def privateFace  :
    ExactSemanticFace I.rightRows (build I F hroot hA hB hC t ht).rows :=
  face I F hroot hA hB hC I.rightFace hC.not_ge t ht

end

section
variable (t : ℕ) (ht : t + 2 ≤ A.card)

theorem donor_order  :
    StrictMono (donorFace I F hroot hA hB hC t ht).map := by
  have he := funext (face_map I F hroot hA hB hC I.leftFace hB.not_ge t ht)
  change StrictMono (face I F hroot hA hB hC I.leftFace hB.not_ge t ht).map
  rw [he]
  exact (build I F hroot hA hB hC t ht).base_mono.comp
    ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.left_order)

theorem private_order  :
    StrictMono (privateFace I F hroot hA hB hC t ht).map := by
  have he := funext (face_map I F hroot hA hB hC I.rightFace hC.not_ge t ht)
  change StrictMono (face I F hroot hA hB hC I.rightFace hC.not_ge t ht).map
  rw [he]
  exact (build I F hroot hA hB hC t ht).base_mono.comp
    ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.right_order)

end

end
end VaughtConjecture.Knight.LowOnlyPaddedInstallation
