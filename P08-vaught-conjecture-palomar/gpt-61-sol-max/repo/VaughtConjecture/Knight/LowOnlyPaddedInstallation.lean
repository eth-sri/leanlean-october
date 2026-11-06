/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedIteration
import VaughtConjecture.Knight.LowOnlyPaddedPairLift
import VaughtConjecture.Knight.CanonicalCodingSupport

/-! # Coding and literal ordered faces of the recursive padded LOW carrier

Each recursive output retains both original semantic faces, with their actual
ordered occurrences and exhaustive lower domains. Coding is derived from the
canonical fields and supported native grid, not merely from shortness. Under
the two-original scope cover, completeness holds through the installed height.
No bountifulness of higher outputs is claimed.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedInstallation
open   ExtOrd  LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedStepRows

noncomputable section

section
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

theorem field_coded {j} a d :
    IsCodedLabel j (F.fields j a d) := by
  rcases mem_codedAlphabet_iff.mp
      (CanonicalPairedProfiles.inventory_coded a.property.1 d)
      with hb | ⟨b, i, _, hi, he⟩
  · exact Or.inl hb
  · exact Or.inr ⟨b, i, hi, he⟩
end

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem initial_coded : (initial I F hroot hA hB hC).rows.IsCoded := by
  let J := LowOnlyPaddedSuccessor.input I F hroot hA hB hC
  apply CanonicalCodingSupport.layer
    (RelativeLadderLayer.coded I.boundary I.rows (by omega)
      (field I) (F.fields 1) (proper hB hC) I.coded) J.inherited_row
  rintro ⟨a, v⟩ d
  cases v with
  | some v => exact Empty.elim v
  | none =>
    
    rw [LowOnlyPaddedSuccessor.leaf_row]
    exact CanonicalCodingSupport.supported
      (fun _ hz => CanonicalCodingSupport.grid hz) (field_coded F a)
      (LowOnlyPaddedSuccessor.source_supported a d.1)

section
variable {I F hroot hA hB hC} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem successor_coded (hc : P.rows.IsCoded) : (successor P hk hnext).rows.IsCoded := by
  apply CanonicalCodingSupport.layer hc (inherited_row P hk hnext)
  intro a d
  
  have he := (data P hk hnext).row_new (controller P hnext a) d
  exact he.symm ▸ CanonicalCodingSupport.supported
    (fun _ hz => CanonicalCodingSupport.grid hz) (field_coded F a)
    (source_supported P hk hnext a d.1)

def successor_face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows P.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (successor P hk hnext).rows :=
  SeparatedLayerFace.face (inherited_row P hk hnext) G hT

end

local notation "build₀" => build I F hroot hA hB hC

theorem build_coded t (ht : t + 2 ≤ A.card) :
    (build₀ t ht).rows.IsCoded := by
  induction t with
  | zero => exact initial_coded I F hroot hA hB hC
  | succ t ih => solve_by_elim [successor_coded]

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    (t : ℕ) → (ht : t + 2 ≤ A.card) →
      ExactSemanticFace oldRows (build₀ t ht).rows
  | 0, _ => LowOnlyPaddedFaces.face I F hroot hA hB hC G hT
  | t + 1, ht => successor_face (build₀ t (by omega))
      (by omega) ht (face G hT t (by omega)) hT

local notation "face₀" => face I F hroot hA hB hC

theorem face_map {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T)
    (t : ℕ) (ht : t + 2 ≤ A.card) (d : Cell E) :
    (face₀ G hT t ht).map d =
      (build₀ t ht).baseMap
        (RelativeLadderLayer.old I.boundary (by omega) (G.map d)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    exact congrArg (old (build₀ t (by omega)) (by omega)) (ih (by omega))

def donorFace t (ht : t + 2 ≤ A.card) :=
  face₀ I.leftFace hB.not_ge t ht

def privateFace t (ht : t + 2 ≤ A.card) :=
  face₀ I.rightFace hC.not_ge t ht

theorem donor_order (t : ℕ) (ht : t + 2 ≤ A.card) :
    StrictMono (donorFace I F hroot hA hB hC t ht).map := by
  have he := funext (face_map I F hroot hA hB hC I.leftFace hB.not_ge t ht)
  change StrictMono (face₀ I.leftFace hB.not_ge t ht).map
  rw [he]
  exact (build₀ t ht).base_mono.comp
    ((SourceLayerCarrier.old_order).comp I.left_order)

theorem private_order (t : ℕ) (ht : t + 2 ≤ A.card) :
    StrictMono (privateFace I F hroot hA hB hC t ht).map := by
  have he := funext (face_map I F hroot hA hB hC I.rightFace hC.not_ge t ht)
  change StrictMono (face₀ I.rightFace hC.not_ge t ht).map
  rw [he]
  exact (build₀ t ht).base_mono.comp
    ((SourceLayerCarrier.old_order).comp I.right_order)

