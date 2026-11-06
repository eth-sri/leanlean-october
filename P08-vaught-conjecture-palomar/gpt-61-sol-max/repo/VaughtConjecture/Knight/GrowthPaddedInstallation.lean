/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedIteration
import VaughtConjecture.Knight.GrowthPaddedFaces
import VaughtConjecture.Knight.CanonicalCodingSupport

/-! # Coding and literal ordered faces of the recursive padded growth carrier

Each recursive output retains both original semantic faces, with their actual
ordered occurrences and exhaustive lower domains. Coding is derived from the
canonical fields and supported native grid, not merely from shortness. Under
the two-original scope cover, completeness holds through the installed height.
No bountifulness of higher outputs is claimed.
-/

namespace VaughtConjecture.Knight.GrowthPaddedInstallation
open   ExtOrd  Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration GrowthPaddedStepRows

noncomputable section

section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

theorem field_coded {j} a d :
    IsCodedLabel j (fields X j a d) := by
  rcases mem_codedAlphabet_iff.mp
      (CanonicalPairedProfiles.inventory_coded a.property.1 d)
      with hb | ⟨b, i, _, hi, he⟩
  · exact Or.inl hb
  · exact Or.inr ⟨b, i, hi, he⟩
end

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (attach : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem initial_coded : (initial I X attach hA hB hC).rows.IsCoded := by
  let J := GrowthPaddedSuccessor.input I X attach hA hB hC
  apply CanonicalCodingSupport.layer
    (RelativeLadderLayer.coded I.boundary I.rows (by omega)
      (field I) (fields X 1) (proper hB hC) I.coded) J.inherited_row
  rintro ⟨a, v⟩ d
  cases v with
  | some v => exact Empty.elim v
  | none =>
    
    rw [GrowthPaddedSuccessor.leaf_row]
    exact CanonicalCodingSupport.supported
      (fun _ hz => CanonicalCodingSupport.grid hz) (field_coded X a)
      (GrowthPaddedSuccessor.source_supported a d.1)

section
variable {I X attach hA hB hC} {k : ℕ}
  (P : Layer I X attach hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem successor_coded (hc : P.rows.IsCoded) : (successor P hk hnext).rows.IsCoded := by
  apply CanonicalCodingSupport.layer hc (inherited_row P hk hnext)
  intro a d
  
  have he := (data P hk hnext).row_new (controller P hnext a) d
  exact he.symm ▸ CanonicalCodingSupport.supported
    (fun _ hz => CanonicalCodingSupport.grid hz) (field_coded X a)
    (source_supported P hk hnext a d.1)

def successor_face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows P.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (successor P hk hnext).rows :=
  SeparatedLayerFace.face (inherited_row P hk hnext) G hT

end

local notation "build₀" => build I X attach hA hB hC

theorem build_coded t (ht : t + 2 ≤ A.card) :
    (build₀ t ht).rows.IsCoded := by
  induction t with
  | zero => exact initial_coded I X attach hA hB hC
  | succ t ih => solve_by_elim [successor_coded]

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    (t : ℕ) → (ht : t + 2 ≤ A.card) →
      ExactSemanticFace oldRows (build₀ t ht).rows
  | 0, _ => GrowthPaddedFaces.face I X attach hA hB hC G hT
  | t + 1, ht => successor_face (build₀ t (by omega))
      (by omega) ht (face G hT t (by omega)) hT

local notation "face₀" => face I X attach hA hB hC

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
    StrictMono (donorFace I X attach hA hB hC t ht).map := by
  have he := funext (face_map I X attach hA hB hC I.leftFace hB.not_ge t ht)
  change StrictMono (face₀ I.leftFace hB.not_ge t ht).map
  rw [he]
  exact (build₀ t ht).base_mono.comp
    ((SourceLayerCarrier.old_order).comp I.left_order)

theorem private_order (t : ℕ) (ht : t + 2 ≤ A.card) :
    StrictMono (privateFace I X attach hA hB hC t ht).map := by
  have he := funext (face_map I X attach hA hB hC I.rightFace hC.not_ge t ht)
  change StrictMono (face₀ I.rightFace hC.not_ge t ht).map
  rw [he]
  exact (build₀ t ht).base_mono.comp
    ((SourceLayerCarrier.old_order).comp I.right_order)

/-- Every installed full-scope grade has an actual owner, obtained from the
constructed ceiling receipt rather than an assumed completeness contract. -/
theorem full_occupied t (ht : t + 2 ≤ A.card) j
    (hj : 1 ≤ j) (hjt : j ≤ t + 2) :
    ∃ d, (build₀ t ht).carrier.cell d = (A, j) := by
  obtain ⟨d, hd, _⟩ := (build₀ t ht).ceiling_at le_rfl
    zero (zero_admitted X) (fun f => by cases f <;> exact bot_ne_top)
    (G := ∅)  (by simp [VisibleOn]) (by simp [SelfVis]) (fun _ => le_top) j hj hjt
  exact ⟨d, hd⟩

