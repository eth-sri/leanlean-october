/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyDonorGradeOneSource
public import VaughtConjecture.Knight.LowOnlyGradeOneLift

/-! # Positive-cap donor lifting on the unchanged padded LOW ladder

Attribution: the physical rank-table endgame is the donor-occurrence
specialization of `LowOnlyGradeOneLift`. It reuses the actual capped leaf chart,
rank-table interpolation, rank decoder and raw-row lawfulness. Admission is
constructed by the donor release fibre, not a symmetry of LOW.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse LadderScalarRendering SharpWitnessComposition RelativeLadderLayer

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)
  {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → Field P C) (hproper : ∀ d, D.scope d ≠ A)
  (hboundary : ∀ S : State P C, F.Admissible 1 S →
    RespectsSemanticsBelow sem (A, 1) (fun d => S.profile (field d.1)))
  (incl : P.scheme.below (effC n 1) → D.below (A, 1))
  (hfield : ∀ (S : State P C), F.Admissible 1 S → ∀ d,
    S.profile (field (incl d).1) = S.u d.1)

local notation "L" => carrier D hA (X := Field P C) (Q := F.Anchor 1)
local notation "E" => rows D sem hA field (F.fields 1) hproper
local notation "H" => rungs (X := Field P C)
def donorAt (d : P.scheme.below (effC n 1)) : (L).below (A, 1) :=
  ⟨old D hA (incl d).1, by rw [old_index]; exact (incl d).2⟩

include hboundary hfield in
/-- Every positive visible cap, including top; the inactive case is just the
lawful capped ambient, with the literal prescription pinned by its cap. -/
theorem donor_positive_lift
    {p : P.scheme.below (effC n 1) → ExtOrd} {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (donorAt F D hA incl d)) γ = min (p d) γ) :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt F D hA incl d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ :=
  face_positive_lift F D sem hA field hproper hboundary P incl .inl
    (fun a d => by obtain ⟨S, hs, he⟩ := a.property.2; rw [← he]; exact hfield S hs d)
    hp hq hγ hpos hag fun a _ hσ hpr c hactive =>
      F.exists_donor_rank_repair a hσ hp hγ hpos hpr c hactive

