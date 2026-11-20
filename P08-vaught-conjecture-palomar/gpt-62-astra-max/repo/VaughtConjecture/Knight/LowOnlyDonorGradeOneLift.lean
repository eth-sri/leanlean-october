/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RankFaceLift
public import VaughtConjecture.Knight.LowOnlyDonorGradeOneSource
public import VaughtConjecture.Knight.LowOnlyGradeOneLift

/-! # Positive-cap donor lifting on the unchanged padded LOW ladder

Attribution: the physical rank-table endgame is the donor-occurrence
specialization of `LowOnlyGradeOneLift`. It reuses the actual capped leaf chart,
rank-table interpolation, rank decoder and raw-row lawfulness. Admission is
constructed by the donor release fibre, not a symmetry of LOW.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition RelativeLadderLayer
noncomputable section
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → Field P C) (hproper : ∀ d, D.scope d ≠ A)
  (hboundary : ∀ S : State P C, F.Admissible 1 S →
    RespectsSemanticsBelow sem (A, 1) (fun d => S.profile (field d.1)))
  (incl : P.ClippedCells 1 → D.below (A, 1))
  (hfield : ∀ (S : State P C), F.Admissible 1 S → ∀ d,
    S.profile (field (incl d).1) = S.u d.1)

local notation "L" => carrier D hA (X := Field P C) (Q := F.Anchor 1)
local notation "E" => rows D sem hA field (F.fields 1) hproper
local notation "H" => rungs (X := Field P C)
local instance donorLiftFintype : Fintype (P.ClippedCells 1) := Fintype.ofFinite _

def donorAt (d : P.ClippedCells 1) : (L).below (A, 1) :=
  ⟨old D hA (incl d).1, by rw [old_index]; exact (incl d).2⟩

include hfield in
theorem anchor_donor (a : F.Anchor 1) (d : P.ClippedCells 1) :
    F.fields 1 a (field (incl d).1) = a.val (.inl d.1) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  change a.val (field (incl d).1) = a.val (.inl d.1)
  rw [← he]
  exact hfield S hs d

include hfield in
theorem leafSource_donor (a : F.Anchor 1) (d : P.ClippedCells 1) :
    leafSource F D hA field a (donorAt F D hA incl d).1 =
      SupportLadderRows.source H (fieldRank a.val (.inl d.1)) := by
  simp only [leafSource, donorAt, image, rankIndex_old, ranks, fieldRank,
    anchor_donor F D field incl hfield a d]
  rfl

include hboundary hfield in
/-- Arbitrary-input active lifting. All replacement/source data are constructed;
the hypotheses describe only the original boundary and the actual input query. -/
theorem donor_active_lift
    {p : P.ClippedCells 1 → ExtOrd} {q : (L).SectionAt (A, 1)}
    (hp : P.rows.Lawful p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : CappedEq (q ∘ donorAt F D hA incl) p γ)
    (c : P.ClippedCells 1) (hactive : γ < p c) :
    ∃ w : (L).SectionAt (A, 1), RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt F D hA incl d) = p d) ∧ CappedEq w q γ := by
  classical
  let Z := (zero : State P C).normalize 1
  have hz := F.normalize_admissible (by decide : 1 ≤ 1) (F.zero_admissible 1)
  have hzc : Z.profile ∈ CanonicalPairedProfiles.inventory (Field P C) 1 :=
    normalize_inventory 1 (fun d => by cases d with
      | inl d => exact bot_ne_top
      | inr d => cases d <;> exact bot_ne_top)
  let seed : F.Anchor 1 := ⟨Z.profile, hzc, Z, hz, rfl⟩
  have hpvis (d : P.ClippedCells 1) : SelfVis 1 (p d) := by
    have hg : P.scheme.grade d.1 = 1 :=
      le_antisymm (d.2.2.trans (min_le_left _ _)) (P.scheme.grade_pos d.1)
    exact hg ▸ (hp.orderly d).symm
  exact RankRepair.lift (D := D) (sem := sem) (hA := hA) (field := field) (profile := F.fields 1)
    (proper := hproper) (face := donorAt F D hA incl) seed (pick := (fun d => .inl d.1)) (leafSource_donor F D hA field incl hfield)
    (leafSource_lawful F D sem hA field hproper hboundary) hq hγ hpos hpvis hag hactive
    (fun a _ hσ hh => F.exists_donor_rank_repair a hσ hp hγ hpos hh c hactive)

include hboundary hfield in
/-- Every positive visible cap, including top; the inactive case is just the
lawful capped ambient, with the literal prescription pinned by its cap. -/
theorem donor_positive_lift
    {p : P.ClippedCells 1 → ExtOrd} {q : (L).SectionAt (A, 1)}
    (hp : P.rows.Lawful p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : CappedEq (q ∘ donorAt F D hA incl) p γ) :
    ∃ w : (L).SectionAt (A, 1), RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt F D hA incl d) = p d) ∧ CappedEq w q γ := by
  classical
  by_cases hsmall : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hsmall d)),
      fun _ => by rw [min_assoc, min_self]⟩
  · obtain ⟨c, hc⟩ := not_forall.mp hsmall
    exact donor_active_lift F D sem hA field hproper hboundary incl hfield
      hp hq hγ hpos hag c (not_le.mp hc)

end
end VaughtConjecture.Knight.LowOnly.Family
