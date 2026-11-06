
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
import VaughtConjecture.Knight.LowOnlyPaddedStepCharts
import VaughtConjecture.Knight.LowOnlyDonorOrderedLift

/-! # Constructed higher donor owner-capped repair

The actual chart supplies lawful source-cut factorization. The donor fibre
is used explicitly; LOW is not exchanged between faces. Supported decoding
retains every physical coordinate's external cap.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedStepDonorRepair
open    CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedStepDecode LowOnlyPaddedStepCharts SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : F.root.Covers I.shared.f I.shared.g}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

local notation "effC₀" => effC n (k + 1)

theorem donor_grade d :
    (carrier P hnext).grade (donorAt P hnext d).1 =
      I.left.scheme.grade d.1 := (congrArg Prod.snd (original_index P hnext
    (I.leftFace.map d.1))).trans (congrArg Prod.snd (I.leftFace.index d.1))

/-- A supplied original owner identifies the actual donor lower domain.
The final lifting theorem chooses a maximal such owner from the prescription. -/
theorem owner_capped
    (c : I.left.scheme.below (effC₀))
    (hc : I.left.scheme.cell c.1 = effC₀) (hg : I.left.scheme.grade c.1 = (k + 1))
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (effC₀) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) q)
    {γ} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) u ∧
      (∀ d, u (donorAt P hnext d) = min (p d) (p c)) ∧
      (CappedEq u q γ) ∧ (BoundedBy u (p c)) := by
  
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := LowOnlyPaddedStepCharts.exists_chart P hk hnext hq
  have hreach : γ ≤ H := by
    grind [donor_grade]
  have hchart d : min (σ (source P hk hnext a d.1)) γ = min (q d) γ := by
    grind
  obtain ⟨S, hS, he⟩ := a.property.2
  have hcanon  :=
    he.symm ▸ a.property.1
  have ha : (⟨S.profile, hcanon, S, hS, rfl⟩ : F.Anchor (k + 1)) = a := Subtype.ext he
  have hdonor (d : I.left.scheme.below effC₀) :
      source P hk hnext a (donorAt P hnext d).1 = S.lowerP (k + 1) d := by
    change source P hk hnext a
      (original P hnext (I.leftFace.map d.1)) = _
    rw [source_original]
    change a.val (LowOnlyOrderedLadder.field I (I.leftFace.map d.1)) = S.u d.1
    rw [← he]
    exact LowOnlyOrderedLadder.field_donor I
  let toEff := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (I.left.scheme.cell c.1) (effC₀) from by
      rw [hc]; exact GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (effC₀) (I.left.scheme.cell c.1) from by
      rw [hc]; exact GradedLe.refl _)
  let s := S.lowerP (k + 1) ∘ toEff
  let p' := p ∘ toEff
  have hs' : Semantics.RowLawful I.left.rows c.1 s := hS.lawfulP.mono _
  have hp' : Semantics.RowLawful I.left.rows c.1 p' := hp.mono _
  obtain ⟨δ, hδ, hδpos, _, _, ⟨fac⟩⟩ := PrivateRowFactorization.exists_factorization hs' hp'
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_coded hcanon (.inl d.1))
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_short hcanon (.inl d.1))
    (by simpa only [hg] using hσ) (by simpa only [hg] using hγ) hpos hactive (fun d => by
      grind)
  rw [hg] at hδ
  rcases Finset.mem_insert.mp hδ with hz | hd
  · simp_all
  obtain ⟨b, hb, hbδ⟩ := Finset.mem_image.mp hd
  change CanonicalPairedInverse.grid (k + 1) b = δ at hbδ
  subst δ
  have hb' : b ≤ 2 * Fintype.card (Field I.left I.right) + 1 := by
    grind
  let v := fac.source ∘ fromEff
  have hv : RespectsSemanticsBelow I.left.rows (effC₀) v := fac.lawful.mono _
  obtain ⟨w, hw, hwread, hwcap⟩ := donor_source_repair P hk hnext hS hcanon hb' hv
    (fun d => fac.prefix_eq (fromEff d))
  have hcap d : min (fac.outgoing (w d)) γ = min (q d) γ := by
    have hpre := hwcap d
    rw [ha] at hpre
    have hs : Short (I.left.scheme.grade c.1) (source P hk hnext a d.1) := by
      simpa only [hg] using source_short P hk hnext a d.1
    exact (AmbientGradeCharts.map_cap_agreement fac.witness.mono hpre fac.reaches).trans
      ((fac.caps _ hs).trans (hchart d))
  have hν  := by simpa only [hg] using fac.witness
  refine ⟨fun d => fac.outgoing (w d),
    map_respects_of_positive_cap_agreement hw hq (fun d => d.2.2)
      (boundedMap_of_witness hν) (ne_of_gt hpos) hcap, ?_, hcap, fun _ => fac.bounded _⟩
  intro d
  exact (congrArg fac.outgoing (hwread d)).trans (fac.readback (fromEff d))


