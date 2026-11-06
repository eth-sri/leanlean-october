
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedCharts

/-! # Constructed owner-capped donor repair on the installed growth successor

The three cuts remain distinct: the original external cap, the constructed
native grid cut, and the prescribed owner value. No alignment or replacement
source is supplied by the caller. The argument reuses
`LowOnlyPaddedDonorRepair` with the pre-activation growth donor repair producer.
No symmetry of the admission predicate is used.
-/

namespace VaughtConjecture.Knight.GrowthPaddedDonorRepair
open     Growth CanonicalPairedInverse
open GrowthPaddedSuccessor GrowthPaddedDecode GrowthPaddedCharts
open SharpWitnessComposition


variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "donorAt₀" => donorAt I X T hA hB hC

theorem donor_grade d :
    (carrier I X T hA hB hC).grade (donorAt₀ d).1 =
      I.left.scheme.grade d.1 := (congrArg Prod.snd (original_index I X T hA hB hC
    (I.leftFace.map d.1))).trans (congrArg Prod.snd (I.leftFace.index d.1))

local notation "source₀" => source I X T hA hB hC

/-- A supplied original owner identifies the actual donor lower domain.
The final lifting theorem chooses a maximal such owner from the prescription. -/
theorem owner_capped (hN : 2 < X.req.N)
    (c : I.left.scheme.below (Finset.univ, 2))
    (hc : I.left.scheme.cell c.1 = (Finset.univ, 2)) (hg : I.left.scheme.grade c.1 = 2)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) q)
    {γ} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (donorAt₀ d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) u ∧
      (∀ d, u (donorAt₀ d) = min (p d) (p c)) ∧
      (CappedEq u q γ) ∧ (BoundedBy u (p c)) := by
  
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := GrowthPaddedCharts.exists_chart I X T hA hB hC hq
  have hreach : γ ≤ H := by
    grind [donor_grade]
  have hchart d : min (σ (source₀ a d.1)) γ = min (q d) γ := by
    rw [hread, min_assoc, min_eq_right hreach]
  obtain ⟨S, hS, he⟩ := a.property.2
  have hcanon  :=
    he.symm ▸ a.property.1
  have ha : (⟨S.profile, hcanon, S, hS, rfl⟩ : Catalogue X 2) = a := Subtype.ext he
  have hdonor (d : I.left.scheme.below (Finset.univ, 2)) :
      source₀ a (donorAt₀ d).1 = S.donorValues d.1 := by
    change source₀ a
      (original I X T hA hB hC (I.leftFace.map d.1)) = _
    rw [original_readback]
    change a.val (GrowthOrderedBase.field I (I.leftFace.map d.1)) = S.donorValues d.1
    rw [← he]
    exact GrowthOrderedBase.field_donor I
  let toEff := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (I.left.scheme.cell c.1) (Finset.univ, 2) from by
      rw [hc]; exact GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (Finset.univ, 2) (I.left.scheme.cell c.1) from by
      rw [hc]; exact GradedLe.refl _)
  let s := (fun d => S.donorValues d.1) ∘ toEff
  let p' := p ∘ toEff
  have hs' : Semantics.RowLawful I.left.rows c.1 s :=
    hS.donor_lawful.mono _
  have hp' : Semantics.RowLawful I.left.rows c.1 p' := hp.mono _
  obtain ⟨δ, hδ, hδpos, _, _, ⟨fac⟩⟩ := PrivateRowFactorization.exists_factorization hs' hp'
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_coded hcanon (.inr d.1))
    (fun d => by
      rw [hg]
      exact CanonicalPairedProfiles.inventory_short hcanon (.inr d.1))
    (by simpa only [hg] using hσ) (by simpa only [hg] using hγ) hpos hactive (fun d => by
      grind)
  rw [hg] at hδ
  rcases Finset.mem_insert.mp hδ with hz | hd
  · simp_all
  obtain ⟨b, hb, hbδ⟩ := Finset.mem_image.mp hd
  change grid 2 b = δ at hbδ
  subst δ
  have hb' : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1 := by
    grind
  let v := fac.source ∘ fromEff
  have hv : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) v := fac.lawful.mono _
  obtain ⟨w, hw, hwread, hwcap⟩ := donor_source_repair I X T hA hB hC hN hS hcanon hb' hv
    (fun d => fac.prefix_eq (fromEff d))
  have hcap d : min (fac.outgoing (w d)) γ = min (q d) γ := by
    have hpre := hwcap d
    rw [ha] at hpre
    have hs : Short (I.left.scheme.grade c.1) (source₀ a d.1) := by
      simpa only [hg] using source_short I X T hA hB hC a d.1
    exact (AmbientGradeCharts.map_cap_agreement fac.witness.mono hpre fac.reaches).trans
      ((fac.caps _ hs).trans (hchart d))
  have hν  := by simpa only [hg] using fac.witness
  refine ⟨fun d => fac.outgoing (w d),
    map_respects_of_positive_cap_agreement hw hq (fun d => d.2.2)
      (boundedMap_of_witness hν) (ne_of_gt hpos) hcap, ?_, hcap, fun _ => fac.bounded _⟩
  intro d
  exact (congrArg fac.outgoing (hwread d)).trans (fac.readback (fromEff d))


