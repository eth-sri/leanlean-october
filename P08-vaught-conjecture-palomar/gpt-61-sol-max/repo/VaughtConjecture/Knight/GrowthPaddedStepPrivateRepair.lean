
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedStepDecode
import VaughtConjecture.Knight.GrowthPaddedStepCharts

/-! # Constructed higher private owner-capped repair

The actual chart supplies lawful source-cut factorization. The private fibre
and supported decoder construct the replacement and every external-cap receipt.
-/

/- Adapted from LowOnlyPaddedStepPrivateRepair using growth admission. -/

namespace VaughtConjecture.Knight.GrowthPaddedStepPrivateRepair
open     Growth CanonicalPairedInverse
open GrowthPaddedContract GrowthPaddedStepRows GrowthOrderedBase
open GrowthPaddedStepDecode GrowthPaddedStepCharts SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {T : I.GrowthAttachment X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem private_grade d :
    (carrier P hnext).grade (privateAt P hnext d).1 =
      I.right.scheme.grade d.1 := (congrArg Prod.snd (original_index P hnext
    (I.rightFace.map d.1))).trans (congrArg Prod.snd (I.rightFace.index d.1))

/-- A supplied original owner identifies the actual private lower domain.
The final lifting theorem chooses a maximal such owner from the prescription. -/
theorem owner_capped
    (c : I.right.scheme.below (Finset.univ, k + 1))
    (hc : I.right.scheme.cell c.1 = (Finset.univ, k + 1)) (hg : I.right.scheme.grade c.1 = (k + 1))
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) q)
    {γ} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) u ∧
      (∀ d, u (privateAt P hnext d) = min (p d) (p c)) ∧
      (CappedEq u q γ) ∧ (BoundedBy u (p c)) := by
  
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := GrowthPaddedStepCharts.exists_chart P hk hnext hq
  have hreach  := by
    have he := hag c
    rw [min_eq_right hactive.le] at he
    exact (he.ge.trans (min_le_left _ _)).trans
      (hmax _ ((private_grade P hnext c).trans hg))
  have hchart (d) : min (σ (source P hk hnext a d.1)) γ = min (q d) γ := by
    rw [hread, min_assoc, min_eq_right hreach]
  obtain ⟨S, hS, he⟩ := a.property.2
  have hcanon  :=
    he.symm ▸ a.property.1
  have ha : (⟨S.profile, hcanon, S, hS, rfl⟩ : Catalogue X (k + 1)) = a := Subtype.ext he
  have hprivate (d : I.right.scheme.below (Finset.univ, k + 1)) :
      source P hk hnext a (privateAt P hnext d).1 = S.privateValues d.1 := by
    change source P hk hnext a
      (original P hnext (I.rightFace.map d.1)) = _
    rw [source_original]
    change a.val (GrowthOrderedBase.field I (I.rightFace.map d.1)) = S.privateValues d.1
    rw [← he]
    exact GrowthOrderedBase.field_private T hS d.1
  let toEff := CellScheme.below.mono (D := I.right.scheme)
    (show GradedLe (I.right.scheme.cell c.1) (Finset.univ, k + 1) from by
      rw [hc]; exact GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := I.right.scheme)
    (show GradedLe (Finset.univ, k + 1) (I.right.scheme.cell c.1) from by
      rw [hc]; exact GradedLe.refl _)
  let s := (fun d =>
    S.privateValues d.1) ∘ toEff
  let p' := p ∘ toEff
  have hs' : Semantics.RowLawful I.right.rows c.1 s :=
    hS.private_lawful.mono _
  have hp' : Semantics.RowLawful I.right.rows c.1 p' := hp.mono _
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
  have hb' : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1 := by
    grind
  let v := fac.source ∘ fromEff
  have hv : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) v := fac.lawful.mono _
  obtain ⟨w, hw, hwread, hwcap⟩ := private_source_repair P hk hnext hS hcanon hb' hv
    (fun d => fac.prefix_eq (fromEff d))
  have hcap d : min (fac.outgoing (w d)) γ = min (q d) γ := by
    have hpre := hwcap d
    rw [ha] at hpre
    have hs : Short (I.right.scheme.grade c.1) (source P hk hnext a d.1) := by
      simpa only [hg] using source_short P hk hnext a d.1
    exact (AmbientGradeCharts.map_cap_agreement fac.witness.mono hpre fac.reaches).trans
      ((fac.caps _ hs).trans (hchart d))
  have hν  := by simpa only [hg] using fac.witness
  refine ⟨fun d => fac.outgoing (w d),
    map_respects_of_positive_cap_agreement hw hq (fun d => d.2.2)
      (boundedMap_of_witness hν) (ne_of_gt hpos) hcap, ?_, hcap, fun _ => fac.bounded _⟩
  intro d
  exact (congrArg fac.outgoing (hwread d)).trans (fac.readback (fromEff d))


