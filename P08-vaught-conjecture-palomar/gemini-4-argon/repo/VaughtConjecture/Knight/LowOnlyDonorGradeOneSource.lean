/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyGradeOneSource

/-! # Donor-side source repair from an actual grade-one chart

The first-reaching represented cut and rank decoding follow
`LowOnlyGradeOneSource.exists_private_rank_repair`. The lawfulness input is the
actual donor restriction, and the asymmetric step consumes
`donor_protected_repair`. The LOW family and its two face roles are never swapped.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse LadderScalarRendering SharpWitnessComposition

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

theorem exists_donor_rank_repair (a : F.Anchor 1) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ)
    {p : P.scheme.below (effC n 1) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (effC n 1) p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (σ (SupportLadderRows.source (RelativeLadderLayer.rungs
        (X := Field P C)) (fieldRank a.val (.inl d.1)))) γ = min (p d) γ)
    (c : P.scheme.below (effC n 1)) (hactive : γ < p c) :
    ∃ b : F.Anchor 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
      BoundedMap 1 ν ∧
      (∀ f, a.val f < grid 1 B ↔
        σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := Field P C))
          (fieldRank a.val f)) < γ) ∧
      (∀ d, ν (b.val (.inl d.1)) = p d) ∧
      ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B) := by
  obtain ⟨S, hS, heS⟩ := a.property.2
  exact ReceivingRankLift.exists_rank_repair_of_protected
    (fun d => d.2.2.trans (min_le_left _ _))
    a a.property.1 (F.anchor_visible_one a)
    hσ hp hγ hpos hag c hactive
    (by
      have he : (fun d : P.scheme.below (effC n 1) => a.val (.inl d.1)) = S.lowerP 1 :=
        funext fun d => (congrFun heS (.inl d.1)).symm
      exact he ▸ hS.lawfulP)
    fun hp' hp'cap => by
      obtain ⟨T, _, hT, _, _, ⟨r⟩⟩ := F.donor_protected_repair (by decide) hS
        (heS.symm ▸ a.property.1) hp'
        (fun d => (hp'cap d).trans (by rw [show a.val (.inl d.1) = S.lowerP 1 d from
          (congrFun heS (.inl d.1)).symm]))
      exact ⟨r.anchor, r.decoder, r.witness,
        fun d => (r.readback (.inl d.1)).trans (congrFun hT d),
        fun f => (congrArg (fun z => min (z f) (grid 1 _)) heS).symm.trans (r.prefix_eq f).symm⟩
