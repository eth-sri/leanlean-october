/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyLadderRepair
public import VaughtConjecture.Knight.ReceivingRankLift

/-! # From an actual grade-one chart to an admitted LOW replacement

The separator and lawful encoding are constructed, not alignment hypotheses.
The complete LOW fibre supplies the replacement, and bounded decoding orders
the literal prescription. The physical lift consuming this producer is separate.
The rank-table and bounded interpolation proofs are reused from the checked
fixed receiving construction, without importing its LOW/HIGH family.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse LadderScalarRendering SharpWitnessComposition

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

theorem Admissible.profile_visible_one {S : State P C} (hS : F.Admissible 1 S)
    (d : Field P C) : SelfVis 1 (S.profile d) := by
  rcases d with d | d | d
  · by_cases hd : 1 < P.scheme.grade d
    · exact hS.futureP d hd
    · have hg : P.scheme.grade d = 1 := le_antisymm (not_lt.mp hd) (P.scheme.grade_pos d)
      exact hg ▸ (hS.lawfulP.orderly
        ⟨d, Finset.subset_univ _, by
          have := F.gap.K_pos; have := F.gap.K_le
          change P.scheme.grade d ≤ min 1 n
          omega⟩).symm
  · by_cases hd : 1 < C.scheme.grade d
    · exact hS.futureC d hd
    · have hg : C.scheme.grade d = 1 := le_antisymm (not_lt.mp hd) (C.scheme.grade_pos d)
      exact hg ▸ (hS.lawfulC.orderly
        ⟨d, Finset.subset_univ _, by
          have := F.gap.K_pos; have := F.gap.K_le
          change C.scheme.grade d ≤ min 1 n
          omega⟩).symm
  · simpa only [State.profile, min_eq_left (Nat.succ_le_of_lt F.gap.K_pos)] using hS.cutoff

theorem anchor_visible_one (a : F.Anchor 1) (d : Field P C) :
    SelfVis 1 (F.fields 1 a d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  change SelfVis 1 (a.val d)
  rw [← he]
  exact hS.profile_visible_one F d

theorem exists_private_rank_repair (a : F.Anchor 1) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ)
    {p : C.scheme.below (effC n 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC n 1) p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (σ (SupportLadderRows.source (RelativeLadderLayer.rungs
        (X := Field P C)) (fieldRank a.val (.inr (.inl d.1))))) γ = min (p d) γ)
    (c : C.scheme.below (effC n 1)) (hactive : γ < p c) :
    ∃ b : F.Anchor 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
      BoundedMap 1 ν ∧
      (∀ f, a.val f < grid 1 B ↔
        σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := Field P C))
          (fieldRank a.val f)) < γ) ∧
      (∀ d, ν (b.val (.inr (.inl d.1))) = p d) ∧
      ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B) := by
  obtain ⟨S, hS, heS⟩ := a.property.2
  exact ReceivingRankLift.exists_rank_repair_of_protected
    (fun d => d.2.2.trans (min_le_left _ _))
    a a.property.1 (F.anchor_visible_one a)
    hσ hp hγ hpos hag c hactive
    (by
      have he : (fun d : C.scheme.below (effC n 1) => a.val (.inr (.inl d.1))) = S.lowerC 1 :=
        funext fun d => (congrFun heS (.inr (.inl d.1))).symm
      exact he ▸ hS.lawfulC)
    fun hp' hp'cap => by
      obtain ⟨T, _, hT, _, _, ⟨r⟩⟩ := F.private_protected_repair (by decide) hS
        (heS.symm ▸ a.property.1) hp'
        (fun d => (hp'cap d).trans (by rw [show a.val (.inr (.inl d.1)) = S.lowerC 1 d from
          (congrFun heS (.inr (.inl d.1))).symm]))
      exact ⟨r.anchor, r.decoder, r.witness,
        fun d => (r.readback (.inr (.inl d.1))).trans (congrFun hT d),
        fun f => (congrArg (fun z => min (z f) (grid 1 _)) heS).symm.trans (r.prefix_eq f).symm⟩
