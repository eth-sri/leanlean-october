/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyLadderRepair
public import VaughtConjecture.Knight.RankRepair

/-! # From an actual grade-one chart to an admitted LOW replacement

The separator and lawful encoding are constructed, not alignment hypotheses.
The complete LOW fibre supplies the replacement, and bounded decoding orders
the literal prescription. The physical lift consuming this producer is separate.
The rank-table and bounded interpolation proofs are reused from the checked
fixed receiving construction, without importing its LOW/HIGH family.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition
noncomputable section
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

theorem Admissible.profile_visible_one {S} (hS : F.Admissible 1 S)
    d : SelfVis 1 (S.profile d) := by
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

theorem anchor_visible_one a d :
    SelfVis 1 (F.fields 1 a d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  change SelfVis 1 (a.val d)
  rw [← he]
  exact hS.profile_visible_one F d

local instance : Fintype (C.ClippedCells 1) := Fintype.ofFinite _

/-- The chart, prescription and original cap determine a lawful encoded private
source and an actual member of the unchanged birth-grade catalogue. -/
theorem exists_private_rank_repair (a : F.Anchor 1) {σ}
    (hσ : Witness (gTop 1) σ)
    {p : C.scheme.below (effC n 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC n 1) p)
    {γ} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (RankRepair.chart a.val σ (.inr (.inl d.1))) γ = min (p d) γ)
    (c : C.scheme.below (effC n 1)) (hactive : γ < p c) :
    RankRepair.Repaired (fun b : F.Anchor 1 => b.val) a.val (fun d => .inr (.inl d.1)) σ p γ := by
  have hv := F.anchor_visible_one a
  rcases a with ⟨_, hcanon, S, hS, rfl⟩
  apply RankRepair.repair hσ hp hγ hpos hag hactive hcanon hv (fun d => d.2.2.trans (min_le_left _ _)) hS.lawfulC
  intro B p' hp' hp'cap
  obtain ⟨T, _, hT, _, _, ⟨r⟩⟩ := F.private_protected_repair (by decide) hS hcanon hp' hp'cap
  exact ⟨r.anchor, r.decoder, r.witness,
    fun d => (r.readback (.inr (.inl d.1))).trans (congrFun hT d), r.prefix_eq⟩

end
end VaughtConjecture.Knight.LowOnly.Family
