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

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition
noncomputable section
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

local instance donorSourceFintype : Fintype (P.ClippedCells 1) := Fintype.ofFinite _

/-- The chart, prescription and original cap determine a lawful encoded donor
source and an actual member of the unchanged birth-grade catalogue. -/
theorem exists_donor_rank_repair (a : F.Anchor 1) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ)
    {p : P.ClippedCells 1 → ExtOrd}
    (hp : P.rows.Lawful p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (RankRepair.chart a.val σ (.inl d.1)) γ = min (p d) γ)
    (c : P.ClippedCells 1) (hactive : γ < p c) :
    RankRepair.Repaired (fun b : F.Anchor 1 => b.val) a.val (fun d => .inl d.1) σ p γ := by
  have hv := F.anchor_visible_one a
  rcases a with ⟨_, hcanon, S, hS, rfl⟩
  apply RankRepair.repair hσ hp hγ hpos hag hactive hcanon hv (fun d => d.2.2.trans (min_le_left _ _)) hS.lawfulP
  intro B p' hp' hp'cap
  obtain ⟨T, _, hT, _, _, ⟨r⟩⟩ := F.donor_protected_repair (by decide) hS hcanon hp' hp'cap
  exact ⟨r.anchor, r.decoder, r.witness,
    fun d => (r.readback (.inl d.1)).trans (congrFun hT d), r.prefix_eq⟩

end
end VaughtConjecture.Knight.LowOnly.Family
