/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthScalarLedger
public import VaughtConjecture.Knight.RankRepair

/-! # Actual chart to admitted growth source

The first-reaching separator and lawful source prescription are constructed.
The proof adapts the rank encoding of `LowOnlyGradeOneSource`, but consumes
the growth private fibre and the distinct pre-activation donor fibre.
-/

@[expose] public section

namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition
noncomputable section
variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  {F : SemScheme r} {fP : Fin r ↪ Fin (n + 1)}
  {hvP : Finset.univ.image fP ∈ P.scheme.plan} {hP : P.restrictFace fP hvP = F}
  {fC : Fin r ↪ Fin J} {hvC : Finset.univ.image fC ∈ C.scheme.plan}
  {hC : C.restrictFace fC hvC = F}
  (X : RelativeData C.scheme C.rows P.scheme P.rows)
  (R : RootAttachment F fP hvP hP fC hvC hC X)

theorem anchor_visible_one (a : Catalogue X 1) d :
    SelfVis 1 (a.val d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  rw [← he]
  exact hS.visible d

local instance : Fintype (C.Native 1) := Fintype.ofFinite _

include R in
/-- The chart, prescription and original cap determine a lawful encoded private
source and an actual member of the unchanged birth-grade catalogue. -/
theorem exists_private_rank_repair (a : Catalogue X 1) {σ}
    (hσ : Witness (gTop 1) σ)
    {p : C.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (Finset.univ, 1) p)
    {γ} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (RankRepair.chart a.val σ (.inl d.1)) γ = min (p d) γ)
    (c : C.scheme.below (Finset.univ, 1)) (hactive : γ < p c) :
    RankRepair.Repaired (fun b : Catalogue X 1 => b.val) a.val (fun d => .inl d.1) σ p γ := by
  have hv := anchor_visible_one X a
  rcases a with ⟨_, hcanon, S, hS, rfl⟩
  apply RankRepair.repair hσ hp hγ hpos hag hactive hcanon hv (fun d => d.2.2) hS.private_lawful
  intro B p' hp' hp'cap
  obtain ⟨U, _, hU, _, _, _, ⟨r⟩⟩ := R.private_protected_all (by decide) hS hcanon hp' hp'cap
  exact ⟨⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩, r.decoder, r.witness,
    fun d => (r.readback (.inl d.1)).trans (hU d), r.prefix_eq⟩

local instance : Fintype (P.Native 1) := Fintype.ofFinite _

include R in
/-- The chart, prescription and original cap determine a lawful encoded donor
source and an actual member of the unchanged birth-grade catalogue. -/
theorem exists_donor_rank_repair (hN : 1 < X.req.N) (a : Catalogue X 1) {σ}
    (hσ : Witness (gTop 1) σ)
    {p : P.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (Finset.univ, 1) p)
    {γ} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (RankRepair.chart a.val σ (.inr d.1)) γ = min (p d) γ)
    (c : P.scheme.below (Finset.univ, 1)) (hactive : γ < p c) :
    RankRepair.Repaired (fun b : Catalogue X 1 => b.val) a.val (fun d => .inr d.1) σ p γ := by
  have hv := anchor_visible_one X a
  rcases a with ⟨_, hcanon, S, hS, rfl⟩
  apply RankRepair.repair hσ hp hγ hpos hag hactive hcanon hv (fun d => d.2.2) hS.donor_lawful
  intro B p' hp' hp'cap
  obtain ⟨U, _, hU, _, _, _, ⟨r⟩⟩ := R.donor_protected_before (by decide) hN hS hcanon hp' hp'cap
  exact ⟨⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩, r.decoder, r.witness,
    fun d => (r.readback (.inr d.1)).trans (hU d), r.prefix_eq⟩

end
end VaughtConjecture.Knight.Growth
