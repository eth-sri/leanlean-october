/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthScalarLedger
public import VaughtConjecture.Knight.ReceivingRankLift
public import VaughtConjecture.Knight.RelativeLadderLayer

/-! # Actual chart to admitted growth source

The first-reaching separator and lawful source prescription are constructed.
The proof adapts the rank encoding of `LowOnlyGradeOneSource`, but consumes
the growth private fibre and the distinct pre-activation donor fibre.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse LadderScalarRendering SharpWitnessComposition

variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  {F : SemScheme r} {fP : Fin r ↪ Fin (n + 1)}
  {hvP : Finset.univ.image fP ∈ P.scheme.plan} {hP : P.restrictFace fP hvP = F}
  {fC : Fin r ↪ Fin J} {hvC : Finset.univ.image fC ∈ C.scheme.plan}
  {hC : C.restrictFace fC hvC = F}
  (X : RelativeData C.scheme C.rows P.scheme P.rows)
  (R : RootAttachment F fP hvP hP fC hvC hC X)

theorem anchor_visible_one (a : Catalogue X 1) (d : Field C.scheme P.scheme) :
    SelfVis 1 (a.val d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  rw [← he]
  exact hS.visible d

include R in
theorem exists_private_rank_repair (a : Catalogue X 1) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ)
    {p : C.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (Finset.univ, 1) p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (σ (SupportLadderRows.source (RelativeLadderLayer.rungs
        (X := Field C.scheme P.scheme)) (fieldRank a.val (.inl d.1)))) γ = min (p d) γ)
    (c : C.scheme.below (Finset.univ, 1)) (hactive : γ < p c) :
    ∃ b : Catalogue X 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
      BoundedMap 1 ν ∧
      (∀ f, a.val f < grid 1 B ↔
        σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := Field C.scheme P.scheme))
          (fieldRank a.val f)) < γ) ∧
      (∀ d, ν (b.val (.inl d.1)) = p d) ∧
      ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B) := by
  obtain ⟨S, hS, heS⟩ := a.property.2
  exact ReceivingRankLift.exists_rank_repair_of_protected (fun d => d.2.2)
    a a.property.1 (anchor_visible_one X a)
    hσ hp hγ hpos hag c hactive
    (by
      have he : (fun d : C.scheme.below (Finset.univ, 1) => a.val (.inl d.1)) =
          fun d => S.privateValues d.1 :=
        funext fun d => (congrFun heS (.inl d.1)).symm
      exact he ▸ hS.private_lawful)
    fun hp' hp'cap => by
      obtain ⟨U, _, hU, _, _, _, ⟨r⟩⟩ := R.private_protected_all (by decide) hS
        (heS.symm ▸ a.property.1) hp'
        (fun d => (hp'cap d).trans (by rw [show a.val (.inl d.1) = S.privateValues d.1 from
          (congrFun heS (.inl d.1)).symm]))
      exact ⟨⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩,
        r.decoder, r.witness, fun d => (r.readback (.inl d.1)).trans (hU d),
        fun f => (congrArg (fun z => min (z f) (grid 1 _)) heS).symm.trans (r.prefix_eq f).symm⟩

include R in
theorem exists_donor_rank_repair (hN : 1 < X.req.N) (a : Catalogue X 1) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop 1) σ)
    {p : P.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (Finset.univ, 1) p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (σ (SupportLadderRows.source (RelativeLadderLayer.rungs
        (X := Field C.scheme P.scheme)) (fieldRank a.val (.inr d.1)))) γ = min (p d) γ)
    (c : P.scheme.below (Finset.univ, 1)) (hactive : γ < p c) :
    ∃ b : Catalogue X 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
      BoundedMap 1 ν ∧
      (∀ f, a.val f < grid 1 B ↔
        σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := Field C.scheme P.scheme))
          (fieldRank a.val f)) < γ) ∧
      (∀ d, ν (b.val (.inr d.1)) = p d) ∧
      ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B) := by
  obtain ⟨S, hS, heS⟩ := a.property.2
  exact ReceivingRankLift.exists_rank_repair_of_protected (fun d => d.2.2)
    a a.property.1 (anchor_visible_one X a)
    hσ hp hγ hpos hag c hactive
    (by
      have he : (fun d : P.scheme.below (Finset.univ, 1) => a.val (.inr d.1)) =
          fun d => S.donorValues d.1 :=
        funext fun d => (congrFun heS (.inr d.1)).symm
      exact he ▸ hS.donor_lawful)
    fun hp' hp'cap => by
      obtain ⟨U, _, hU, _, _, _, ⟨r⟩⟩ := R.donor_protected_before (by decide) hN hS
        (heS.symm ▸ a.property.1) hp'
        (fun d => (hp'cap d).trans (by rw [show a.val (.inr d.1) = S.donorValues d.1 from
          (congrFun heS (.inr d.1)).symm]))
      exact ⟨⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩,
        r.decoder, r.witness, fun d => (r.readback (.inr d.1)).trans (hU d),
        fun f => (congrArg (fun z => min (z f) (grid 1 _)) heS).symm.trans (r.prefix_eq f).symm⟩
