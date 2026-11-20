/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingRankLift
public import VaughtConjecture.Knight.RelativeLadderLayer
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.AlignedCutEncoding

/-! # Rank repair on a face of a grade-one catalogue

Only the protected replacement depends on the catalogue and on which face is
being repaired. The choice of separator, alignment and decoding are common.
-/

@[expose] public section
namespace VaughtConjecture.Knight.RankRepair
open Transform Value ExtOrd LadderScalarRendering CanonicalPairedInverse SharpWitnessComposition
noncomputable section
variable {X : Type*} [Fintype X]

/-- A positive visible canonical grade-one field is a grid endpoint. -/
theorem exists_grid {s : X → ExtOrd} (hs : s ∈ CanonicalPairedProfiles.inventory X 1) (f : X)
    (hv : SelfVis 1 (s f)) (hp : s f ≠ ⊥) : ∃ B, grid 1 B = s f := by
  rcases mem_codedAlphabet_iff.mp (CanonicalPairedProfiles.inventory_coded _ _ hs f) with h | ⟨b,i,_,_,he⟩
  · contradiction
  have h := CanonicalPairedProfiles.inventory_short _ _ hs f
  rw [he, selfVis_ofOrd_iff] at hv
  simp only [he, Short, ofOrd_ne_bot, ofOrd_ne_top, false_or, ofOrd_inj] at h
  obtain ⟨_, rfl, h⟩ := h
  have hf : finitePart (Ordinal.omega0 * b + i) = i := by
    simpa only [limitPart_omega0_mul] using finitePart_limitPart_add_nat (Ordinal.omega0 * b) i
  rw [hf] at hv h
  obtain rfl : i = 1 := le_antisymm h hv
  exact ⟨b, he.symm⟩

abbrev chart (s : X → ExtOrd) (σ : ExtOrd → ExtOrd) (f : X) :=
  σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := X)) (fieldRank s f))

variable {Y Q : Type*}

def Repaired (profile : Q → X → ExtOrd) (s : X → ExtOrd) (face : Y → X)
    (σ : ExtOrd → ExtOrd) (p : Y → ExtOrd) (γ : ExtOrd) : Prop :=
  ∃ b ν B, BoundedMap 1 ν ∧ (∀ f, s f < grid 1 B ↔ chart s σ f < γ) ∧
    (∀ d, ν (profile b (face d)) = p d) ∧ ∀ f, min (s f) (grid 1 B) = min (profile b f) (grid 1 B)

theorem repair {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}
    {BJ : Finset ι × ℕ} [Fintype (D.below BJ)] {profile : Q → X → ExtOrd}
    {s : X → ExtOrd} {face : D.below BJ → X} {σ : ExtOrd → ExtOrd} {p : D.below BJ → ExtOrd}
    {γ : ExtOrd} (hσ : Witness (gTop 1) σ) (hp : RespectsSemanticsBelow sem BJ p)
    (hγ : SelfVis 1 γ) (hpos : ⊥ < γ) (hag : ∀ d, min (chart s σ (face d)) γ = min (p d) γ)
    {c} (hactive : γ < p c) (hcanonical : s ∈ CanonicalPairedProfiles.inventory X 1)
    (hvis : ∀ f, SelfVis 1 (s f)) (hgrade : ∀ d : D.below BJ, D.grade d.1 ≤ 1)
    (hs : RespectsSemanticsBelow sem BJ (s ∘ face))
    (replace : ∀ B (p' : D.below BJ → ExtOrd), RespectsSemanticsBelow sem BJ p' →
      (∀ d, min (p' d) (grid 1 B) = min (s (face d)) (grid 1 B)) →
      ∃ b τ, Witness (gTop 1) τ ∧ (∀ d, τ (profile b (face d)) = p' d) ∧
        ∀ f, min (profile b f) (grid 1 B) = min (s f) (grid 1 B)) : Repaired profile s face σ p γ := by
  classical
  let v := chart s σ
  let H := RelativeLadderLayer.rungs (X := X)
  have hmono (f g) (h : s f ≤ s g) : v f ≤ v g :=
    hσ.mono (SupportLadderRows.source_mono H (rank_mono (values s) h))
  have hbot (f) (h : s f = ⊥) : v f = ⊥ := by
    simp [v, chart, fieldRank, h, rank_bot (bot_not_values _), SupportLadderRows.source_zero, hσ.bot]
  let high := Finset.univ.filter (fun f => γ ≤ v f)
  have hact : γ ≤ v (face c) := min_eq_right_iff.mp ((hag c).trans (min_eq_right hactive.le))
  obtain ⟨f,hf,hmin⟩ := Finset.exists_min_image high s ⟨face c, by simpa [high] using hact⟩
  have hfg : γ ≤ v f := (Finset.mem_filter.mp hf).2
  obtain ⟨B,hB⟩ := exists_grid hcanonical f (hvis f) (fun h => hpos.not_ge (hfg.trans_eq (hbot f h)))
  have cut (d) : s d < grid 1 B ↔ v d < γ := by
    rw [hB, ← not_le, ← not_le (b := v d)]
    exact not_congr ⟨fun h => hfg.trans (hmono _ _ h), fun h => hmin _ (by simpa [high] using h)⟩
  have align (d) (hd : γ < p d) : grid 1 B ≤ s (face d) :=
    le_of_not_gt (fun h => (cut _).mp h |>.not_ge (min_eq_right_iff.mp ((hag d).trans (min_eq_right hd.le))))
  have room : grid 1 B < ofOrd (Ordinal.omega0 * (↑(B + 1) : Ordinal)) :=
    ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self B)) 1)
  let p' := AlignedCutEncoding.encode (s ∘ face) p (B + 1) (grid 1 B) γ
  obtain ⟨b, τ, hτ, hr, hpre⟩ := replace B p'
    (AlignedCutEncoding.encode_respects hs hp hgrade (grid_visible 1 B) (ofOrd_ne_bot _) hγ room align)
    (AlignedCutEncoding.encode_cap _ p room align)
  obtain ⟨ρ, hρ, hcut, hread⟩ := ReceivingCutDecoder.exists_chart hvis
    (fun f => CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _))
    (grid_visible 1 B) (ofOrd_ne_bot _) hγ hmono hbot cut
  let μ := PaddedSourceDecoder.extend (B + 1) ρ γ
  have hμ : BoundedMap 1 μ := ReceivingCutDecoder.extend_bounded hρ hγ
  refine ⟨b, μ ∘ τ, B, BoundedMap.comp_witness hμ hτ le_rfl, cut, fun d => (congrArg μ (hr d)).trans ?_, fun f => (hpre f).symm⟩
  exact AlignedCutEncoding.decode_encode _ p hρ.mono room hcut.ge (fun e => by
    change min (ρ (s (face e))) γ = _
    rw [hread, min_assoc, min_self]; exact hag e) d

end
end VaughtConjecture.Knight.RankRepair
