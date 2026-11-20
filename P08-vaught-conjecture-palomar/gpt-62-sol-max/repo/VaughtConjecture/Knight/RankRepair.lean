/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingRankLift
public import VaughtConjecture.Knight.RelativeLadderLayer
public import VaughtConjecture.Knight.AlignedCutEncoding
public import VaughtConjecture.Knight.CanonicalPairedProfiles
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization

public import VaughtConjecture.Knight.TerminalProfile

@[expose] public section

namespace VaughtConjecture.Knight.RankRepair

open Transform Value ExtOrd CanonicalPairedInverse LadderScalarRendering SharpWitnessComposition

noncomputable section

variable {X Q : Type*} [Fintype X]

abbrev IsRepair {α : Type*} (fields : Q → X → ExtOrd) (lawful : (α → ExtOrd) → Prop)
    (pick : α → X) : Prop :=
  ∀ (a : Q) {σ : ExtOrd → ExtOrd}, Witness (gTop 1) σ →
    ∀ {p : α → ExtOrd}, lawful p → ∀ {γ : ExtOrd}, SelfVis 1 γ → ⊥ < γ →
    (∀ d, min (σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := X))
      (fieldRank (fields a) (pick d)))) γ = min (p d) γ) →
    ∀ c, γ < p c →
    ∃ b : Q, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ, BoundedMap 1 ν ∧
      (∀ f, fields a f < grid 1 B ↔
        σ (SupportLadderRows.source (RelativeLadderLayer.rungs (X := X)) (fieldRank (fields a) f)) < γ) ∧
      (∀ d, ν (fields b (pick d)) = p d) ∧
      ∀ f, min (fields a f) (grid 1 B) = min (fields b f) (grid 1 B)

/-- A nonbottom canonical, visible field of grade one lies at a grid endpoint. -/
theorem grid_one {p : X → ExtOrd} (hc : p ∈ CanonicalPairedProfiles.inventory X 1)
    (d : X) (hvis : SelfVis 1 (p d)) (hd : p d ≠ ⊥) : ∃ B, grid 1 B = p d := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp (CanonicalPairedProfiles.inventory_coded _ _ hc d) with
    hz | ⟨b, i, _, _, he⟩
  · lia
  have hs := CanonicalPairedProfiles.inventory_short _ _ hc d
  rw [he, selfVis_ofOrd_iff] at hvis
  rw [he] at hs
  simp only [Short, ofOrd_ne_bot, ofOrd_ne_top, false_or, ofOrd_inj] at hs
  obtain ⟨_, rfl, hs⟩ := hs
  have hf : finitePart (Ordinal.omega0 * b + i) = i := by
    simpa [limitPart_omega0_mul] using finitePart_limitPart_add_nat (Ordinal.omega0 * b) i
  rw [hf] at hvis hs
  obtain rfl : i = 1 := le_antisymm hs hvis
  exact ⟨b, he.symm⟩

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- A repair of the encoded tail gives a repair at the original cap. -/
theorem of_protected (fields : Q → X → ExtOrd) (pick : D.below BJ → X) (hj : BJ.2 ≤ 1)
    (vis : ∀ a f, SelfVis 1 (fields a f))
    (grid_mem : ∀ a f, fields a f ≠ ⊥ → ∃ B, grid 1 B = fields a f)
    (lawful : ∀ a, RespectsSemanticsBelow sem BJ (fun d => fields a (pick d)))
    (repair : ∀ (a : Q) (B : ℕ) {p' : D.below BJ → ExtOrd},
      RespectsSemanticsBelow sem BJ p' →
      (∀ d, min (p' d) (grid 1 B) = min (fields a (pick d)) (grid 1 B)) →
      ∃ b τ, Witness (gTop 1) τ ∧ (∀ d, τ (fields b (pick d)) = p' d) ∧
        ∀ f, min (fields a f) (grid 1 B) = min (fields b f) (grid 1 B)) :
    IsRepair fields (RespectsSemanticsBelow sem BJ) pick := by
  intro a σ hσ p hp γ hγ hpos hag c hactive
  classical
  let _ := Fintype.ofFinite (D.below BJ)
  let H := RelativeLadderLayer.rungs (X := X)
  let v : X → ExtOrd :=
    fun f => σ (SupportLadderRows.source H (fieldRank (fields a) f))
  let high := Finset.univ.filter (fun f => γ ≤ v f)
  have hact : γ ≤ v (pick c) :=
    min_eq_right_iff.mp ((hag c).trans (min_eq_right hactive.le))
  obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image high (fields a)
    ⟨pick c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩⟩
  have hfg : γ ≤ v f := (Finset.mem_filter.mp hf).2
  have hbot (x) (hx : (fields a) x = ⊥) : v x = ⊥ := by
    simp [v, fieldRank, hx, rank_bot (bot_not_values _), SupportLadderRows.source_zero,
      hσ.bot]
  have hfb : (fields a) f ≠ ⊥ := by grind
  obtain ⟨B, hB⟩ := grid_mem a f hfb
  have hcut (d) : (fields a) d < grid 1 B ↔ v d < γ := by
    rw [hB]
    constructor
    · grind
    · intro hd
      by_contra hn
      exact hd.not_ge (hfg.trans (hσ.mono (SupportLadderRows.source_mono H
        (rank_mono (values (fields a)) (not_lt.mp hn)))))
  let s : D.below BJ → ExtOrd := fun d => (fields a) (pick d)
  have halign (d) (hd : γ < p d) : grid 1 B ≤ s d := by
    grind
  have hroom : grid 1 B < ofOrd (Ordinal.omega0 * (↑(B + 1) : Ordinal)) :=
    ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self B)) 1)
  have hs : RespectsSemanticsBelow sem BJ s := lawful a
  let p' := AlignedCutEncoding.encode s p 1 (B + 1) (grid 1 B) γ
  have hp' : RespectsSemanticsBelow sem BJ p' :=
    AlignedCutEncoding.encode_respects hs hp (fun d => d.2.2.trans hj)
      (grid_visible 1 B) (ofOrd_ne_bot _) hγ hroom halign
  obtain ⟨b, θ, hθ, hread, hpref⟩ := repair a B hp' (AlignedCutEncoding.encode_cap s p hroom halign)
  obtain ⟨τ, hτ, hτcut, hτread⟩ := ReceivingCutDecoder.exists_chart
    (vis a)
    (fun f => CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _))
    (grid_visible 1 B) (ofOrd_ne_bot _) hγ
    (fun f g h => hσ.mono (SupportLadderRows.source_mono H (rank_mono (values (fields a)) h)))
    hbot hcut
  let μ := PaddedSourceDecoder.extend (RelativePrefixEncoding.inventory p γ) 1 (B + 1) τ γ
  have hμ : BoundedMap 1 μ := ReceivingCutDecoder.extend_bounded _ hτ hγ
  have hμread (d) : μ (p' d) = p d := by
    apply AlignedCutEncoding.decode_encode s p hτ.mono hroom hτcut.ge
    intro e
    have hh := hτread (pick e)
    change τ (s e) = min (v (pick e)) γ at hh
    grind
  refine ⟨b, μ ∘ θ, B, ?_, hcut, by grind, hpref⟩
  exact ⟨by simp [Function.comp_apply, hθ.bot, hμ.bot], hμ.mono.comp hθ.mono,
    fun x k i hk hi => by
      simp only [Function.comp_apply]
      rw [hθ.comm x hk hi, hμ.comm _ k i hk hi]⟩

/-- A scalar prescription, together with repair of the full canonical profile,
induces a rank repair on the projected lower set. -/
theorem of_catalogue {S : Type*} (C : TerminalProfile.Context S X)
    (pick : D.below BJ → X) (hj : BJ.2 ≤ 1)
    (vis : ∀ s, C.admitted 1 s → ∀ f, SelfVis 1 (C.profile s f))
    (lawful : ∀ s, C.admitted 1 s → RespectsSemanticsBelow sem BJ (fun d => C.profile s (pick d)))
    (prescribe : ∀ {s B}, C.admitted 1 s → C.profile s ∈ CanonicalPairedProfiles.inventory X 1 →
      ∀ {p : D.below BJ → ExtOrd}, RespectsSemanticsBelow sem BJ p →
      (∀ d, min (p d) (grid 1 B) = min (C.profile s (pick d)) (grid 1 B)) →
      ∃ t, (∀ d, C.profile t (pick d) = p d) ∧ Nonempty (C.ProtectedRepair (C.profile s) t 1 B)) :
    IsRepair (fun a : ↥(CanonicalPairedProfiles.Realized X 1 C.profile (C.admitted 1)) => a.val)
      (RespectsSemanticsBelow sem BJ) pick := by
  have visible (a : ↥(CanonicalPairedProfiles.Realized X 1 C.profile (C.admitted 1))) (f : X) :
      SelfVis 1 (a.val f) := by
    obtain ⟨s, hs, he⟩ := a.property.2
    rw [← he]
    exact vis s hs f
  apply of_protected _ pick hj visible (fun a f => grid_one a.property.1 f (visible a f))
  · intro a
    obtain ⟨s, hs, he⟩ := a.property.2
    rw [← he]
    exact lawful s hs
  · intro a B p hp hcap
    obtain ⟨s, hs, he⟩ := a.property.2
    obtain ⟨t, ht, ⟨r⟩⟩ := prescribe hs (he.symm ▸ a.property.1) hp (by rwa [he])
    refine ⟨⟨C.profile r.encoded, r.canonical, r.encoded, r.admitted, rfl⟩, r.decoder, r.witness,
      fun d => (r.readback _).trans (ht d), fun f => ?_⟩
    rw [← he]
    exact (r.prefix_eq f).symm

end

end VaughtConjecture.Knight.RankRepair
