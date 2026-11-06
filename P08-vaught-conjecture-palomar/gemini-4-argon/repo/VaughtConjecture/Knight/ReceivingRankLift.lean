/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCutDecoder

/-! # Literal lower readback by a cap-preserving rank table

The low rank segment retains the actual ambient chart. The high segment is
the finite maximum of the prescribed values already encountered. Distinct
prescriptions and literal top are retained without synchronizing physical
sections with raw receiving fields.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.ReceivingRankLift
open Transform Value ExtOrd SharpWitnessComposition FullRowLifting LadderScalarRendering

/-- Every occupied rank has an actual field representative. -/
theorem exists_field_rank {X : Type*} [Fintype X] (a : X → ExtOrd) {i : ℕ}
    (hi : 0 < i) (hic : i ≤ (values a).card) : ∃ f, fieldRank a f = i := by
  classical
  let S := values a
  have he : S.image (rank S) = Finset.Icc 1 S.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro n hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Icc.mpr ⟨rank_pos hx, rank_le_card _ _⟩
    · have hinj : Set.InjOn (rank S) S := by
        intro x hx y hy hxy
        rcases lt_trichotomy x y with h | h | h
        · exact ((rank_strict hy h).ne hxy).elim
        · exact h
        · exact ((rank_strict hx h).ne hxy.symm).elim
      rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
      omega
  have hm : i ∈ S.image (rank S) := by rw [he]; exact Finset.mem_Icc.mpr ⟨hi, hic⟩
  obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hm
  obtain ⟨_, f, hf⟩ := mem_values.mp hx
  exact ⟨f, by change rank S (a f) = i; rw [hf]; exact hxi⟩

theorem exists_table {X : Type*} [Finite X] (a b : X → ℕ) (p : X → ExtOrd)
    (f : ℕ → ExtOrd) {k : ℕ} {γ : ExtOrd}
    (hk : 0 < k) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hfv : ∀ i, SelfVis 1 (f i)) (hpv : ∀ d, SelfVis 1 (p d)) (hγ : SelfVis 1 γ)
    (hlow : ∀ i, i < k → f i < γ) (hreach : γ ≤ f k)
    (hprefix : ∀ d, min (a d) k = min (b d) k)
    (hag : ∀ d, min (f (a d)) γ = min (p d) γ)
    (horder : ∀ d e, b d ≤ b e → p d ≤ p e) :
    ∃ g, Monotone g ∧ g 0 = ⊥ ∧ (∀ i, SelfVis 1 (g i)) ∧
      (∀ i, i < k → g i = f i) ∧ γ ≤ g k ∧ ∀ d, g (b d) = p d := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let g (i : ℕ) : ExtOrd :=
    if i < k then f i else max γ ((Finset.univ.filter (fun d => b d ≤ i)).sup p)
  have glow (i) (hi : i < k) : g i = f i := ite_eq_left hi
  have ghigh (i) (hi : k ≤ i) :
      g i = max γ ((Finset.univ.filter (fun d => b d ≤ i)).sup p) := ite_eq_right (not_lt.mpr hi)
  have gh (i) (hi : k ≤ i) : γ ≤ g i := by rw [ghigh i hi]; exact le_max_left _ _
  refine ⟨g, ?_, (glow 0 hk).trans h0, ?_, glow, gh k le_rfl, ?_⟩
  · intro i j hij
    by_cases hj : j < k
    · rw [glow i (hij.trans_lt hj), glow j hj]; exact hf hij
    · by_cases hi : i < k
      · rw [glow i hi]; exact (hlow i hi).le.trans (gh j (not_lt.mp hj))
      · rw [ghigh i (not_lt.mp hi), ghigh j (not_lt.mp hj)]
        exact max_le_max_left _ (Finset.sup_le fun d hd => Finset.le_sup (f := p)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2.trans hij⟩))
  · intro i
    by_cases hi : i < k
    · rw [glow i hi]; exact hfv i
    · rw [ghigh i (not_lt.mp hi)]
      exact selfVis_max hγ (Finset.sup_induction (selfVis_bot 1)
        (fun _ ha _ hb => selfVis_max ha hb) (fun d _ => hpv d))
  · intro d
    by_cases hd : b d < k
    · have he : a d = b d := by have := hprefix d; omega
      rw [glow _ hd]
      exact PairedSlotEncoding.eq_of_cap_eq_lt (he ▸ hag d) (hlow _ hd)
    · have ha : k ≤ a d := by have := hprefix d; omega
      have hpd : γ ≤ p d :=
        min_eq_right_iff.mp ((hag d).symm.trans (min_eq_right (hreach.trans (hf ha))))
      rw [ghigh _ (not_lt.mp hd)]
      exact le_antisymm
        (max_le hpd (Finset.sup_le fun e he => horder e d (Finset.mem_filter.mp he).2))
        ((Finset.le_sup (s := Finset.univ.filter (fun e => b e ≤ b d)) (f := p)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ d, le_rfl⟩)).trans (le_max_right _ _))

theorem exists_rank_decoder (H : ℕ) (g : ℕ → ExtOrd) (hg : Monotone g)
    (h0 : g 0 = ⊥) (hv : ∀ i, SelfVis 1 (g i)) :
    ∃ τ, BoundedMap 1 τ ∧ ∀ i, i ≤ H → τ (SupportLadderRows.source H i) = g i := by
  let s : Fin (H + 1) → ExtOrd := fun i => SupportLadderRows.source H i
  let v : Fin (H + 1) → ExtOrd := fun i => g i
  have ho (i j : Fin (H + 1)) (h : s i ≤ s j) : v i ≤ v j := by
    have hh := (SupportLadderRows.source_le_iff H i j).mp h
    rw [min_eq_left (by omega : i.val ≤ H), min_eq_left (by omega : j.val ≤ H)] at hh
    exact hg hh
  have hz (i : Fin (H + 1)) (h : s i = ⊥) : v i = ⊥ := by
    have hh := (SupportLadderRows.source_bot_iff H i).mp h
    rw [min_eq_left (by omega : i.val ≤ H)] at hh
    exact (congrArg g hh).trans h0
  exact ⟨orderInterpolate s v,
    orderInterpolate_bounded (fun _ => SupportLadderRows.source_visible _ _) (fun i => hv i),
    fun i hi => orderInterpolate_read ho hz ⟨i, by omega⟩⟩

theorem inventory_grid_one {X : Type*} [Fintype X] {a : X → ExtOrd}
    (hc : a ∈ CanonicalPairedProfiles.inventory X 1)
    (hvis : ∀ d, SelfVis 1 (a d)) (d : X) (hd : a d ≠ ⊥) :
    ∃ B, CanonicalPairedInverse.grid 1 B = a d := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp
      (CanonicalPairedProfiles.inventory_coded _ _ hc d) with hz | ⟨b, i, _, _, he⟩
  · exact (hd hz).elim
  have hv := hvis d
  have hs := CanonicalPairedProfiles.inventory_short _ _ hc d
  rw [he, selfVis_ofOrd_iff] at hv
  rw [he] at hs
  simp only [Short, ofOrd_ne_bot, ofOrd_ne_top, false_or, ofOrd_inj] at hs
  obtain ⟨_, rfl, hs⟩ := hs
  have hf : finitePart (Ordinal.omega0 * b + i) = i := by
    simpa only [limitPart_omega0_mul] using finitePart_limitPart_add_nat (Ordinal.omega0 * b) i
  rw [hf] at hv hs
  obtain rfl : i = 1 := le_antisymm hs hv
  exact ⟨b, he.symm⟩

open CanonicalPairedInverse in
theorem exists_rank_repair_of_protected
    {ι X : Type*} [DecidableEq ι] [Fintype X] {A : Finset ι}
    {D : CellScheme A} {sem : Semantics D} {idx : Finset ι × ℕ} {H : ℕ}
    {P_cat : (X → ExtOrd) → Prop} {incl : D.below idx → X}
    (hidx : ∀ d : D.below idx, D.grade d.1 ≤ 1)
    (a : Subtype P_cat)
    (hcanon : a.val ∈ CanonicalPairedProfiles.inventory X 1)
    (hvis : ∀ f, SelfVis 1 (a.val f))
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop 1) σ)
    {p : D.below idx → ExtOrd} (hp : RespectsSemanticsBelow sem idx p)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (σ (SupportLadderRows.source H (fieldRank a.val (incl d)))) γ = min (p d) γ)
    (c : D.below idx) (hactive : γ < p c)
    (hs : RespectsSemanticsBelow sem idx (fun d => a.val (incl d)))
    (hrepair : ∀ {B : ℕ} {p' : D.below idx → ExtOrd},
      RespectsSemanticsBelow sem idx p' →
      (∀ d, min (p' d) (grid 1 B) = min (a.val (incl d)) (grid 1 B)) →
      ∃ b : Subtype P_cat, ∃ δ : ExtOrd → ExtOrd, Witness (gTop 1) δ ∧
        (∀ d, δ (b.val (incl d)) = p' d) ∧
        ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B)) :
    ∃ b : Subtype P_cat, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
      BoundedMap 1 ν ∧
      (∀ f, a.val f < grid 1 B ↔
        σ (SupportLadderRows.source H (fieldRank a.val f)) < γ) ∧
      (∀ d, ν (b.val (incl d)) = p d) ∧
      ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B) := by
  classical
  let : Fintype (D.below idx) := Fintype.ofFinite _
  let v (f : X) : ExtOrd := σ (SupportLadderRows.source H (fieldRank a.val f))
  let high := Finset.univ.filter (fun f => γ ≤ v f)
  have hact : γ ≤ v (incl c) := min_eq_right_iff.mp ((hag c).trans (min_eq_right hactive.le))
  obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image high a.val
    ⟨incl c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩⟩
  have hfg : γ ≤ v f := (Finset.mem_filter.mp hf).2
  have hbot (x) (hx : a.val x = ⊥) : v x = ⊥ := by
    simp only [v, fieldRank, hx, rank_bot (bot_not_values _), SupportLadderRows.source_zero, hσ.bot]
  obtain ⟨B, hB⟩ := inventory_grid_one hcanon hvis f fun hz => hpos.not_ge (hfg.trans_eq (hbot f hz))
  have hcut (d) : a.val d < grid 1 B ↔ v d < γ := by
    rw [hB]
    exact ⟨fun hd => by
      by_contra hn
      exact hd.not_ge (hmin d (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hn⟩)),
      fun hd => by
      by_contra hn
      exact hd.not_ge (hfg.trans (hσ.mono (SupportLadderRows.source_mono H
        (rank_mono (values a.val) (not_lt.mp hn)))))⟩
  let s : D.below idx → ExtOrd := fun d => a.val (incl d)
  have halign (d) (hd : γ < p d) : grid 1 B ≤ s d := not_lt.mp fun hl => by
    have hh := (hcut (incl d)).mp hl
    have he := hag d
    rw [min_eq_left hh.le, min_eq_right hd.le] at he
    exact hh.ne he
  have hroom : grid 1 B < ofOrd (Ordinal.omega0 * (↑(B + 1) : Ordinal)) :=
    ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self B)) 1)
  let p' := AlignedCutEncoding.encode s p 1 (B + 1) (grid 1 B) γ
  have hp' : RespectsSemanticsBelow sem idx p' :=
    AlignedCutEncoding.encode_respects hs hp hidx
      (grid_visible 1 B) (ofOrd_ne_bot _) hγ hroom halign
  obtain ⟨b, δ, hδ, hbread, hbpre⟩ := hrepair hp' (AlignedCutEncoding.encode_cap s p hroom halign)
  obtain ⟨τ, hτ, hτcut, hτread⟩ := ReceivingCutDecoder.exists_chart hvis
    (fun x => by
      have he := hσ.clause5 (SupportLadderRows.source H (fieldRank a.val x)) 1
        (by rw [gTop_of_le le_rfl]; exact le_top) 1 le_rfl
      change SelfVis 1 _
      rw [SupportLadderRows.source_visible] at he
      exact he.symm)
    (grid_visible 1 B) (ofOrd_ne_bot _) hγ
    (fun _ _ h => hσ.mono (SupportLadderRows.source_mono H (rank_mono (values a.val) h)))
    hbot hcut
  let μ := PaddedSourceDecoder.extend (RelativePrefixEncoding.inventory p γ) 1 (B + 1) τ γ
  have hμ : BoundedMap 1 μ := ReceivingCutDecoder.extend_bounded _ hτ hγ
  have hμread (d) : μ (p' d) = p d := by
    apply AlignedCutEncoding.decode_encode s p hτ.mono hroom hτcut.ge
    intro e
    have hh := hτread (incl e)
    change τ (s e) = min (v (incl e)) γ at hh
    rw [hh, min_assoc, min_self]
    exact hag e
  let ν := μ ∘ δ
  have hν : BoundedMap 1 ν :=
    ⟨by dsimp only [ν, Function.comp_apply]; rw [hδ.bot, hμ.bot],
      hμ.mono.comp hδ.mono,
      fun x k i hk hi => by
        dsimp only [ν, Function.comp_apply]
        rw [hδ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi, hμ.comm _ k i hk hi]⟩
  exact ⟨b, ν, B, hν, hcut, fun d => (congrArg μ (hbread d)).trans (hμread d), hbpre⟩
