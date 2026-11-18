/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCatalogueIncidences
public import VaughtConjecture.Knight.RelativeLadderLayer
public import VaughtConjecture.Knight.AmbientGradeCharts

@[expose] public section

namespace VaughtConjecture.Knight
open Transform Value ExtOrd SharpWitnessComposition FullRowLifting

namespace RelativeLadderLayer
noncomputable section
variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → X) (fields : Q → X → ExtOrd) (hp : ∀ d, D.scope d ≠ A)

def leafOccurrence (a : Q) : (carrier D hA (X := X) (Q := Q)).below (A, 1) :=
  ⟨added D hA (SupportLadderRows.leaf (Nat.succ_pos _) a), by
    rw [added_index]; exact GradedLe.refl _⟩

theorem exists_leaf_chart (seed : Q)
    {q : (carrier D hA (X := X) (Q := Q)).below (A, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows D sem hA field fields hp) (A, 1) q) :
    ∃ a : Q, ∃ τ : ExtOrd → ExtOrd, Witness (gTop 1) τ ∧
      (∀ x, τ x ≤ q (leafOccurrence D hA a)) ∧
      ∀ d, τ (ladderRow D hA field fields
        (SupportLadderRows.leaf (Nat.succ_pos _) a) d.1) = q d := by
  obtain ⟨chart⟩ := AmbientGradeCharts.exists_chart hq
    ⟨leafOccurrence D hA seed, added_index D hA _⟩
  have hg (d : (carrier D hA (X := X) (Q := Q)).below (A, 1)) :
      (carrier D hA (X := X) (Q := Q)).grade d.1 = 1 :=
    le_antisymm d.2.2 ((carrier D hA).grade_pos d.1)
  obtain ⟨v, hv⟩ : ∃ v, chart.owner.1 = added D hA v := by
    rcases cell_cases D hA chart.owner.1 with ⟨c, hc⟩ | hv
    · have he := chart.index; rw [hc, old_index] at he
      exact (hp c (congrArg Prod.fst he)).elim
    · exact hv
  have hr0 (d : (carrier D hA (X := X) (Q := Q)).below (A, 1)) :
      chart.shift (ladderRow D hA field fields v d.1) = q d := by
    have hh := chart.read_grade d (hg d)
    have he : (rows D sem hA field fields hp).E chart.owner.1
        (chart.occurrence d (hg d).le) = ladderRow D hA field fields v d.1 := by
      simp only [rows, hv, view, added, SourceLayerCarrier.toOcc_toCell,
        AmbientGradeCharts.Chart.occurrence]
    rwa [he] at hh
  let a := SupportLadderRows.parent v
  have hmax (d : (carrier D hA (X := X) (Q := Q)).below (A, 1)) :
      q d ≤ q (leafOccurrence D hA a) := by
    have he : ladderRow D hA field fields v (leafOccurrence D hA a).1 =
        ladderRow D hA field fields v chart.owner.1 := by
      rw [hv]
      simp only [leafOccurrence, ladderRow, image, rankIndex_added]
      exact SupportLadderRows.row_parent (fun a x => (rank_bound fields a x).le) (Nat.succ_pos _) v
    exact (chart.dominates d (hg d)).trans_eq (by rw [← hr0, ← hr0, he])
  let c := leafOccurrence (X := X) D hA a
  have hgc : (carrier D hA (X := X) (Q := Q)).grade c.1 = 1 :=
    congrArg Prod.snd (added_index D hA _)
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness
    (c := (⟨c.1, GradedLe.refl _⟩ : (carrier D hA (X := X) (Q := Q)).below ((carrier D hA).cell c.1)))
    (fun d => d.2.2) (hq.orderly c).symm (hq.locality c)
  refine ⟨a, τ, hgc ▸ hτ, hb, fun d => ?_⟩
  let e : (carrier D hA (X := X) (Q := Q)).below ((carrier D hA).cell c.1) :=
    ⟨d.1, by simpa only [c, leafOccurrence, added_index] using d.2⟩
  have hh := hr e
  have he := row_added D sem hA field fields hp (SupportLadderRows.leaf (Nat.succ_pos _) a) e
  change (rows D sem hA field fields hp).E c.1 e =
    ladderRow D hA field fields (SupportLadderRows.leaf (Nat.succ_pos _) a) d.1 at he
  rw [he] at hh
  exact hh.trans (min_eq_left (hmax d))
end
end RelativeLadderLayer

namespace ReceivingRankLift
open LadderScalarRendering
noncomputable section

private theorem exists_cut_chart {X : Type*} [Fintype X] {s v : X → ExtOrd} {δ γ : ExtOrd}
    (hs : ∀ f, SelfVis 1 (s f)) (hv : ∀ f, SelfVis 1 (v f))
    (hδ : SelfVis 1 δ) (hδb : δ ≠ ⊥) (hγ : SelfVis 1 γ)
    (hord : ∀ f g, s f ≤ s g → v f ≤ v g)
    (hbot : ∀ f, s f = ⊥ → v f = ⊥)
    (hcut : ∀ f, s f < δ ↔ v f < γ) :
    ∃ τ, BoundedMap 1 τ ∧ τ δ = γ ∧ ∀ f, τ (s f) = min (v f) γ := by
  let E : Option X → ExtOrd := fun d => d.elim δ s
  let t : Option X → ExtOrd := fun d => d.elim γ (fun f => min (v f) γ)
  have horder (d e : Option X) (h : E d ≤ E e) : t d ≤ t e := by
    cases d with
    | none => cases e with
      | none => exact le_rfl
      | some f => exact le_min (not_lt.mp fun hf => ((hcut f).mpr hf).not_ge h) le_rfl
    | some f => cases e with
      | none => exact min_le_right _ _
      | some g => exact min_le_min_right _ (hord f g h)
  have hzero (d : Option X) (hd : E d = ⊥) : t d = ⊥ := by
    cases d with
    | none => exact (hδb hd).elim
    | some f => exact (congrArg (fun x => min x γ) (hbot f hd)).trans (min_bot_left _)
  exact ⟨orderInterpolate E t,
    orderInterpolate_bounded (fun | none => hδ | some f => hs f)
      (fun | none => hγ | some f => selfVis_min (hv f) hγ),
    orderInterpolate_read horder hzero none, fun f => orderInterpolate_read horder hzero (some f)⟩

theorem exists_field_rank {X : Type*} [Fintype X] (a : X → ExtOrd) {i : ℕ}
    (hi : 0 < i) (hic : i ≤ (values a).card) : ∃ f, fieldRank a f = i := by
  classical
  let S := values a
  have he : S.image (rank S) = Finset.Icc 1 S.card := by
    refine Finset.eq_of_subset_of_card_le (fun n hn => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Icc.mpr ⟨rank_pos hx, rank_le_card _ _⟩
    · have hinj : Set.InjOn (rank S) S := fun x hx y hy hxy => by
        rcases lt_trichotomy x y with h | h | h
        · exact ((rank_strict hy h).ne hxy).elim
        · exact h
        · exact ((rank_strict hx h).ne hxy.symm).elim
      rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]; omega
  obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp (he.symm ▸ Finset.mem_Icc.mpr ⟨hi, hic⟩)
  obtain ⟨_, f, hf⟩ := mem_values.mp hx
  exact ⟨f, by change rank S (a f) = i; rw [hf]; exact hxi⟩

open Classical in
def table {X : Type*} [Fintype X] (r : X → ℕ) (p : X → ExtOrd)
    (f : ℕ → ExtOrd) (k : ℕ) (γ : ExtOrd) (i : ℕ) : ExtOrd :=
  if i < k then f i else max γ ((Finset.univ.filter (fun d => r d ≤ i)).sup p)

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
  let g := table b p f k γ
  have glow (i) (hi : i < k) : g i = f i := ite_eq_left hi
  have ghigh (i) (hi : k ≤ i) :
      g i = max γ ((Finset.univ.filter (fun d => b d ≤ i)).sup p) := ite_eq_right (not_lt.mpr hi)
  have gh (i) (hi : k ≤ i) : γ ≤ g i := by rw [ghigh i hi]; exact le_max_left _ _
  refine ⟨g, fun i j hij => ?_, (glow 0 hk).trans h0, fun i => ?_, glow, gh k le_rfl, fun d => ?_⟩
  · by_cases hj : j < k
    · rw [glow i (hij.trans_lt hj), glow j hj]; exact hf hij
    · by_cases hi : i < k
      · rw [glow i hi]; exact (hlow i hi).le.trans (gh j (not_lt.mp hj))
      · rw [ghigh i (not_lt.mp hi), ghigh j (not_lt.mp hj)]
        exact max_le_max_left _ (Finset.sup_le fun d hd => Finset.le_sup (f := p)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2.trans hij⟩))
  · by_cases hi : i < k
    · rw [glow i hi]; exact hfv i
    · rw [ghigh i (not_lt.mp hi)]
      exact selfVis_max hγ (Finset.sup_induction (selfVis_bot 1)
        (fun _ ha _ hb => selfVis_max ha hb) fun d _ => hpv d)
  · by_cases hd : b d < k
    · have he : a d = b d := by have := hprefix d; omega
      rw [glow _ hd]; exact PairedSlotEncoding.eq_of_cap_eq_lt (he ▸ hag d) (hlow _ hd)
    · have ha : k ≤ a d := by have := hprefix d; omega
      have hpd : γ ≤ p d := min_eq_right_iff.mp ((hag d).symm.trans (min_eq_right (hreach.trans (hf ha))))
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
    orderInterpolate_bounded (fun _ => SupportLadderRows.source_visible _ _) fun i => hv i,
    fun i hi => orderInterpolate_read ho hz ⟨i, by omega⟩⟩

theorem anchor_grid_one {X : Type*} [Fintype X] {a : X → ExtOrd}
    (hinv : a ∈ CanonicalPairedProfiles.inventory X 1)
    (hvis : ∀ d, SelfVis 1 (a d)) (d : X) (hd : a d ≠ ⊥) :
    ∃ B, CanonicalPairedInverse.grid 1 B = a d := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp
      (CanonicalPairedProfiles.inventory_coded X 1 hinv d) with hz | ⟨b, i, _, _, he⟩
  · exact (hd hz).elim
  have hv := hvis d
  have hs := CanonicalPairedProfiles.inventory_short X 1 hinv d
  rw [he, selfVis_ofOrd_iff] at hv; rw [he] at hs
  simp only [Short, ofOrd_ne_bot, ofOrd_ne_top, false_or, ofOrd_inj] at hs
  obtain ⟨_, rfl, hs⟩ := hs
  have hf : finitePart (Ordinal.omega0 * b + i) = i := by
    simpa only [limitPart_omega0_mul] using finitePart_limitPart_add_nat (Ordinal.omega0 * b) i
  rw [hf] at hv hs
  obtain rfl : i = 1 := le_antisymm hs hv
  exact ⟨b, he.symm⟩

theorem face_positive_lift
    {ι ιO X Q : Type*} [DecidableEq ι] [DecidableEq ιO] [Fintype X] [Fintype Q]
    {A : Finset ι} {O : Finset ιO}
    (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
    (field : Cell D → X) (fields : Q → X → ExtOrd) (hproper : ∀ d, D.scope d ≠ A)
    (hboundary : ∀ a : Q, RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1)))
    (hinv : ∀ a : Q, fields a ∈ CanonicalPairedProfiles.inventory X 1)
    (hvis : ∀ (a : Q) (x : X), SelfVis 1 (fields a x))
    (seed : Q)
    {DO : CellScheme O} {semO : Semantics DO} {JO : Finset ιO × ℕ}
    (hJO : ∀ d : DO.below JO, DO.grade d.1 ≤ 1)
    (incl : DO.below JO → D.below (A, 1))
    (pick : Cell DO → X)
    (hfield : ∀ (a : Q) (d : DO.below JO), fields a (field (incl d).1) = fields a (pick d.1))
    (hlaw : ∀ a : Q, RespectsSemanticsBelow semO JO (fun d => fields a (pick d.1)))
    (hprot : ∀ (a : Q) {p' : DO.below JO → ExtOrd} {B : ℕ},
      RespectsSemanticsBelow semO JO p' →
      (∀ d, min (p' d) (CanonicalPairedInverse.grid 1 B) =
        min (fields a (pick d.1)) (CanonicalPairedInverse.grid 1 B)) →
      ∃ (b : Q) (dec : ExtOrd → ExtOrd), Witness (gTop 1) dec ∧
        (∀ d, dec (fields b (pick d.1)) = p' d) ∧
        ∀ x, min (fields a x) (CanonicalPairedInverse.grid 1 B) =
          min (fields b x) (CanonicalPairedInverse.grid 1 B))
    {p : DO.below JO → ExtOrd}
    {q : (RelativeLadderLayer.carrier D hA (X := X) (Q := Q)).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow semO JO p)
    (hq : RespectsSemanticsBelow (RelativeLadderLayer.rows D sem hA field fields hproper) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q ⟨RelativeLadderLayer.old D hA (incl d).1,
      by rw [RelativeLadderLayer.old_index]; exact (incl d).2⟩) γ = min (p d) γ) :
    ∃ w : (RelativeLadderLayer.carrier D hA (X := X) (Q := Q)).below (A, 1) → ExtOrd,
      RespectsSemanticsBelow (RelativeLadderLayer.rows D sem hA field fields hproper) (A, 1) w ∧
      (∀ d, w ⟨RelativeLadderLayer.old D hA (incl d).1,
        by rw [RelativeLadderLayer.old_index]; exact (incl d).2⟩ = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ := by
  classical
  let _ : Fintype (DO.below JO) := Fintype.ofFinite _
  by_cases hsmall : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hsmall d)),
      fun _ => by rw [min_assoc, min_self]⟩
  obtain ⟨c, hc⟩ := not_forall.mp hsmall
  have hactive : γ < p c := not_le.mp hc
  let H := RelativeLadderLayer.rungs (X := X)
  let src (b : Q) (d : Cell (RelativeLadderLayer.carrier D hA (X := X) (Q := Q))) : ExtOrd :=
    RelativeLadderLayer.image D hA field fields b (SupportLadderRows.source H) d
  have hsrc_face (b : Q) (d : DO.below JO) :
      src b (RelativeLadderLayer.old D hA (incl d).1) =
        SupportLadderRows.source H (fieldRank (fields b) (pick d.1)) := by
    simp only [src, RelativeLadderLayer.image, RelativeLadderLayer.rankIndex_old,
      RelativeLadderLayer.ranks, fieldRank, hfield b d]
  obtain ⟨a, σ, hσ, _, hread⟩ :=
    RelativeLadderLayer.exists_leaf_chart D sem hA field fields hproper seed (hq.cap hγ)
  have hread' (d) : σ (src a d.1) = min (q d) γ := hread d
  have hpr (d : DO.below JO) :
      min (σ (SupportLadderRows.source H (fieldRank (fields a) (pick d.1)))) γ = min (p d) γ := by
    rw [← hsrc_face a d, hread' ⟨RelativeLadderLayer.old D hA (incl d).1,
        by rw [RelativeLadderLayer.old_index]; exact (incl d).2⟩, min_assoc, min_self]
    exact hag d
  let v : X → ExtOrd := fun x => σ (SupportLadderRows.source H (fieldRank (fields a) x))
  let high := Finset.univ.filter (fun x => γ ≤ v x)
  have hact : γ ≤ v (pick c.1) := min_eq_right_iff.mp ((hpr c).trans (min_eq_right hactive.le))
  obtain ⟨f0, hf0m, hmin⟩ := Finset.exists_min_image high (fields a)
    ⟨pick c.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩⟩
  have hfg : γ ≤ v f0 := (Finset.mem_filter.mp hf0m).2
  have hbot (x) (hx : fields a x = ⊥) : v x = ⊥ := by
    simp only [v, fieldRank, hx, rank_bot (bot_not_values _), SupportLadderRows.source_zero, hσ.bot]
  obtain ⟨B, hB⟩ := anchor_grid_one (hinv a) (hvis a) f0
    fun hz => hpos.not_ge (hfg.trans_eq (hbot f0 hz))
  let δ := CanonicalPairedInverse.grid 1 B
  have hcut (x : X) : fields a x < δ ↔ v x < γ := by
    change fields a x < CanonicalPairedInverse.grid 1 B ↔ v x < γ; rw [hB]
    exact ⟨fun hd => by_contra fun hn =>
        hd.not_ge (hmin x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hn⟩)),
      fun hd => by_contra fun hn => hd.not_ge (hfg.trans (hσ.mono
        (SupportLadderRows.source_mono H (rank_mono (values (fields a)) (not_lt.mp hn)))))⟩
  let s : DO.below JO → ExtOrd := fun d => fields a (pick d.1)
  have halign (d : DO.below JO) (hd : γ < p d) : δ ≤ s d := not_lt.mp fun hl => by
    have hh := (hcut (pick d.1)).mp hl
    have he := hpr d; rw [min_eq_left hh.le, min_eq_right hd.le] at he; exact hh.ne he
  have hroom : δ < ofOrd (Ordinal.omega0 * (↑(B + 1) : Ordinal)) :=
    ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self B)) 1)
  let p' := AlignedCutEncoding.encode s p 1 (B + 1) δ γ
  have hp' : RespectsSemanticsBelow semO JO p' :=
    AlignedCutEncoding.encode_respects (hlaw a) hp hJO
      (CanonicalPairedInverse.grid_visible 1 B) (ofOrd_ne_bot _) hγ hroom halign
  obtain ⟨b, dec, hdec, hdecread, hpref⟩ :=
    hprot a hp' (AlignedCutEncoding.encode_cap s p hroom halign)
  obtain ⟨τ0, hτ0, hτ0cut, hτ0read⟩ := exists_cut_chart (hvis a)
    (fun x => CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _))
    (CanonicalPairedInverse.grid_visible 1 B) (ofOrd_ne_bot _) hγ
    (fun x y h => hσ.mono (SupportLadderRows.source_mono H (rank_mono (values (fields a)) h)))
    hbot hcut
  let μ := PaddedSourceDecoder.extend (RelativePrefixEncoding.inventory p γ) 1 (B + 1) τ0 γ
  have hμ : BoundedMap 1 μ := PairedSlotIncoming.bounded_max
    ⟨by rw [hτ0.bot, min_bot_left], fun _ _ h => min_le_min_right _ (hτ0.mono h),
      fun x k i hk hi => by rw [hτ0.comm x k i hk hi, evr_min_of_selfVis hγ hk hi]⟩
    (boundedMap_of_witness (PaddedSourceDecoder.witness_release
      (isStepShifter_canonicalDecoder (S := RelativePrefixEncoding.inventory p γ)
        (K := 1)).normalizedWitness (B + 1)))
  have hνread (d : DO.below JO) : μ (dec (fields b (pick d.1))) = p d := by
    rw [hdecread]
    apply AlignedCutEncoding.decode_encode s p hτ0.mono hroom hτ0cut.ge; intro e
    have hh := hτ0read (pick e.1)
    change τ0 (s e) = min (v (pick e.1)) γ at hh
    rw [hh, min_assoc, min_self]; exact hpr e
  let k := next (values (fields a)) δ
  let f : ℕ → ExtOrd := fun i => σ (SupportLadderRows.source H i)
  have hf : Monotone f := hσ.mono.comp (SupportLadderRows.source_mono H)
  have hf0 : f 0 = ⊥ := by simp only [f, SupportLadderRows.source_zero, hσ.bot]
  have hfv (i) : SelfVis 1 (f i) :=
    CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _)
  have hfieldc : δ ≤ fields a (pick c.1) := halign c hactive
  have hcmem : fields a (pick c.1) ∈ values (fields a) :=
    mem_values.mpr ⟨ne_of_gt ((bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)).trans_le hfieldc), _, rfl⟩
  have hkc : k ≤ (values (fields a)).card :=
    (not_lt.mp fun h => ((rank_lt_next hcmem).mp h).not_ge hfieldc).trans
      (rank_le_card _ (fields a (pick c.1)))
  have hkpos : 0 < k := Nat.succ_pos _
  have hkbound : k ≤ H := hkc.trans ((values_card_le (fields a)).trans (Nat.le_succ _))
  have hab : FiniteProfileControllers.Agree (fieldRank (fields a)) (fieldRank (fields b)) k :=
    fieldRank_agreement (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)) hpref
  have hlow (i) (hi : i < k) : f i < γ := by
    by_cases hz : i = 0
    · rw [hz, hf0]; exact hpos
    obtain ⟨x, hx⟩ := exists_field_rank (fields a) (Nat.pos_of_ne_zero hz) (hi.le.trans hkc)
    have hxb : fields a x ≠ ⊥ := fun he => hz (hx.symm.trans (by
      simp only [fieldRank, he, rank_bot (bot_not_values _)]))
    have hl := (rank_lt_next (mem_values.mpr ⟨hxb, x, rfl⟩)).mp (by unfold fieldRank at hx; exact hx ▸ hi)
    simpa only [v, f, hx] using (hcut x).mp hl
  have hreach : γ ≤ f k := by
    obtain ⟨x, hx⟩ := exists_field_rank (fields a) hkpos hkc
    refine not_lt.mp fun hl => ?_
    have hlt : fields a x < δ := (hcut x).mpr (by simpa only [v, f, hx] using hl)
    have hxb : fields a x ≠ ⊥ := fun he => by
      have hr : fieldRank (fields a) x = 0 := by simp only [fieldRank, he, rank_bot (bot_not_values _)]
      have := hx.symm.trans hr; omega
    have hr := (rank_lt_next (mem_values.mpr ⟨hxb, x, rfl⟩)).mpr hlt
    change fieldRank (fields a) x < k at hr
    exact lt_irrefl k (hx ▸ hr)
  have hpvis (d : DO.below JO) : SelfVis 1 (p d) :=
    (le_antisymm (hJO d) (DO.grade_pos d.1)) ▸ (hp.orderly d).symm
  have horder (d e : DO.below JO)
      (h : fieldRank (fields b) (pick d.1) ≤ fieldRank (fields b) (pick e.1)) : p d ≤ p e := by
    rw [← hνread d, ← hνread e]
    refine (hμ.mono.comp hdec.mono) (by_contra fun hn => ?_)
    have hh := not_le.mp hn
    exact (rank_strict (mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hh), _, rfl⟩) hh).not_ge h
  obtain ⟨g, hg, hg0, hgv, hglow, hgreach, hgread⟩ := exists_table
    (fun d : DO.below JO => fieldRank (fields a) (pick d.1))
    (fun d : DO.below JO => fieldRank (fields b) (pick d.1)) p f
    hkpos hf hf0 hfv hpvis hγ hlow hreach (fun d => hab (pick d.1)) hpr horder
  obtain ⟨τ, hτ, hτread⟩ := exists_rank_decoder H g hg hg0 hgv
  have hcaps (d : (RelativeLadderLayer.carrier D hA (X := X) (Q := Q)).below (A, 1)) :
      min (τ (src b d.1)) γ = min (q d) γ := by
    change min (τ (SupportLadderRows.source H
      (RelativeLadderLayer.rankIndex D hA field fields b d.1))) γ = _
    rw [hτread _ (RelativeLadderLayer.rankIndex_bound D hA field fields b d.1), ← hread' d]
    change min (g _) γ = f _
    have hle_cut := FiniteProfileControllers.le_cut hkbound hab
    have hh := RelativeLadderLayer.rankIndex_agreement D hA field fields a b d.1
    change min (RelativeLadderLayer.rankIndex D hA field fields a d.1)
      (FiniteProfileControllers.cut H (fieldRank (fields a)) (fieldRank (fields b))) =
      min (RelativeLadderLayer.rankIndex D hA field fields b d.1)
      (FiniteProfileControllers.cut H (fieldRank (fields a)) (fieldRank (fields b))) at hh
    by_cases hia : RelativeLadderLayer.rankIndex D hA field fields a d.1 < k
    · have he : RelativeLadderLayer.rankIndex D hA field fields b d.1 =
          RelativeLadderLayer.rankIndex D hA field fields a d.1 := by omega
      rw [he, hglow _ hia, min_eq_left (hlow _ hia).le]
    · have hib : k ≤ RelativeLadderLayer.rankIndex D hA field fields b d.1 := by omega
      rw [min_eq_right (hgreach.trans (hg hib))]
      exact le_antisymm (hreach.trans (hf (not_lt.mp hia)))
        (by change σ (src a d.1) ≤ γ; rw [hread']; exact min_le_right _ _)
  refine ⟨fun d => τ (src b d.1),
    map_respects_of_positive_cap_agreement
      (RelativeLadderLayer.ladder_respects D sem hA field fields hproper hboundary
        (SupportLadderRows.leaf (Nat.succ_pos _) b))
      hq (fun d => d.2.2) hτ (ne_of_gt hpos) hcaps,
    fun d => (congrArg τ (hsrc_face b d)).trans
      ((hτread _ (Nat.le_succ_of_le (fieldRank_le _ _))).trans (hgread d)),
    hcaps⟩

end
end ReceivingRankLift
end VaughtConjecture.Knight
