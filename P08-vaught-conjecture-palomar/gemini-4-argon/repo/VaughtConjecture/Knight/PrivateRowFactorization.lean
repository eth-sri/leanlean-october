/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerLocalAlignment
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.AmbientGradeCharts

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.PrivateRowFactorization
open Transform Value ExtOrd SharpWitnessComposition OwnerLocalEndpoint

theorem coded_proper {m j : ℕ} {x : ExtOrd} (hx : x ∈ ExtOrd.codedAlphabet m j) :
    x ≠ ⊤ := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp hx with rfl | ⟨b, i, _, _, rfl⟩
  · exact bot_ne_top
  · exact ofOrd_ne_top _

theorem code_spec {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet m j) (hs : Short j x) :
    x = ⊥ ∨ ∃ b i : ℕ, b ≤ m ∧ i ≤ j ∧ x = ofOrd (Ordinal.omega0 * b + i) := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp hc with hb | ⟨b, i, hb, _, he⟩
  · exact Or.inl hb
  · refine Or.inr ⟨b, i, hb, ?_, he⟩
    rcases hs with hz | ht | ⟨u, hu, hj⟩
    · exact (ofOrd_ne_bot _ (he.symm.trans hz)).elim
    · exact (ofOrd_ne_top _ (he.symm.trans ht)).elim
    have heq := ofOrd_inj.mp (he.symm.trans hu)
    simpa only [← heq, finitePart_mul_add] using hj

theorem endpoint_grid {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet (2 * m) j) (hs : Short j x) :
    endpoint j x ∈ PairedSlotComparison.sourceGrid j m := by
  rcases code_spec hc hs with rfl | ⟨b, i, hb, hi, rfl⟩
  · exact PairedSlotComparison.sourceGrid_bot j m
  · have he : endpoint j (ofOrd (Ordinal.omega0 * b + i)) =
        ofOrd (Ordinal.omega0 * b + j) := by
      by_cases hij : i < j
      · rw [endpoint, extVisibilityReplace_of_finitePart_lt (by
          rw [finitePart_mul_add]; exact hij), limitPart_mul_add]
      · obtain rfl : i = j := by omega
        exact endpoint_of_selfVis (selfVis_ofOrd_iff.mpr (by rw [finitePart_mul_add]))
    rw [he]
    exact PairedSlotComparison.sourceGrid_endpoint (hb.trans (Nat.le_succ _))

theorem short_replace {j k i : ℕ} {x : ExtOrd} (hx : Short j x)
    (hk : k ≤ j) (hi : i ≤ k) : Short j (extVisibilityReplace x k i) := by
  rcases hx with rfl | rfl | ⟨u, rfl, hu⟩
  · exact Or.inl (extVisibilityReplace_bot _ _)
  · exact Or.inr (Or.inl (extVisibilityReplace_top _ _))
  · by_cases hut : finitePart u < k
    · rw [extVisibilityReplace_of_finitePart_lt hut]
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; exact hi.trans hk⟩)
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hut)]
      exact Or.inr (Or.inr ⟨u, rfl, hu⟩)

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D}

structure Factorization (c : Cell D) (s p : D.below (D.cell c) → ExtOrd)
    (σ : ExtOrd → ExtOrd) (γ δ : ExtOrd) where
  source : D.below (D.cell c) → ExtOrd
  outgoing : ExtOrd → ExtOrd
  lawful : RespectsSemanticsBelow sem (D.cell c) source
  proper : ∀ d, source d ≠ ⊤
  witness : Witness (gTop (D.grade c)) outgoing
  bounded : ∀ x, outgoing x ≤ p ⟨c, GradedLe.refl _⟩
  readback : ∀ d, outgoing (source d) = min (p d) (p ⟨c, GradedLe.refl _⟩)
  prefix_eq : ∀ d, min (source d) δ = min (s d) δ
  reaches : γ ≤ outgoing δ
  caps : ∀ x, Short (D.grade c) x → min (outgoing x) γ = min (σ x) γ

theorem exists_factorization (c : Cell D) {s p : D.below (D.cell c) → ExtOrd} (m : ℕ)
    (hs : RespectsSemanticsBelow sem (D.cell c) s)
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (hcoded : ∀ e, s e ∈ ExtOrd.codedAlphabet (2 * m) (D.grade c))
    (hshort : ∀ e, Short (D.grade c) (s e))
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hσ : Witness (gTop (D.grade c)) σ) (hγ : SelfVis (D.grade c) γ)
    (hpos : ⊥ < γ) (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    (hface : ∀ e, min (σ (s e)) γ = min (p e) γ) :
    ∃ δ ∈ PairedSlotComparison.sourceGrid (D.grade c) m, ⊥ < δ ∧ γ ≤ σ δ ∧
      (∀ z ∈ PairedSlotComparison.sourceGrid (D.grade c) m, z < δ → σ z < γ) ∧
      Nonempty (Factorization (sem := sem) c s p σ γ δ) := by
  classical
  let self : D.below (D.cell c) := ⟨c, GradedLe.refl _⟩
  let G := PairedSlotComparison.sourceGrid (D.grade c) m
  let R := G.filter (fun z => γ ≤ σ z)
  have howner : s self ∈ G := by
    have he := endpoint_grid (hcoded self) (hshort self)
    rwa [endpoint_of_selfVis (hs.orderly self).symm] at he
  have hownerread : γ ≤ σ (s self) := by
    have he := hface self
    rw [min_eq_right hpc.le] at he
    exact he.ge.trans (min_le_left _ _)
  have hn : R.Nonempty := ⟨s self, Finset.mem_filter.mpr ⟨howner, hownerread⟩⟩
  let δ := R.min' hn
  have hd : δ ∈ G ∧ γ ≤ σ δ := Finset.mem_filter.mp (Finset.min'_mem R hn)
  obtain ⟨hδ, hreach⟩ := hd
  have hfirst (z) (hz : z ∈ G) (hzd : z < δ) : σ z < γ := by
    by_contra hl
    exact (not_le_of_gt hzd) (Finset.min'_le R z (Finset.mem_filter.mpr ⟨hz, not_lt.mp hl⟩))
  have hδpos : ⊥ < δ := bot_lt_iff_ne_bot.mpr fun hbot => by
    have hr : γ ≤ σ δ := hreach
    rw [hbot, hσ.bot] at hr
    exact not_le_of_gt hpos hr
  refine ⟨δ, hδ, hδpos, hreach, hfirst, ?_⟩
  let := Fintype.ofFinite (D.below (D.cell c))
  let M := p self
  let τ := fun x => min (σ x) γ
  have hτ : Witness (gTop (D.grade c)) τ := FreeDiagonal.clip_witness hσ hγ
  have hτbound : ∀ x, τ x ≤ γ := fun _ => min_le_right _ _
  have hproper : ∀ e, s e ≠ ⊤ := fun e => coded_proper (hcoded e)
  have hbudget : s self ≤ ofOrd (Ordinal.omega0 * ↑(2 * m) + D.grade c) := by
    rcases code_spec (hcoded self) (hshort self) with h | ⟨b, i, hb, hi, h⟩
    · rw [h]; exact bot_le
    · rw [h]; exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) (Nat.cast_le.mpr hi))
  obtain ⟨η, ρ, β, f, H, _, _, _, hroom, hρ, hγβ, hβM, hβvis, hρη,
      hf, hfprefix, hfdef, hfread, _, hρcap⟩ :=
    OwnerLocalAlignment.exists_coded_face c hs hp hproper hshort m hbudget
      hτ hγ hpos hτbound hface hpc
  have hηreach : γ ≤ σ η :=
    (H.reach (Saturation.of_witness hτ hτbound hpos hpc hface hproper (hs.orderly self).symm)).ge.trans
      (min_le_left _ _)
  have hηgrid : η ∈ G := by
    obtain ⟨e, _, he⟩ := H.exists_witness
    rw [← he]; exact endpoint_grid (hcoded e) (hshort e)
  have hδη : δ ≤ η := by
    by_contra hn; exact (not_lt_of_ge hηreach) (hfirst η hηgrid (not_le.mp hn))
  let S := RelativePrefixEncoding.inventory (fun e => min (p e) M) β
  let ν := fun x => min (PaddedSourceDecoder.extend S (D.grade c) (2 * m + 1) ρ β x) M
  have hMvis : SelfVis (D.grade c) M := (hp.orderly self).symm
  have hν : Witness (gTop (D.grade c)) ν :=
    FreeDiagonal.clip_witness (PaddedSourceDecoder.extend_witness S hρ hβvis) hMvis
  have hcaps (x : ExtOrd) (hx : Short (D.grade c) x) : min (ν x) γ = min (σ x) γ := by
    by_cases hlow : x < ofOrd (Ordinal.omega0 * ↑(2 * m + 1))
    · dsimp only [ν]
      rw [PaddedSourceDecoder.extend_before S hlow, min_assoc, min_eq_right (hγβ.trans hβM),
        min_assoc, min_eq_right hγβ]
      simpa only [τ, min_assoc, min_self] using hρcap x hx
    · have hhx : η ≤ x := hroom.le.trans (not_lt.mp hlow)
      have hat : ν η = β := by
        dsimp only [ν]
        rw [PaddedSourceDecoder.extend_before S hroom, hρη, min_self, min_eq_left hβM]
      rw [min_eq_right (hγβ.trans (hat.ge.trans (hν.mono hhx))),
        min_eq_right (hηreach.trans (hσ.mono hhx))]
  refine ⟨{
    source := f
    outgoing := ν
    lawful := hf
    proper := fun e => by
      rw [hfdef]
      by_cases hd : min (p e) (p self) ≤ β
      · rw [AlignedCutEncoding.encode_of_le s _ (D.grade c) (2 * m + 1) η β e hd]
        exact fun ht => hproper e (top_le_iff.mp (ht ▸ min_le_left (s e) η))
      · rw [AlignedCutEncoding.encode_of_gt s _ hroom e (not_le.mp hd)]
        exact coded_proper (PaddedSourceDecoder.encode_mem _ (D.grade c) (2 * m + 1) _)
    witness := hν
    bounded := fun _ => min_le_right _ _
    readback := fun e => by
      change min (PaddedSourceDecoder.extend S (D.grade c) (2 * m + 1) ρ β (f e)) M = _
      rw [hfread e, min_assoc, min_self]
    prefix_eq := fun e => by
      simpa only [min_assoc, min_eq_right hδη] using congrArg (fun x => min x δ) (hfprefix e)
    reaches := by
      have hδshort : Short (D.grade c) δ := by
        rcases Finset.mem_insert.mp hδ with hz | he
        · rw [hz]; exact Or.inl rfl
        · obtain ⟨b, _, he'⟩ := Finset.mem_image.mp he
          rw [← he']; exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)
      have he := hcaps δ hδshort
      rw [min_eq_right hreach] at he
      exact he.ge.trans (min_le_left _ _)
    caps := hcaps }⟩

theorem owner_capped_of_chart {ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]
    {A : Finset ιA} {B : Finset ιB} {T : CellScheme A} {rows : Semantics T}
    {D : CellScheme B} {sem : Semantics D} {idx : Finset ιB × ℕ} {g : ℕ} (m : ℕ)
    {faceAt : D.below idx → T.below (A, g)} (hgrade : ∀ d, T.grade (faceAt d).1 = D.grade d.1)
    (c : D.below idx) (hc : D.cell c.1 = idx) (hg : D.grade c.1 = g)
    {p s₀ : D.below idx → ExtOrd} {q : T.below (A, g) → ExtOrd} {src : Cell T → ExtOrd}
    (hp : RespectsSemanticsBelow sem idx p) (hq : RespectsSemanticsBelow rows (A, g) q)
    {γ : ExtOrd} (hγ : SelfVis g γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (faceAt d)) γ = min (p d) γ)
    {σ : ExtOrd → ExtOrd} {H : ExtOrd} (hσ : Witness (gTop g) σ)
    (hmax : ∀ d : T.below (A, g), T.grade d.1 = g → q d ≤ H)
    (hread : ∀ d : T.below (A, g), σ (src d.1) = min (q d) H)
    (hshort : ∀ d, Short g (src d))
    (hs₀ : RespectsSemanticsBelow sem idx s₀)
    (hface₀ : ∀ d, src (faceAt d).1 = s₀ d)
    (hcoded : ∀ d, s₀ d ∈ ExtOrd.codedAlphabet (2 * m) g)
    (hs₀short : ∀ d, Short g (s₀ d))
    (hrepair : ∀ {b : ℕ} {v : D.below idx → ExtOrd}, b ≤ 2 * m + 1 →
      RespectsSemanticsBelow sem idx v →
      (∀ d, min (v d) (CanonicalPairedInverse.grid g b) =
        min (s₀ d) (CanonicalPairedInverse.grid g b)) →
      ∃ w, RespectsSemanticsBelow rows (A, g) w ∧ (∀ d, w (faceAt d) = v d) ∧
        ∀ d, min (w d) (CanonicalPairedInverse.grid g b) =
          min (src d.1) (CanonicalPairedInverse.grid g b)) :
    ∃ u, RespectsSemanticsBelow rows (A, g) u ∧
      (∀ d, u (faceAt d) = min (p d) (p c)) ∧
      (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c) := by
  classical
  have hreach : γ ≤ H := by
    have he := hag c
    rw [min_eq_right hactive.le] at he
    exact (he.ge.trans (min_le_left _ _)).trans (hmax _ ((hgrade c).trans hg))
  have hchart (d) : min (σ (src d.1)) γ = min (q d) γ := by
    rw [hread, min_assoc, min_eq_right hreach]
  let toEff := CellScheme.below.mono (D := D)
    (show GradedLe (D.cell c.1) idx from by rw [hc]; exact GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := D)
    (show GradedLe idx (D.cell c.1) from by rw [hc]; exact GradedLe.refl _)
  obtain ⟨δ, hδ, hδpos, _, _, ⟨fac⟩⟩ := exists_factorization c.1 m
    (hs₀.mono _) (hp.mono _)
    (fun d => hg ▸ hcoded (toEff d))
    (fun d => hg ▸ hs₀short (toEff d))
    (by simpa only [hg] using hσ) (by simpa only [hg] using hγ) hpos hactive fun d => by
      change min (σ (s₀ (toEff d))) γ = min (p (toEff d)) γ
      rw [← hface₀ (toEff d)]
      exact (hchart _).trans (hag _)
  rw [hg] at hδ
  rcases Finset.mem_insert.mp hδ with hz | hd
  · exact False.elim (not_lt_of_ge (le_of_eq hz) hδpos)
  obtain ⟨b, hb, hbδ⟩ := Finset.mem_image.mp hd
  change CanonicalPairedInverse.grid g b = δ at hbδ
  subst δ
  have hb' : b ≤ 2 * m + 1 := by have := Finset.mem_range.mp hb; omega
  obtain ⟨w, hw, hwread, hwcap⟩ := hrepair hb' (fac.lawful.mono _)
    (fun d => fac.prefix_eq (fromEff d))
  have hcap (d) : min (fac.outgoing (w d)) γ = min (q d) γ := by
    have hs : Short (D.grade c.1) (src d.1) := by simpa only [hg] using hshort d.1
    exact (AmbientGradeCharts.map_cap_agreement fac.witness.mono (hwcap d) fac.reaches).trans
      ((fac.caps _ hs).trans (hchart d))
  have hν : Witness (gTop g) fac.outgoing := by simpa only [hg] using fac.witness
  refine ⟨fun d => fac.outgoing (w d),
    map_respects_of_positive_cap_agreement hw hq (fun d => d.2.2)
      (boundedMap_of_witness hν) (ne_of_gt hpos) hcap,
    fun d => (congrArg fac.outgoing (hwread d)).trans (fac.readback (fromEff d)),
    hcap, fun _ => fac.bounded _⟩
