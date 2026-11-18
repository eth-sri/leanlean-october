/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.HighLayerBountiful
public import VaughtConjecture.Knight.SingleFaceTailRestoration
public import VaughtConjecture.Knight.CappedDonorFields
public import VaughtConjecture.Knight.RelativeLadderRankRendering
public import VaughtConjecture.Knight.OwnerwiseDecoding

@[expose] public section

namespace VaughtConjecture.Knight.PaddedFaceLift

open Transform Value ExtOrd AmalgamationPlan SharpWitnessComposition GradeTailRestoration

noncomputable section

theorem grid_fixed_below {j b cardFld : ℕ} {δ : ExtOrd → ExtOrd}
    (hbot : δ ⊥ = ⊥) (hfix : ∀ i < b, δ (CanonicalPairedInverse.grid j i) = CanonicalPairedInverse.grid j i)
    {z : ExtOrd} (hz : z ∈ PairedSlotComparison.sourceGrid j cardFld)
    (hlt : z < CanonicalPairedInverse.grid j b) : δ z = z := by
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hbot
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    apply hfix
    by_contra hn
    exact (not_le_of_gt hlt) (ofOrd_le_ofOrd.mpr (add_le_add (by have := Nat.le_of_not_gt hn; gcongr) le_rfl))

theorem source_short_of_supported {j : ℕ} {Fld : Type*} [Fintype Fld]
    {p : Fld → ExtOrd} (hp : p ∈ CanonicalPairedProfiles.inventory Fld j) {v : ExtOrd}
    (hv : OrbitPrefixSupport.Supported j
      (PairedSlotComparison.sourceGrid j (Fintype.card Fld) : Set ExtOrd) p v) :
    Short j v := by
  rcases hv with hz | hg | ⟨f, i, hi, he⟩
  · exact Or.inl hz
  · rcases Finset.mem_insert.mp hg with hz | hg
    · exact Or.inl hz
    · obtain ⟨b, _, he⟩ := Finset.mem_image.mp hg
      exact he ▸ Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)
  · exact he ▸ PrivateRowFactorization.short_replace
      (CanonicalPairedProfiles.inventory_short _ _ hp f) le_rfl hi

theorem exists_installed_chart {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D : CellScheme A} {E : Semantics D} {U : Type*} {j : ℕ}
    (a₀ : U) (leaf : U → Cell D) (source : U → Cell D → ExtOrd)
    (hidx : ∀ a, D.cell (leaf a) = (A, j))
    (hrow : ∀ a (e : D.below (D.cell (leaf a))), E.E (leaf a) e = source a e.1)
    (hexh : ∀ c, D.cell c = (A, j) → ∃ a, c = leaf a)
    {q : D.below (A, j) → ExtOrd} (hq : RespectsSemanticsBelow E (A, j) q) :
    ∃ a : U, ∃ σ : ExtOrd → ExtOrd, ∃ M : ExtOrd,
      Witness (gTop j) σ ∧
      (∀ d, D.grade d.1 = j → q d ≤ M) ∧
      ∀ d, σ (source a d.1) = min (q d) M := by
  obtain ⟨H⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨leaf a₀, (hidx a₀).symm ▸ GradedLe.refl _⟩, hidx a₀⟩
  obtain ⟨a, ha⟩ := hexh H.owner.1 H.index
  refine ⟨a, H.shift, q H.owner, H.witness, H.dominates, fun d => ?_⟩
  have hr := H.read_capped d d.2.2
  have hr' : ∀ e : D.below (D.cell H.owner.1), E.E H.owner.1 e = source a e.1 := by
    rw [ha]; exact hrow a
  rwa [hr'] at hr

theorem owner_capped_face {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {m j : ℕ} {O : SemScheme m} {eff : Finset (Fin m) × ℕ}
    {D : CellScheme A} {E : Semantics D}
    (faceAt : O.scheme.below eff → D.below (A, j))
    (hgrade : ∀ d, D.grade (faceAt d).1 = O.scheme.grade d.1)
    {U : Type*} (cardFld : ℕ) (source : U → Cell D → ExtOrd)
    (hshort : ∀ a d, Short j (source a d))
    {q : D.below (A, j) → ExtOrd}
    (hq : RespectsSemanticsBelow E (A, j) q)
    (hchart_ex : ∃ a : U, ∃ σ M, Witness (gTop j) σ ∧
      (∀ d, D.grade d.1 = j → q d ≤ M) ∧ ∀ d, σ (source a d.1) = min (q d) M)
    (hsrc : ∀ a : U, ∃ s : O.scheme.below eff → ExtOrd,
      RespectsSemanticsBelow O.rows eff s ∧
      (∀ d, source a (faceAt d).1 = s d) ∧
      (∀ d, s d ∈ ExtOrd.codedAlphabet (2 * cardFld) j) ∧
      (∀ d, Short j (s d)) ∧
      ∀ {b : ℕ}, b ≤ 2 * cardFld + 1 → ∀ {v : O.scheme.below eff → ExtOrd},
        RespectsSemanticsBelow O.rows eff v →
        (∀ d, min (v d) (CanonicalPairedInverse.grid j b) =
          min (s d) (CanonicalPairedInverse.grid j b)) →
        ∃ w, RespectsSemanticsBelow E (A, j) w ∧
          (∀ d, w (faceAt d) = v d) ∧
          ∀ d, min (w d) (CanonicalPairedInverse.grid j b) =
            min (source a d.1) (CanonicalPairedInverse.grid j b))
    (c : O.scheme.below eff) (hc : O.scheme.cell c.1 = eff) (hg : O.scheme.grade c.1 = j)
    {p : O.scheme.below eff → ExtOrd} (hp : RespectsSemanticsBelow O.rows eff p)
    {γ : ExtOrd} (hγ : SelfVis j γ) (hpos : ⊥ < γ) (hactive : γ < p c)
    (hag : ∀ d, min (q (faceAt d)) γ = min (p d) γ) :
    ∃ u, RespectsSemanticsBelow E (A, j) u ∧
      (∀ d, u (faceAt d) = min (p d) (p c)) ∧
      (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c) := by
  classical
  obtain ⟨a, σ, H, hσ, hmax, hread⟩ := hchart_ex
  have hreach : γ ≤ H := by
    have he := hag c
    rw [min_eq_right hactive.le] at he
    exact (he.ge.trans (min_le_left _ _)).trans (hmax _ ((hgrade c).trans hg))
  have hchart (d) : min (σ (source a d.1)) γ = min (q d) γ := by
    rw [hread, min_assoc, min_eq_right hreach]
  obtain ⟨s₀, hs₀, hface_read, hscoded, hsshort, hrepair⟩ := hsrc a
  let toEff := CellScheme.below.mono (D := O.scheme)
    (show GradedLe (O.scheme.cell c.1) eff by rw [hc]; exact GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := O.scheme)
    (show GradedLe eff (O.scheme.cell c.1) by rw [hc]; exact GradedLe.refl _)
  obtain ⟨δ, hδ, hδpos, _, _, ⟨fac⟩⟩ := PrivateRowFactorization.exists_factorization c.1
    cardFld (hs₀.mono _) (hp.mono _)
    (fun d => by rw [hg]; exact hscoded (toEff d))
    (fun d => by rw [hg]; exact hsshort (toEff d))
    (by simpa only [hg] using hσ) (by simpa only [hg] using hγ) hpos hactive
    (fun d => by
      change min (σ (s₀ (toEff d))) γ = min (p (toEff d)) γ
      rw [← hface_read (toEff d)]
      exact (hchart _).trans (hag _))
  rw [hg] at hδ
  rcases Finset.mem_insert.mp hδ with hz | hd
  · exact (not_lt_of_ge (le_of_eq hz) hδpos).elim
  obtain ⟨b, hb, hbδ⟩ := Finset.mem_image.mp hd
  change CanonicalPairedInverse.grid j b = δ at hbδ
  subst δ
  have hb' : b ≤ 2 * cardFld + 1 := by have := Finset.mem_range.mp hb; omega
  obtain ⟨w, hw, hwread, hwcap⟩ := hrepair hb' (fac.lawful.mono _) (fun d => fac.prefix_eq (fromEff d))
  have hcap (d) : min (fac.outgoing (w d)) γ = min (q d) γ :=
    (AmbientGradeCharts.map_cap_agreement fac.witness.mono (hwcap d) fac.reaches).trans
      ((fac.caps _ (by simpa only [hg] using hshort a d.1)).trans (hchart d))
  have hν : Witness (gTop j) fac.outgoing := by simpa only [hg] using fac.witness
  exact ⟨fun d => fac.outgoing (w d),
    map_respects_of_positive_cap_agreement hw hq (fun d => d.2.2)
      (boundedMap_of_witness hν) (ne_of_gt hpos) hcap,
    fun d => (congrArg fac.outgoing (hwread d)).trans (fac.readback (fromEff d)),
    hcap, fun _ => fac.bounded _⟩

theorem restore_face {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {m k : ℕ} {O : SemScheme m} {effLow eff : Finset (Fin m) × ℕ}
    {DLow D : CellScheme A} {ELow : Semantics DLow} {E : Semantics D}
    (heff : GradedLe effLow eff) (heff_top : ∀ d : O.scheme.below eff, O.scheme.grade d.1 ≤ k + 1)
    (heff_low : ∀ c : Cell O.scheme, O.scheme.grade c ≤ k → GradedLe (O.scheme.cell c) effLow)
    (faceLow : O.scheme.below effLow → DLow.below (A, k))
    (faceAt : O.scheme.below eff → D.below (A, k + 1))
    (hgrade : ∀ d, D.grade (faceAt d).1 = O.scheme.grade d.1)
    (e : DLow.below (A, k) ≃ D.below (A, k))
    (hlow_iff : ∀ r : DLow.below (A, k) → ExtOrd,
      RespectsSemanticsBelow ELow (A, k) r ↔ RespectsSemanticsBelow E (A, k) (r ∘ e.symm))
    (hid : ∀ d : O.scheme.below effLow,
      lowerIncl (Nat.le_succ k) (e (faceLow d)) = faceAt (CellScheme.below.mono heff d))
    (hprev : ∀ (p₀ : O.scheme.below effLow → ExtOrd) (q₀ : DLow.below (A, k) → ExtOrd) (M : ExtOrd),
      RespectsSemanticsBelow O.rows effLow p₀ →
      RespectsSemanticsBelow ELow (A, k) q₀ → SelfVis k M →
      (∀ d, min (q₀ (faceLow d)) M = min (p₀ d) M) →
      ∃ r₀, RespectsSemanticsBelow ELow (A, k) r₀ ∧
        (∀ d, r₀ (faceLow d) = p₀ d) ∧ ∀ d, min (r₀ d) M = min (q₀ d) M)
    {p : O.scheme.below eff → ExtOrd} {u : D.below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow O.rows eff p)
    (hu : RespectsSemanticsBelow E (A, k + 1) u)
    {M : ExtOrd} (hM : SelfVis (k + 1) M)
    (hread : ∀ d, u (faceAt d) = min (p d) M)
    (hbound : ∀ d, u d ≤ M)
    (hmax : ∀ d, O.scheme.grade d.1 = k + 1 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow E (A, k + 1) r ∧
      (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) M = min (u d) M := by
  let inc := CellScheme.below.mono (D := O.scheme) heff
  let u₁ := fun d => u (lowerIncl (Nat.le_succ k) (e d))
  have hu₁ : RespectsSemanticsBelow ELow (A, k) u₁ := by
    apply (hlow_iff u₁).mpr
    have h := hu.mono (show GradedLe (A, k) (A, k + 1) from ⟨Finset.Subset.refl _, Nat.le_succ k⟩)
    simpa only [u₁, Function.comp_def, Equiv.apply_symm_apply, lowerIncl, CellScheme.below.mono] using h
  obtain ⟨v, hv, hvread, hvcap⟩ := hprev (p ∘ inc) u₁ M (hp.mono heff) hu₁ (hM.mono (Nat.le_succ k))
    (fun d => by
      change min (u (lowerIncl _ (e _))) M = min (p (inc d)) M
      rw [hid, hread, min_assoc, min_self])
  let v₁ := v ∘ e.symm
  have hag (d) : min (v₁ d) M = min (u (lowerIncl (Nat.le_succ k) d)) M := by
    simpa only [u₁, v₁, Function.comp_apply, Equiv.apply_symm_apply] using hvcap (e.symm d)
  refine ⟨splice u v₁, splice_respects (Nat.le_succ k) hu ((hlow_iff v).mp hv)
    (fun d _ => hbound d) hag, ?_, splice_cap (Nat.le_succ k) hag⟩
  intro d
  by_cases hd : O.scheme.grade d.1 ≤ k
  · have hd' : D.grade (faceAt d).1 ≤ k := (hgrade d).le.trans hd
    rw [splice_low u v₁ _ hd']
    let d₁ : O.scheme.below effLow := ⟨d.1, heff_low d.1 hd⟩
    have he : (⟨(faceAt d).1, (faceAt d).2.1, hd'⟩ : D.below (A, k)) = e (faceLow d₁) :=
      Subtype.ext (congrArg Subtype.val (hid d₁)).symm
    change v (e.symm _) = p d
    rw [he, Equiv.symm_apply_apply]
    exact hvread d₁
  · rw [splice_high u v₁ _ (by simpa only [hgrade] using hd), hread]
    exact min_eq_left (hmax d (by have := heff_top d; omega))

theorem active_face_lift {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {m j : ℕ} (hj : 0 < j) {O : SemScheme m} {eff : Finset (Fin m) × ℕ}
    (heff_eq : j ≤ m → eff = (Finset.univ, j))
    {D : CellScheme A} {E : Semantics D}
    (faceAt : O.scheme.below eff → D.below (A, j))
    (howner : ∀ c : O.scheme.below eff, O.scheme.cell c.1 = eff → O.scheme.grade c.1 = j →
      ∀ {p : O.scheme.below eff → ExtOrd} {q : D.below (A, j) → ExtOrd} {γ : ExtOrd},
        RespectsSemanticsBelow O.rows eff p → RespectsSemanticsBelow E (A, j) q →
        SelfVis j γ → ⊥ < γ → γ < p c →
        (∀ d, min (q (faceAt d)) γ = min (p d) γ) →
        ∃ u, RespectsSemanticsBelow E (A, j) u ∧
          (∀ d, u (faceAt d) = min (p d) (p c)) ∧
          (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c))
    (hrestore : ∀ {p : O.scheme.below eff → ExtOrd} {u : D.below (A, j) → ExtOrd} {M : ExtOrd},
      RespectsSemanticsBelow O.rows eff p → RespectsSemanticsBelow E (A, j) u →
      SelfVis j M → (∀ d, u (faceAt d) = min (p d) M) →
      (∀ d, u d ≤ M) → (∀ d, O.scheme.grade d.1 = j → p d ≤ M) →
      ∃ r, RespectsSemanticsBelow E (A, j) r ∧
        (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) M = min (u d) M)
    {p : O.scheme.below eff → ExtOrd} {q : D.below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow O.rows eff p) (hq : RespectsSemanticsBelow E (A, j) q)
    {γ : ExtOrd} (hγ : SelfVis j γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, O.scheme.grade d.1 = j ∧ γ < p d)
    (hag : ∀ d, min (q (faceAt d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow E (A, j) r ∧
      (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hm : j ≤ m := hd ▸ CappedDonor.gradeC_le d.1
  have heff := heff_eq hm
  subst heff
  obtain ⟨c₀, hc₀⟩ := O.complete (Finset.univ, j) (Plan.mem_gradedPlan.mpr
    ⟨O.scheme.isPlan.domain_mem, hj, by simpa only [Finset.card_univ, Fintype.card_fin] using hm⟩)
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩, hc₀⟩
  have hci : O.scheme.cell c.1 = (Finset.univ, j) := hc
  have hg : O.scheme.grade c.1 = j := congrArg Prod.snd hc
  have hpc : γ < p c := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, hbound⟩ := howner c hci hg hp hq hγ hpos hpc hag
  have hM : SelfVis j (p c) := by simpa only [hg] using (hp.orderly c).symm
  obtain ⟨r, hr, hrr, hrc⟩ := hrestore hp hu hM hread hbound hmax
  exact ⟨r, hr, hrr, fun e => (cap_below (hrc e) hpc.le).trans (hcap e)⟩

theorem all_cap_face_lift {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {m j : ℕ} {O : SemScheme m} {eff : Finset (Fin m) × ℕ}
    {D : CellScheme A} {E : Semantics D}
    (faceAt : O.scheme.below eff → D.below (A, j))
    (hrestore : ∀ {p : O.scheme.below eff → ExtOrd} {u : D.below (A, j) → ExtOrd} {M : ExtOrd},
      RespectsSemanticsBelow O.rows eff p → RespectsSemanticsBelow E (A, j) u →
      SelfVis j M → (∀ d, u (faceAt d) = min (p d) M) →
      (∀ d, u d ≤ M) → (∀ d, O.scheme.grade d.1 = j → p d ≤ M) →
      ∃ r, RespectsSemanticsBelow E (A, j) r ∧
        (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) M = min (u d) M)
    (hbottom : (∃ d : O.scheme.below eff, O.scheme.grade d.1 = j) →
      ∀ {p : O.scheme.below eff → ExtOrd}, RespectsSemanticsBelow O.rows eff p →
        ∃ r, RespectsSemanticsBelow E (A, j) r ∧ ∀ d, r (faceAt d) = p d)
    (hactive_lift : (∃ d : O.scheme.below eff, O.scheme.grade d.1 = j) →
      ∀ {p : O.scheme.below eff → ExtOrd} {q : D.below (A, j) → ExtOrd} {γ : ExtOrd},
        RespectsSemanticsBelow O.rows eff p → RespectsSemanticsBelow E (A, j) q →
        SelfVis j γ → ⊥ < γ → (∃ d, O.scheme.grade d.1 = j ∧ γ < p d) →
        (∀ d, min (q (faceAt d)) γ = min (p d) γ) →
        ∃ r, RespectsSemanticsBelow E (A, j) r ∧
          (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) γ = min (q d) γ)
    {p : O.scheme.below eff → ExtOrd} {q : D.below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow O.rows eff p) (hq : RespectsSemanticsBelow E (A, j) q)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (q (faceAt d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow E (A, j) r ∧
      (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hi : ∀ d, O.scheme.grade d.1 = j → p d ≤ γ
  · obtain ⟨r, hr, hread, hcap⟩ := hrestore hp (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hi
    exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩
  obtain ⟨d, hd⟩ := not_forall.mp hi
  obtain ⟨hg, hv⟩ := not_imp.mp hd
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := hbottom ⟨d, hg⟩ hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  · exact hactive_lift ⟨d, hg⟩ hp hq hγ (bot_lt_iff_ne_bot.mpr hz) ⟨d, hg, not_le.mp hv⟩ hag

theorem decoded_renderWith_respects {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {B : CellScheme A} {semB : Semantics B} (hpos : 0 < A.card)
    {Fld Q₁ : Type*} [Fintype Fld] [Fintype Q₁]
    (field : Cell B → Fld) (fields₁ : Q₁ → Fld → ExtOrd)
    (hproper : ∀ c : Cell B, B.scope c ≠ A)
    (b₀ : Q₁) (val : Fld → ExtOrd) (C : ExtOrd)
    (hval_bound : ∀ f, val f ≤ C) (hval_vis : ∀ f, SelfVis 1 (val f)) (hC_vis : SelfVis 1 C)
    (hranks : ∀ f, RelativeLadderLayer.ranks fields₁ b₀ f = LadderScalarRendering.fieldRank val f)
    {j : ℕ} (hj : 1 ≤ j) {δ : ExtOrd → ExtOrd} (hδ : Witness (gTop j) δ)
    (hreflect : ∀ f, δ (val f) = ⊥ → val f = ⊥)
    (horiginal : RespectsSemanticsBelow semB (A, j) (fun d => δ (val (field d.1)))) :
    RespectsSemanticsBelow (RelativeLadderLayer.rows B semB hpos field fields₁ hproper) (A, j)
      (fun d => δ (RelativeLadderLayer.renderWith B hpos field fields₁ b₀ val C d.1)) := by
  by_cases hz : δ C = ⊥
  · have he (d : Cell (RelativeLadderLayer.carrier B hpos (X := Fld) (Q := Q₁))) :
        δ (RelativeLadderLayer.renderWith B hpos field fields₁ b₀ val C d) = ⊥ :=
      le_bot_iff.mp ((hδ.mono (RelativeLadderLayer.renderWith_bound B hpos field fields₁ b₀ val hval_bound d)).trans_eq hz)
    simp only [he]
    exact ⟨fun _ => (selfVis_bot _).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot (_), fun _ c _ _ => ⟨c, rfl, le_rfl⟩⟩
  · let f := fun i => δ (LadderScalarRendering.level (LadderScalarRendering.values val) C i)
    apply RelativeLadderLayer.image_respects B semB hpos field fields₁ hproper b₀ f
      (hδ.mono.comp (LadderScalarRendering.level_mono (LadderScalarRendering.values_bound hval_bound)))
      (by simp only [f, LadderScalarRendering.level_zero, hδ.bot])
    · intro i
      have hv := LadderScalarRendering.level_visible hval_vis hC_vis i
      have he := hδ.clause5 (LadderScalarRendering.level (LadderScalarRendering.values val) C i)
        1 (by rw [gTop_of_le hj]; exact le_top) 1 le_rfl
      change SelfVis 1 (δ _)
      rw [hv] at he
      exact he.symm
    · intro i hi _
      have hp := LadderScalarRendering.level_pos (LadderScalarRendering.bot_not_values val)
        (LadderScalarRendering.values_bound hval_bound) (fun h => hz (h ▸ hδ.bot)) hi
      rcases LadderScalarRendering.level_supported (LadderScalarRendering.values val) C i with he | he | he
      · exact (hp he).elim
      · obtain ⟨_, x, hx⟩ := LadderScalarRendering.mem_values.mp he
        exact fun h => hp (hx.symm.trans (hreflect x ((congrArg δ hx).trans h)))
      · exact fun h => hz (he ▸ h)
    · simpa only [f, hranks, LadderScalarRendering.field_readback] using horiginal

theorem decoded_layer_lawful {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {DBase D : CellScheme A} {EBase : Semantics DBase} {E : Semantics D}
    {j : ℕ} {src : Cell D → ExtOrd} {δ : ExtOrd → ExtOrd}
    (hs : RespectsSemanticsBelow E (A, j) (fun d => src d.1))
    (hδ : Witness (gTop j) δ)
    (baseMap : Cell DBase → Cell D)
    (hbase_idx : ∀ b, D.cell (baseMap b) = DBase.cell b)
    (hbase_resp : ∀ b (p : Cell D → ExtOrd),
      RespectsSemanticsBelow E (D.cell (baseMap b)) (fun d => p d.1) ↔
        RespectsSemanticsBelow EBase (DBase.cell b) (fun d => p (baseMap d.1)))
    (hl : RespectsSemanticsBelow EBase (A, j) (fun d => δ (src (baseMap d.1))))
    (hcases : ∀ c : Cell D, GradedLe (D.cell c) (A, j) →
      (∃ b, c = baseMap b) ∨ ∀ d : D.below (D.cell c), Short (D.grade c) (E.E c d)) :
    RespectsSemanticsBelow E (A, j) (fun d => δ (src d.1)) := by
  apply map_respects_of_short_or_local hs (fun d => d.2.2) hδ
  intro ⟨c, hc⟩
  rcases hcases c hc with ⟨b, rfl⟩ | hsh
  · right
    have hb : GradedLe (DBase.cell b) (A, j) := by simpa only [hbase_idx] using hc
    exact ((hbase_resp b (fun d => δ (src d))).mpr (hl.mono hb)).locality ⟨_, GradedLe.refl _⟩
  · exact Or.inl hsh

theorem full_face_lift {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {m j : ℕ} (hj : 0 < j) {O : SemScheme m} {eff : Finset (Fin m) × ℕ}
    (heff_eq : j ≤ m → eff = (Finset.univ, j))
    {D : CellScheme A} {E : Semantics D}
    (faceAt : O.scheme.below eff → D.below (A, j))
    (hgrade : ∀ d, D.grade (faceAt d).1 = O.scheme.grade d.1)
    (hrestore : ∀ {p : O.scheme.below eff → ExtOrd} {u : D.below (A, j) → ExtOrd} {M : ExtOrd},
      RespectsSemanticsBelow O.rows eff p → RespectsSemanticsBelow E (A, j) u →
      SelfVis j M → (∀ d, u (faceAt d) = min (p d) M) →
      (∀ d, u d ≤ M) → (∀ d, O.scheme.grade d.1 = j → p d ≤ M) →
      ∃ r, RespectsSemanticsBelow E (A, j) r ∧
        (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) M = min (u d) M)
    {Fld St U : Type*} [Fintype Fld]
    (prof : St → Fld → ExtOrd) (Adm : St → Prop)
    (uVal : U → Fld → ExtOrd)
    (hU : ∀ a : U, uVal a ∈ CanonicalPairedProfiles.inventory Fld j ∧
      ∃ S : St, Adm S ∧ prof S = uVal a)
    (mkU : ∀ S : St, Adm S → prof S ∈ CanonicalPairedProfiles.inventory Fld j → U)
    (hmkU : ∀ S hS hc, uVal (mkU S hS hc) = prof S)
    (source : U → Cell D → ExtOrd)
    (hsrc_law : ∀ a, RespectsSemanticsBelow E (A, j) (fun d => source a d.1))
    (hsrc_supp : ∀ a d, OrbitPrefixSupport.Supported j
      (PairedSlotComparison.sourceGrid j (Fintype.card Fld) : Set ExtOrd) (uVal a) (source a d))
    (hsrc_pref : ∀ b a {h}, h ∈ PairedSlotComparison.sourceGrid j (Fintype.card Fld) →
      SourcePrefixRows.Agree (uVal b) (uVal a) h → SourcePrefixRows.Agree (source b) (source a) h)
    {p : O.scheme.below eff → ExtOrd} {q : D.below (A, j) → ExtOrd}
    (hp : RespectsSemanticsBelow O.rows eff p) (hq : RespectsSemanticsBelow E (A, j) q)
    (hchart_ex : ∀ {q : D.below (A, j) → ExtOrd}, RespectsSemanticsBelow E (A, j) q →
      ∃ a : U, ∃ σ M, Witness (gTop j) σ ∧
        (∀ d, D.grade d.1 = j → q d ≤ M) ∧ ∀ d, σ (source a d.1) = min (q d) M)
    (pick : Cell O.scheme → Fld)
    (sVal : St → O.scheme.below eff → ExtOrd)
    (hs_law : ∀ S, Adm S → RespectsSemanticsBelow O.rows eff (sVal S))
    (hs_eq : ∀ S, Adm S → ∀ d, prof S (pick d.1) = sVal S d)
    (hsrc_face : ∀ a d, source a (faceAt d).1 = uVal a (pick d.1))
    (hbottom : (∃ d : O.scheme.below eff, O.scheme.grade d.1 = j) →
      ∀ {p : O.scheme.below eff → ExtOrd}, RespectsSemanticsBelow O.rows eff p →
        ∃ r, RespectsSemanticsBelow E (A, j) r ∧ ∀ d, r (faceAt d) = p d)
    (hprot : (∃ d : O.scheme.below eff, O.scheme.grade d.1 = j) →
      ∀ {S : St}, Adm S → prof S ∈ CanonicalPairedProfiles.inventory Fld j →
      ∀ {b : ℕ} {v : O.scheme.below eff → ExtOrd}, RespectsSemanticsBelow O.rows eff v →
      (∀ d, min (v d) (CanonicalPairedInverse.grid j b) =
        min (sVal S d) (CanonicalPairedInverse.grid j b)) →
      ∃ (Q : St) (dec : ExtOrd → ExtOrd), Adm Q ∧
        prof Q ∈ CanonicalPairedProfiles.inventory Fld j ∧
        (∀ x, min (prof Q x) (CanonicalPairedInverse.grid j b) =
          min (prof S x) (CanonicalPairedInverse.grid j b)) ∧
        Witness (gTop j) dec ∧
        (∀ d, dec (prof Q (pick d.1)) = v d) ∧
        (∀ i < b, dec (CanonicalPairedInverse.grid j i) = CanonicalPairedInverse.grid j i) ∧
        CanonicalPairedInverse.grid j b ≤ dec (CanonicalPairedInverse.grid j b) ∧
        ∀ x, prof S x < CanonicalPairedInverse.grid j b → dec (prof S x) = prof S x)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (q (faceAt d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow E (A, j) r ∧
      (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) γ = min (q d) γ := by
  refine all_cap_face_lift faceAt hrestore hbottom
    (fun hex {p q γ} hp hq hγ hpos hact hag =>
      active_face_lift hj heff_eq faceAt
        (fun c hci hg {p q γ} hp hq hγ hpos hpc hag =>
          owner_capped_face faceAt hgrade (Fintype.card Fld) source
            (fun a d => source_short_of_supported (hU a).1 (hsrc_supp a d)) hq (hchart_ex hq)
            (fun a => by
              obtain ⟨hinv, S, hS, he⟩ := hU a
              have hcanon : prof S ∈ CanonicalPairedProfiles.inventory Fld j := he.symm ▸ hinv
              refine ⟨sVal S, hs_law S hS,
                fun d => (hsrc_face a d).trans (he ▸ hs_eq S hS d),
                fun d => hs_eq S hS d ▸ CanonicalPairedProfiles.inventory_coded _ _ hcanon (pick d.1),
                fun d => hs_eq S hS d ▸ CanonicalPairedProfiles.inventory_short _ _ hcanon (pick d.1),
                fun {b} hb {v} hv hagv => ?_⟩
              obtain ⟨Q, dec, hQ, hcQ, hpre, hw, hrd, hgf, hreach, hbf⟩ :=
                hprot hex hS hcanon hv hagv
              let aQ := mkU Q hQ hcQ
              have hfix (z : ExtOrd)
                  (hz : z ∈ PairedSlotComparison.sourceGrid j (Fintype.card Fld))
                  (hlt : z < CanonicalPairedInverse.grid j b) : dec z = z :=
                grid_fixed_below hw.bot hgf hz hlt
              have hbf' (x : Fld) (hx : uVal a x < CanonicalPairedInverse.grid j b) :
                  dec (uVal a x) = uVal a x := he ▸ hbf x (he.symm ▸ hx)
              have hpre' : SourcePrefixRows.Agree (uVal aQ) (uVal a)
                  (CanonicalPairedInverse.grid j b) := by
                intro x
                rw [hmkU, ← he]
                exact hpre x
              have hlw := (OrbitPrefixSupport.decode_respects_of_positive_cut hw
                (hsrc_law a) (hsrc_law aQ) (fun d => d.2.2)
                (CanonicalPairedInverse.grid_visible j b) (ofOrd_ne_bot _) hreach hfix hbf'
                (fun d => hsrc_supp a d.1)
                (fun d => hsrc_pref aQ a (PairedSlotComparison.sourceGrid_endpoint hb) hpre' d.1)).1
              have hcp := OrbitPrefixSupport.decode_agree hw
                (CanonicalPairedInverse.grid_visible j b) (by rw [gTop_of_le le_rfl]; exact le_top)
                hreach hfix hbf' (hsrc_supp a)
                (hsrc_pref aQ a (PairedSlotComparison.sourceGrid_endpoint hb) hpre')
              refine ⟨fun d => dec (source aQ d.1), hlw, fun d => ?_, fun d => hcp d.1⟩
              dsimp only
              rw [hsrc_face aQ d, hmkU]
              exact hrd d)
            c hci hg hp hγ hpos hpc hag)
        hrestore hp hq hγ hpos hact hag)
    hp hq hγ hag

end
end VaughtConjecture.Knight.PaddedFaceLift
