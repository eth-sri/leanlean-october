/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerLocalAlignment
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.CanonicalFieldLayer

@[expose] public section

namespace VaughtConjecture.Knight.RetunedCutDecoding

open Transform Value ExtOrd SharpWitnessComposition

/-- No lawful intermediate ambient is supplied. It is constructed as sigma(s)
using original-cap agreement, before consuming the existing aligned decoder. -/
theorem decode_lift
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {X : Type*} [Fintype X]
    (s : D.below BJ → ExtOrd) (p : X → ExtOrd) (incl : X → D.below BJ)
    {r q : D.below BJ → ExtOrd} {K b : ℕ} {a γ δ : ExtOrd} {σ : ExtOrd → ExtOrd}
    (hs : RespectsSemanticsBelow sem BJ s)
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hσ : Witness (gTop K) σ) (hδ : SelfVis K δ) (hγb : γ ≠ ⊥) (hγδ : γ ≤ δ)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : δ ≤ σ a)
    (hsource : ∀ d, min (r d) a = min (s d) a)
    (hambient : ∀ d, min (σ (s d)) γ = min (q d) γ)
    (hface : ∀ d, min (p d) δ = min (σ (s (incl d))) δ)
    (hlit : ∀ d, r (incl d) = AlignedCutEncoding.encode (s ∘ incl) p K b a δ d) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d, q' (incl d) = p d) ∧ ∀ d, min (q' d) γ = min (q d) γ := by
  have hδb : δ ≠ ⊥ := fun he => hγb (le_bot_iff.mp (he ▸ hγδ))
  have hmid : RespectsSemanticsBelow sem BJ (fun d => σ (s d)) :=
    map_respects_of_positive_cap_agreement hs hq hK (boundedMap_of_witness hσ) hγb hambient
  obtain ⟨q', hq', hread, hcap⟩ := AlignedCutEncoding.decode_lift s p incl hr hmid hK
    hσ hδ hδb hroom hactive hsource (fun _ => rfl) hface hlit
  refine ⟨q', hq', hread, ?_⟩
  intro d
  have he := congrArg (fun z => min z γ) (hcap d)
  simp only [min_assoc, min_eq_right hγδ] at he
  exact he.trans (hambient d)

end VaughtConjecture.Knight.RetunedCutDecoding

namespace VaughtConjecture.Knight.CanonicalOwnerBoundary
open Transform Value ExtOrd SharpWitnessComposition OwnerLocalEndpoint
open CanonicalPairedProfiles CoatomBoundaryExtension SourcePrefixRows
open CanonicalPairedInverse PairedSlotEncoding
noncomputable section

theorem endpoint_grid {X : Type*} [Fintype X] {j : ℕ} {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (d : X) (hd : a d ≠ ⊥) :
    ∃ b : ℕ, b ≤ 2 * Fintype.card X ∧
      endpoint j (a d) = CanonicalPairedInverse.grid j b := by
  rcases mem_codedAlphabet_iff.mp (inventory_coded X j ha d) with hb | ⟨b, n, hb, _, he⟩
  · exact (hd hb).elim
  have hn : n ≤ j := by
    rcases inventory_short X j ha d with hz | ht | ⟨v, hv, hshort⟩
    · exact (hd hz).elim
    · exact (ha.2 d ht).elim
    · have heq := ofOrd_inj.mp (he.symm.trans hv)
      simpa only [← heq, finitePart_mul_add] using hshort
  refine ⟨b, hb, ?_⟩
  rcases lt_or_eq_of_le hn with hn | hn
  · rw [endpoint, he, extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rwa [finitePart_mul_add]), ordinalReplace, limitPart_mul_add]
    rfl
  · rw [endpoint, he, hn, extVisibilityReplace_of_le_finitePart
      (by simp only [finitePart_mul_add, le_refl])]
    rfl

theorem local_endpoint_grid {X Y : Type*} [Fintype X] {j : ℕ} {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (occ : Y → X)
    {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}
    (H : IsEndpoint j (a ∘ occ) τ γ h) (hpos : ⊥ < h) :
    ∃ b : ℕ, b ≤ 2 * Fintype.card X ∧ h = CanonicalPairedInverse.grid j b := by
  obtain ⟨d, _, hd⟩ := H.exists_witness
  have hbot : a (occ d) ≠ ⊥ := by
    intro hb
    have he : h = ⊥ := hd.symm.trans (by rw [Function.comp_apply, hb]; rfl)
    exact hpos.ne he.symm
  obtain ⟨b, hb, he⟩ := endpoint_grid ha (occ d) hbot
  exact ⟨b, hb, hd.symm.trans he⟩

/-- An ordinary matching-face completion with all old coordinate caps retained.
The only lifting inputs are two actual old graded-pair clauses. They can be
obtained from the respective old faces by `lift_of_restrictFace`; no new
full-scope bountifulness is an input. -/
theorem exists_completion
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {X : Type*} [Fintype X]
    (c : Cell D) [Fintype (D.below (D.cell c))]
    {a : X → ExtOrd} (ha : a ∈ CanonicalPairedProfiles.inventory X (D.grade c))
    (occ : Cell D → X) (hs : RespectsSemantics sem (a ∘ occ))
    {p : D.below (D.cell c) → ExtOrd} (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ D.grade c) (hV : V.2 ≤ D.grade c)
    {τ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ) (hpos : ⊥ < γ) (hτbound : ∀ z, τ z ≤ γ)
    (hface : ∀ e : D.below (D.cell c), τ (a (occ e.1)) = min (p e) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩) :
    ∃ (h : ExtOrd) (ρ : ExtOrd → ExtOrd) (δ : ExtOrd) (r : Cell D → ExtOrd),
      ⊥ < h ∧ SelfVis (D.grade c) h ∧
      (∃ b : ℕ, b ≤ 2 * Fintype.card X ∧ h = CanonicalPairedInverse.grid (D.grade c) b) ∧
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ h = δ ∧ RespectsSemantics sem r ∧
      (∀ d, min (r d) h = min (a (occ d)) h) ∧
      (∀ e : D.below (D.cell c), r e.1 = AlignedCutEncoding.encode
        (fun e => a (occ e.1)) (fun e => min (p e) (p ⟨c, GradedLe.refl _⟩))
        (D.grade c) (2 * Fintype.card X + 1) h δ e) ∧
      (∀ e : D.below (D.cell c), PaddedSourceDecoder.extend
        (RelativePrefixEncoding.inventory (fun e => min (p e) (p ⟨c, GradedLe.refl _⟩)) δ)
        (D.grade c) (2 * Fintype.card X + 1) ρ δ (r e.1) =
          min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      (∀ e, min (p e) δ = min (ρ (a (occ e.1))) δ) ∧
      ∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ := by
  obtain ⟨h, ρ, δ, f, H, hhpos, hvis, _, _, hρ, hγδ, hδM, hδvis,
      hρh, hf, hfcap, hfeq, hfread, hread, hcap⟩ :=
    OwnerLocalAlignment.exists_coded_face c (hs.toBelow (D.cell c)) hp
      (fun e => ha.2 (occ e.1)) (fun e => inventory_short X (D.grade c) ha (occ e.1))
      (Fintype.card X) (inventory_bound X (D.grade c) ha (occ c))
      hτ hγ hpos hτbound hface hpc
  have hgrid := local_endpoint_grid ha (fun e : D.below (D.cell c) => occ e.1) H hhpos
  let old : Section sem U V := {
    onLeft := fun d => a (occ d.1)
    onRight := fun d => a (occ d.1)
    left_lawful := hs.toBelow U
    right_lawful := hs.toBelow V
    overlap := fun _ _ _ => rfl }
  obtain ⟨r, hr, hrcap, hrread⟩ := extend_boundary hcover hcU hOU hOV hinter hleft hright
    old f h hf (selfVis_mono hvis hU) (selfVis_mono hvis hV) (fun d => (hfcap d).symm)
  refine ⟨h, ρ, δ, r, hhpos, hvis, hgrid, hρ, hγδ, hδM, hδvis, hρh, hr,
    ?_, ?_, ?_, hread, hcap⟩
  · intro d
    have hold : old.whole hcover d = a (occ d) := by
      rcases hcover d with hu | hv
      · exact old.whole_left hcover ⟨d, hu⟩
      · exact old.whole_right hcover ⟨d, hv⟩
    exact (hrcap d).trans (congrArg (fun z => min z h) hold)
  · intro e
    rw [hrread, hfeq]
    rfl
  · intro e
    rw [hrread]
    exact hfread e

theorem supported_self {X : Type*} (K : ℕ) (grid : Set ExtOrd) (p : X → ExtOrd) (a : X) :
    OrbitPrefixSupport.Supported K grid p (p a) := by
  rcases ExtOrd.cases (p a) with hb | ht | ⟨v, hv⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inr ⟨a, K, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
  · by_cases hi : finitePart v < K
    · exact Or.inr (Or.inr ⟨a, finitePart v, hi.le, by
        rw [hv, extVisibilityReplace_of_finitePart_lt hi, limitPart_add_finitePart]⟩)
    · exact Or.inr (Or.inr ⟨a, K, le_rfl, by
        rw [hv, extVisibilityReplace_of_le_finitePart (not_lt.mp hi)]⟩)

theorem exists_prefix_section
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D E : CellScheme A}
    {sem : Semantics D} {rowsE : Semantics E}
    {k : ℕ} {X : Type*} [Fintype X] {occ : Cell D → X} (hinj : Function.Injective occ)
    (hg : ∀ d : Cell D, D.grade d ≤ k)
    (oldCell : Cell D → Cell E)
    (src : CanonicalFieldLayer.Profile sem k X occ → Cell E → ExtOrd)
    (hsrc_respects : ∀ b, RespectsSemanticsBelow rowsE (A, k) (fun d => src b d.1))
    (hsrc_old : ∀ b d, src b (oldCell d) = b.val (occ d))
    (hsrc_supp : ∀ b d, OrbitPrefixSupport.Supported k
      (PairedSlotComparison.sourceGrid k (Fintype.card X) : Set ExtOrd) b.val (src b d))
    (hsrc_agree : ∀ b a {h}, h ∈ PairedSlotComparison.sourceGrid k (Fintype.card X) →
      Agree b.val a.val h → Agree (src b) (src a) h)
    (a : CanonicalFieldLayer.Profile sem k X occ)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card X + 1)
    (hag : ∀ d, min (a.val (occ d)) (CanonicalPairedInverse.grid k B) =
      min (p d) (CanonicalPairedInverse.grid k B)) :
    ∃ r : Cell E → ExtOrd,
      RespectsSemanticsBelow rowsE (A, k) (fun d => r d.1) ∧
      (∀ d, r (oldCell d) = p d) ∧
      ∀ d, min (r d) (CanonicalPairedInverse.grid k B) =
        min (src a d) (CanonicalPairedInverse.grid k B) := by
  classical
  let v := Function.extend occ p a.val
  have hv (d : Cell D) : v (occ d) = p d := hinj.extend_apply p a.val d
  have hvp : RespectsSemantics sem (v ∘ occ) := by simpa only [Function.comp_def, hv] using hp
  have hvt (x : X) : v x ≠ ⊤ := by
    by_cases hx : ∃ d, occ d = x
    · obtain ⟨d, rfl⟩ := hx; rw [hv]; exact ht d
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]; exact a.property.2.2 x
  have hva (x : X) : min (a.val x) (CanonicalPairedInverse.grid k B) =
      min (v x) (CanonicalPairedInverse.grid k B) := by
    by_cases hx : ∃ d, occ d = x
    · obtain ⟨d, rfl⟩ := hx; rw [hv]; exact hag d
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
  let b := CanonicalFieldLayer.encode sem k X occ hg hvp hvt
  have hb : ∀ x, min (b.val x) (CanonicalPairedInverse.grid k B) =
      min (a.val x) (CanonicalPairedInverse.grid k B) :=
    CanonicalPairedProfiles.normalize_cap X k a.property.2 hva
  have hgrid : CanonicalPairedInverse.grid k B ∈
      PairedSlotComparison.sourceGrid k (Fintype.card X) :=
    PairedSlotComparison.sourceGrid_endpoint hB
  have hsource := hsrc_agree b a hgrid hb
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ :=
    CanonicalPairedInverse.exists_supported_inverse a.property.2 hvt hva
  have hfixGrid : ∀ z ∈ PairedSlotComparison.sourceGrid k (Fintype.card X),
      z < CanonicalPairedInverse.grid k B → κ z = z := by
    intro z hz hzB
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hw.bot
    · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hz
      apply hfix n
      by_contra hn
      have hBn : B ≤ n := Nat.le_of_not_gt hn
      exact (not_le_of_gt hzB) (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl))
  have hfixBoundary (x : X) (hx : a.val x < CanonicalPairedInverse.grid k B) :
      κ (a.val x) = a.val x :=
    (congrArg κ (eq_of_cap_eq_lt (hb x).symm hx)).trans
      ((hread x).trans (eq_of_cap_eq_lt (hva x) hx).symm)
  have hguard : CanonicalPairedInverse.grid k B ≤ gTop k k := by
    rw [gTop_of_le le_rfl]; exact le_top
  have hcaps := OrbitPrefixSupport.decode_agree hw (CanonicalPairedInverse.grid_visible k B)
    hguard hreach hfixGrid hfixBoundary (hsrc_supp a) hsource
  have hwhole := SharpWitnessComposition.map_respects_of_positive_cap_agreement
    (hsrc_respects b) (hsrc_respects a) (fun d => d.2.2)
    (SharpWitnessComposition.boundedMap_of_witness hw) (ofOrd_ne_bot _) (fun d => hcaps d.1)
  exact ⟨fun d => κ (src b d), hwhole,
    fun d => by dsimp only; rw [hsrc_old]; exact (hread (occ d)).trans (hv d), hcaps⟩

theorem exists_owner_capped_lift
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D E : CellScheme A}
    {sem : Semantics D} {rowsE : Semantics E}
    {k : ℕ} {X : Type*} [Fintype X] {occ : Cell D → X} (hinj : Function.Injective occ)
    (hg : ∀ d : Cell D, D.grade d ≤ k)
    (oldTarget : Cell D → E.below (A, k))
    (hold_grade : ∀ d, E.grade (oldTarget d).1 = D.grade d)
    (src : CanonicalFieldLayer.Profile sem k X occ → Cell E → ExtOrd)
    (hsrc_respects : ∀ b, RespectsSemanticsBelow rowsE (A, k) (fun d => src b d.1))
    (hsrc_old : ∀ b d, src b (oldTarget d).1 = b.val (occ d))
    (hsrc_supp : ∀ b d, OrbitPrefixSupport.Supported k
      (PairedSlotComparison.sourceGrid k (Fintype.card X) : Set ExtOrd) b.val (src b d))
    (hsrc_agree : ∀ b a {h}, h ∈ PairedSlotComparison.sourceGrid k (Fintype.card X) →
      Agree b.val a.val h → Agree (src b) (src a) h)
    (hamb : ∀ {q : E.below (A, k) → ExtOrd}, RespectsSemanticsBelow rowsE (A, k) q →
      ∀ d, E.grade d.1 = k → ∀ {γ}, SelfVis k γ → γ ≠ ⊥ → γ ≤ q d →
        ∃ (a : CanonicalFieldLayer.Profile sem k X occ) (τ : ExtOrd → ExtOrd),
          Witness (gTop k) τ ∧ (∀ z, τ z ≤ γ) ∧
          ∀ x, τ (src a x.1) = min (q x) γ)
    (c : Cell D) (hc : D.grade c = k)
    {p : D.below (D.cell c) → ExtOrd} (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {q : E.below (A, k) → ExtOrd} (hq : RespectsSemanticsBelow rowsE (A, k) q)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (D.cell c), min (p e) γ = min (q (oldTarget e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ k) (hV : V.2 ≤ k) :
    ∃ r : E.below (A, k) → ExtOrd,
      RespectsSemanticsBelow rowsE (A, k) r ∧
      (∀ e : D.below (D.cell c), r (oldTarget e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  classical
  let _ := Fintype.ofFinite (D.below (D.cell c))
  subst k
  let M := p ⟨c, GradedLe.refl _⟩
  let pp : D.below (D.cell c) → ExtOrd := fun e => min (p e) M
  have hactive : γ ≤ q (oldTarget c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, hτ, hbound, hambient⟩ := hamb hq (oldTarget c) (hold_grade c) hγ hγb hactive
  have hface (e : D.below (D.cell c)) : τ (a.val (occ e.1)) = min (p e) γ := by
    have he := hambient (oldTarget e.1)
    rw [hsrc_old] at he
    exact he.trans (hag e).symm
  obtain ⟨h, ρ, δ, u, _, _, ⟨B, hB, hBeq⟩, hρ, hγδ, hδM, hδvis,
      hρh, hu, hucap, huface, _, hread, hretune⟩ :=
    exists_completion c a.property.2 occ a.property.1 hp
      hcover hcU hOU hOV hinter hleft hright hU hV hτ hγ
      (bot_lt_iff_ne_bot.mpr hγb) hbound hface hpc
  let tail := 2 * Fintype.card X + 1
  have hroom : h < ofOrd (Ordinal.omega0 * tail) := by
    rw [hBeq]
    exact ofOrd_lt_ofOrd.mpr (code_add_lt_mul
      (Nat.cast_lt.mpr (by dsimp [tail]; omega)) _)
  let S := RelativePrefixEncoding.inventory pp δ
  let T := S.card + tail
  let C := CanonicalPairedInverse.grid (D.grade c) (T + 1)
  have hC : SelfVis (D.grade c) C := CanonicalPairedInverse.grid_visible _ _
  have hhC : h ≤ C := hroom.le.trans (ofOrd_le_ofOrd.mpr (le_trans
    (by gcongr; dsimp [T]; omega) le_self_add))
  have hfC (e : D.below (D.cell c)) : u e.1 ≤ C := by
    rw [huface]
    change AlignedCutEncoding.encode (fun e => a.val (occ e.1)) pp
      (D.grade c) tail h δ e ≤ C
    by_cases he : pp e ≤ δ
    · rw [AlignedCutEncoding.encode_of_le _ _ _ _ _ _ e he]
      exact (min_le_right _ _).trans hhC
    · rw [AlignedCutEncoding.encode_of_gt _ _ hroom e (not_le.mp he)]
      rcases mem_codedAlphabet_iff.mp (PaddedSourceDecoder.encode_mem S (D.grade c) tail
          (pp e)) with hb | ⟨b, n, hb, _, he⟩
      · rw [hb]; exact bot_le
      · rw [he]
        exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul
          (Nat.cast_lt.mpr (by dsimp [T]; omega)) n).le.trans le_self_add)
  let v : Cell D → ExtOrd := fun d => min (u d) C
  have hv : RespectsSemantics sem v :=
    ((hu.toBelow (A, D.grade c)).cap hC).toRespects
      (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hg d⟩)
  have hvt (d : Cell D) : v d ≠ ⊤ := by
    intro hd
    change min (u d) C = ⊤ at hd
    exact ofOrd_ne_top _ (top_le_iff.mp (hd ▸ min_le_right (u d) C))
  have hvcap (d : Cell D) : min (v d) h = min (a.val (occ d)) h := by
    dsimp only [v]; rw [min_assoc, min_eq_right hhC]; exact hucap d
  obtain ⟨w, hw, hwold, hwcap⟩ := exists_prefix_section hinj hg (fun d => (oldTarget d).1)
    src hsrc_respects hsrc_old hsrc_supp hsrc_agree a hv hvt (hB.trans (Nat.le_succ _))
    (fun d => by rw [← hBeq]; exact (hvcap d).symm)
  have hwcap' (d) : min (w d) h = min (src a d) h := by rw [hBeq]; exact hwcap d
  apply RetunedCutDecoding.decode_lift (fun d => src a d.1) pp (fun e => oldTarget e.1)
    (hsrc_respects a) hw hq (fun d => d.2.2) hρ hδvis hγb hγδ hroom hρh.ge
    (fun d => hwcap' d.1)
  · intro d
    have hshort := PairedCoupledSections.supported_short
      (fun _ hh => CanonicalFieldLayer.grid_short (D.grade c) X hh)
      (CanonicalFieldLayer.profile_short sem (D.grade c) X occ a) (hsrc_supp a d.1)
    exact (hretune _ hshort).trans ((min_eq_left (hbound _)).trans (hambient d))
  · intro e
    change min (pp e) δ = min (ρ (src a (oldTarget e.1).1)) δ
    rw [hsrc_old]
    dsimp only [pp]
    rw [min_assoc, min_eq_right hδM]
    exact hread e
  · intro e
    have hs : ((fun d => src a d.1) ∘ fun e : D.below (D.cell c) => oldTarget e.1) =
        fun e => a.val (occ e.1) := funext (fun e => hsrc_old a e.1)
    rw [hs]
    change w (oldTarget e.1).1 = _
    rw [hwold, show v e.1 = u e.1 from min_eq_left (hfC e), huface]

end
end VaughtConjecture.Knight.CanonicalOwnerBoundary
