/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AlignedCutEncoding
public import VaughtConjecture.Knight.CanonicalOwnerBoundary

/-! # Separate the retuned readback level from the original agreement cap

Plan 29 may retune the first saturated strip to a level delta above gamma.
`decode_lift` then applies at delta, NOT at gamma. Its intermediate ambient
is constructed from the lawful source and the retuned witness. Positive-cap
transport against the original ambient proves its lawfulness, even on long
rows. The final output still agrees at the original gamma on every coordinate.

This discharges the two-cap transport step. Producing the retuned witness
and the lawful prefix-preserving coded completion remains separate.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.RetunedCutDecoding

open Transform Value ExtOrd SharpWitnessComposition CoatomBoundaryExtension CanonicalPairedProfiles

theorem owner_capped_lift
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D K : CellScheme A}
    {sem : Semantics D} {Rws : Semantics K} {X : Type*} [Fintype X]
    (occ : Cell D → X) (c : Cell D) {k : ℕ} (hc : D.grade c = k)
    (hg : ∀ d : Cell D, D.grade d ≤ k)
    {p : D.below (D.cell c) → ExtOrd} (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {q : K.below (A, k) → ExtOrd} (hq : RespectsSemanticsBelow Rws (A, k) q)
    (hK : ∀ d : K.below (A, k), K.grade d.1 ≤ k)
    (oldT : Cell D → K.below (A, k))
    {γ : ExtOrd} (hγ : SelfVis k γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (D.cell c), min (p e) γ = min (q (oldT e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell D, GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell D, GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ k) (hV : V.2 ≤ k)
    {a : X → ExtOrd} (ha : a ∈ CanonicalPairedProfiles.inventory X k)
    (hs : RespectsSemantics sem (a ∘ occ))
    {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop k) τ) (hbound : ∀ z, τ z ≤ γ)
    {src : Cell K → ExtOrd} (hsrc : RespectsSemanticsBelow Rws (A, k) (fun d => src d.1))
    (hshort : ∀ d : Cell K, Short k (src d))
    (hbdry : ∀ d : Cell D, src (oldT d).1 = a (occ d))
    (hambient : ∀ d : K.below (A, k), τ (src d.1) = min (q d) γ)
    (hpref : ∀ {v : Cell D → ExtOrd}, RespectsSemantics sem v → (∀ d, v d ≠ ⊤) →
      ∀ {B : ℕ}, B ≤ 2 * Fintype.card X + 1 →
      (∀ d, min (a (occ d)) (CanonicalPairedInverse.grid k B) =
        min (v d) (CanonicalPairedInverse.grid k B)) →
      ∃ w : Cell K → ExtOrd,
        RespectsSemanticsBelow Rws (A, k) (fun d => w d.1) ∧
        (∀ d : Cell D, w (oldT d).1 = v d) ∧
        ∀ d : Cell K, min (w d) (CanonicalPairedInverse.grid k B) =
          min (src d) (CanonicalPairedInverse.grid k B)) :
    ∃ r : K.below (A, k) → ExtOrd,
      RespectsSemanticsBelow Rws (A, k) r ∧
      (∀ e : D.below (D.cell c), r (oldT e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  classical
  let _ := Fintype.ofFinite (D.below (D.cell c))
  subst hc
  let M := p ⟨c, GradedLe.refl _⟩
  let pp : D.below (D.cell c) → ExtOrd := fun e => min (p e) M
  have hface (e : D.below (D.cell c)) : τ (a (occ e.1)) = min (p e) γ := by
    rw [← hbdry e.1, hambient (oldT e.1), hag e]
  obtain ⟨h, ρ, δ, f, H, hhpos, hvis, _, hroom, hρ, hγδ, hδM, hδvis,
      hρh, hf, hfcap, hfeq, _, hread, hretune⟩ :=
    OwnerLocalAlignment.exists_coded_face c (hs.toBelow (D.cell c)) hp
      (fun e => ha.2 (occ e.1)) (fun e => inventory_short X (D.grade c) ha (occ e.1))
      (Fintype.card X) (inventory_bound X (D.grade c) ha (occ c))
      hτ hγ (bot_lt_iff_ne_bot.mpr hγb) hbound hface hpc
  obtain ⟨d₀, _, hd₀⟩ := H.exists_witness
  obtain ⟨B, hB, he⟩ := CanonicalOwnerBoundary.endpoint_grid ha (occ d₀.1) fun hbot =>
    hhpos.ne (hd₀.symm.trans (by rw [Function.comp_apply, hbot]; rfl)).symm
  have hBeq : h = CanonicalPairedInverse.grid (D.grade c) B := hd₀.symm.trans he
  let old : Section sem U V := {
    onLeft := fun d => a (occ d.1)
    onRight := fun d => a (occ d.1)
    left_lawful := hs.toBelow U
    right_lawful := hs.toBelow V
    overlap := fun _ _ _ => rfl }
  obtain ⟨u, hu, hucap', hrread⟩ := extend_boundary hcover hcU hOU hOV hinter hleft hright
    old f h hf (selfVis_mono hvis hU) (selfVis_mono hvis hV) (fun d => (hfcap d).symm)
  have hucap (d : Cell D) : min (u d) h = min (a (occ d)) h :=
    (hucap' d).trans (congrArg (min · h) (by
      rcases hcover d with hu' | hv'
      · exact old.whole_left hcover ⟨d, hu'⟩
      · exact old.whole_right hcover ⟨d, hv'⟩))
  have huface (e : D.below (D.cell c)) := (hrread e).trans (congrFun hfeq e)
  let tail := 2 * Fintype.card X + 1
  let S := RelativePrefixEncoding.inventory pp δ
  let T := S.card + tail
  let C := CanonicalPairedInverse.grid (D.grade c) (T + 1)
  have hC : SelfVis (D.grade c) C := CanonicalPairedInverse.grid_visible _ _
  have hhC : h ≤ C := hroom.le.trans (ofOrd_le_ofOrd.mpr (le_trans
    (by gcongr; dsimp [T]; omega) le_self_add))
  have hfC (e : D.below (D.cell c)) : u e.1 ≤ C := by
    rw [huface]
    change AlignedCutEncoding.encode (fun e => a (occ e.1)) pp (D.grade c) tail h δ e ≤ C
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
  have hvt : ∀ d, v d ≠ ⊤ := fun d hd => by
    change min (u d) C = ⊤ at hd
    exact ofOrd_ne_top _ (top_le_iff.mp (hd ▸ min_le_right (u d) C))
  obtain ⟨w, hw, hwold, hwcap⟩ := hpref hv hvt (hB.trans (Nat.le_succ _)) fun d => by
    dsimp only [v]; rw [← hBeq, min_assoc, min_eq_right hhC, hucap d]
  have hamb (d : K.below (A, D.grade c)) : min (ρ (src d.1)) γ = min (q d) γ :=
    (hretune _ (hshort d.1)).trans ((min_eq_left (hbound _)).trans (hambient d))
  have hmid : RespectsSemanticsBelow Rws (A, D.grade c) (fun d => ρ (src d.1)) :=
    map_respects_of_positive_cap_agreement hsrc hq hK (boundedMap_of_witness hρ) hγb hamb
  obtain ⟨q', hq', hq'read, hq'cap⟩ := AlignedCutEncoding.decode_lift
    (fun d => src d.1) pp (fun e => oldT e.1) hw hmid hK hρ hδvis
    (fun he => hγb (le_bot_iff.mp (he ▸ hγδ))) hroom hρh.ge
    (fun d => by rw [hBeq]; exact hwcap d.1) (fun _ => rfl)
    (fun e => by
      change min (pp e) δ = min (ρ (src (oldT e.1).1)) δ
      rw [hbdry]; dsimp only [pp]; rw [min_assoc, min_eq_right hδM]; exact hread e)
    fun e => by
      have hs' : ((fun d : K.below (A, D.grade c) => src d.1) ∘ fun e : D.below (D.cell c) => oldT e.1) =
          fun e => a (occ e.1) := funext fun e => hbdry e.1
      rw [hs']
      change w (oldT e.1).1 = _
      rw [hwold, show v e.1 = u e.1 from min_eq_left (hfC e), huface]; rfl
  refine ⟨q', hq', hq'read, fun d => ?_⟩
  have he := congrArg (min · γ) (hq'cap d)
  simp only [min_assoc, min_eq_right hγδ] at he
  exact he.trans (hamb d)
