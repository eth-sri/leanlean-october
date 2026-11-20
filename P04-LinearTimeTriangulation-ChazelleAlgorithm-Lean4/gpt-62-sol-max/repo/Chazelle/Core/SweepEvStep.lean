module

public import Chazelle.Core.SweepEvDet
public import Chazelle.Core.SweepEvNoTie

/-!
# The sweep (WP-D), stage 3: the step of the event loop

* `f2_cases`: a chord of `F₂⁺` is seen from an end of a chord of `S₂` along it, or is a shared
  chord, or a top chord;
* `nonstop_cases`: a chord of `F₂⁺` that is not a stop chord is seen from an end `a` of a chord
  `c ∈ S₂` lying on `C₂`, other than the shared vertex and the top of `C₂` (an endpoint query);
* `nonstop_found` (**all non-stop chords at the next key are found**): from the invariant at
  `oK ≥ Lst`, every non-stop chord at the next cut key `K` is seen from an end of a chord of `S₂`
  touching a region of the label set or a gap region, or of the chord of `S₂` containing a stop
  chord at `K`;
* `evInv_step` (**the label rule**): at the next key, a pocket chord resets nothing (every later
  position is enclosed), anchored chords give the new label set (their side labels), and bracket
  chords alone keep the label set.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Step

variable {J : Merge.Junction}

/-- **The three kinds of chords of `F₂⁺`.** -/
theorem f2_cases {S₂ : Set (Set Point)} (_hS₂ : S₂ ⊆ Merge.augChords J.right) {e : Set Point}
    (he : e ∈ F₂plus J S₂) :
    (∃ c ∈ S₂, ∃ (a : Point) (σ : ℝ), ((σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) ∧
      FreeAt J.whole a σ ∧ e = Merge.shoot J.whole a σ) ∨
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ FreeAt J.whole J.shared σ ∧ e = Merge.shoot J.whole J.shared σ) ∨
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ FreeAt J.whole J.right.top σ ∧
      e = Merge.shoot J.whole J.right.top σ) := by
  rcases he with ((⟨c', hc', hfree, rfl⟩ | ⟨c', hc', hfree, rfl⟩) | hsh) | htop
  · have hc'S : c' ∈ S₂ := by simpa using hc'
    exact Or.inl ⟨c', hc'S, _, 1, Or.inl ⟨rfl, rfl⟩, hfree, rfl⟩
  · have hc'S : c' ∈ S₂ := by simpa using hc'
    exact Or.inl ⟨c', hc'S, _, -1, Or.inr ⟨rfl, rfl⟩, hfree, rfl⟩
  · obtain ⟨σ, hσ, hfree, rfl⟩ := hsh
    exact Or.inr (Or.inl ⟨σ, hσ, (Merge.freeAt_vertex _ _ _).2 hfree, rfl⟩)
  · obtain ⟨σ, hσ, hfree, rfl⟩ := htop
    have hv : J.whole.vertex (J.m₁ + J.right.topIdx) = J.right.top := by
      rw [Merge.Junction.whole_vertex_add]; rfl
    refine Or.inr (Or.inr ⟨σ, hσ, ?_, ?_⟩)
    · rw [← hv]; exact (Merge.freeAt_vertex _ _ _).2 hfree
    · rw [← hv]; rfl

/-- A chord seen from an end of a chord of `S₂` along it lies in it. -/
theorem shoot_sub_end {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point}
    (hc : c ∈ S₂) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) :
    Merge.shoot J.whole a σ ⊆ c := by
  obtain ⟨y, l, r, hH, hy, hceq, hl, hr⟩ := Merge.augChords_spec (hS₂ hc)
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hl, hceq]
    exact Merge.shoot_subset_pos J.whole hH.lt (fun hd => hH.right_not (dom_right J hd hy))
  · rw [hr, hceq]
    exact Merge.shoot_subset_neg J.whole hH.lt (fun hd => hH.left_not (dom_right J hd hy))

/-- **A non-stop chord is an endpoint-query chord.** -/
theorem nonstop_cases {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) {e : Set Point}
    (he : e ∈ F₂plus J S₂) (hns : ¬ StopChord2 J S₂ e) :
    ∃ c ∈ S₂, ∃ (a : Point) (σ : ℝ), ((σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) ∧
      a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ FreeAt J.whole a σ ∧
      e = Merge.shoot J.whole a σ := by
  rcases f2_cases hS₂ he with ⟨c, hc, a, σ, ha, hfree, rfl⟩ | ⟨σ, hσ, hfree, rfl⟩ |
      ⟨σ, hσ, hfree, rfl⟩
  · refine ⟨c, hc, a, σ, ha, ?_, ?_, ?_, hfree, rfl⟩
    · by_contra hn
      exact hns (Or.inl (Or.inr ⟨c, hc, a, σ, ha, hn, hfree, rfl⟩))
    · rintro rfl
      have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
      exact hns (Or.inl (Or.inl ⟨σ, hσ, hfree, rfl⟩))
    · rintro rfl
      have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
      exact hns (Or.inr ⟨σ, hσ, hfree, rfl⟩)
  · exact absurd (Or.inl (Or.inl ⟨σ, hσ, hfree, rfl⟩)) hns
  · exact absurd (Or.inr ⟨σ, hσ, hfree, rfl⟩) hns

/-- **Every non-stop chord at the next key is found** from the label set, the gap regions, or
the chord of `S₂` containing a stop chord at the key. -/
theorem nonstop_found (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {oK : ℝ} {Λ : Set (Set Point)}
    (hLK : (Lst J : ℝ) ≤ oK) (hInv : EvInv J S₂ oK Λ) {pK : ℕ} {tK : ℝ}
    (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hoK : oK < oW J (pK + tK))
    (hgap : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      ¬ (oK < oW J (q + s) ∧ oW J (q + s) < oW J (pK + tK)))
    {e : Set Point} (he : e ∈ F₂plus J S₂) (heK : SideAttach (chainModel J.whole).W e pK tK)
    (hns : ¬ StopChord2 J S₂ e) :
    ∃ c ∈ S₂, ∃ (a : Point) (σ : ℝ), ((σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) ∧
      a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ FreeAt J.whole a σ ∧
      e = Merge.shoot J.whole a σ ∧
      ((∃ V ∈ (chainModel J.right).regions S₂, (V ∈ Λ ∨ GapLab J S₂ V) ∧
          Chazelle.Chain.TouchesIn (chainModel J.right).D c V) ∨
        (∃ s ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W s pK tK ∧ StopChord2 J S₂ s ∧
          s ⊆ c)) := by
  have hS₂a := hS₂.2.1
  have hS₂f := hS₂.1
  have hNTV : NoTieV J S₂ := noTieV hP hS₂a
  have hLt : (Lst J : ℝ) < oW J (pK + tK) := by linarith
  obtain ⟨c, hc, a, σ, ha, haR, hav, hat, hfree, rfl⟩ := nonstop_cases hS₂a he hns
  have hsub := shoot_sub_end hS₂a hc ha
  rcases det_of_evInv hP hS₂ hF hLK hInv hpK htK0 htK1 hoK hgap he heK with
    ⟨s, hs, hsK, hss⟩ | ⟨h, hh, hhK, a', σ', c', V, hc', hV, hVΛ, hT, ha', ha'R, ha'v, ha't,
      hfree', rfl⟩
  · -- a stop chord at the key: it is the other piece of `c`
    have hne : Merge.shoot J.whole a σ ≠ s := fun h' => hns (h' ▸ hss)
    have hpar := partner_of_parent hP hS₂a hS₂f hNTV he hs hne hc hsub heK hsK hLt
    refine ⟨c, hc, a, σ, ha, haR, hav, hat, hfree, rfl, Or.inr ⟨s, hs, hsK, hss, ?_⟩⟩
    rcases hpar with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact shoot_sub_end hS₂a hc (Or.inl ⟨rfl, rfl⟩)
    · exact shoot_sub_end hS₂a hc (Or.inr ⟨rfl, rfl⟩)
  · by_cases hhe : Merge.shoot J.whole a' σ' = Merge.shoot J.whole a σ
    · rw [← hhe]
      exact ⟨c', hc', a', σ', ha', ha'R, ha'v, ha't, hfree', rfl, Or.inl ⟨V, hV, hVΛ, hT⟩⟩
    · -- the other piece of `c'`
      have hsub' := shoot_sub_end hS₂a hc' ha'
      have hpar := partner_of_parent hP hS₂a hS₂f hNTV hh he hhe hc' hsub' hhK heK hLt
      rcases hpar with ⟨hf₁, he₁⟩ | ⟨hf₁, he₁⟩
      · rw [he₁] at hns ⊢
        obtain ⟨c₂, hc₂, a₂, σ₂, ha₂, ha₂R, ha₂v, ha₂t, hfree₂, he₂⟩ :=
          nonstop_cases hS₂a (he₁ ▸ he) hns
        have hR : Merge.lend c' ∈ J.right.set := by
          by_contra hn
          exact hns (Or.inl (Or.inr ⟨c', hc', _, 1, Or.inl ⟨rfl, rfl⟩, hn, hf₁, rfl⟩))
        have hv : Merge.lend c' ≠ J.shared := by
          intro hv; rw [hv] at hf₁ hns
          exact hns (Or.inl (Or.inl ⟨1, Or.inl rfl, hf₁, rfl⟩))
        have ht : Merge.lend c' ≠ J.right.top := by
          intro ht; rw [ht] at hf₁ hns
          exact hns (Or.inr ⟨1, Or.inl rfl, hf₁, rfl⟩)
        exact ⟨c', hc', _, 1, Or.inl ⟨rfl, rfl⟩, hR, hv, ht, hf₁, rfl, Or.inl ⟨V, hV, hVΛ, hT⟩⟩
      · rw [he₁] at hns ⊢
        have hR : Merge.rend c' ∈ J.right.set := by
          by_contra hn
          exact hns (Or.inl (Or.inr ⟨c', hc', _, -1, Or.inr ⟨rfl, rfl⟩, hn, hf₁, rfl⟩))
        have hv : Merge.rend c' ≠ J.shared := by
          intro hv; rw [hv] at hf₁ hns
          exact hns (Or.inl (Or.inl ⟨-1, Or.inr rfl, hf₁, rfl⟩))
        have ht : Merge.rend c' ≠ J.right.top := by
          intro ht; rw [ht] at hf₁ hns
          exact hns (Or.inr ⟨-1, Or.inr rfl, hf₁, rfl⟩)
        exact ⟨c', hc', _, -1, Or.inr ⟨rfl, rfl⟩, hR, hv, ht, hf₁, rfl, Or.inl ⟨V, hV, hVΛ, hT⟩⟩

/-- The right stretch is not empty. -/
theorem Lst_pos (J : Merge.Junction) : (0 : ℝ) < Lst J := by
  have h1 := J.right.one_le
  have h2 : J.right.m = J.m₂ := rfl
  have : 0 < Lst J := by
    unfold Lst; rw [rL1_add_rL2]; unfold rlen
    split_ifs <;> omega
  exact_mod_cast this

/-- **The label rule at a key.**  From the invariant at `oL`, at the next key `K` (no cut in
between): if a chord at `K` is attached at offset `0` (a pocket), any label set; if some chord at
`K` is anchored, a label set containing the side labels of every anchored chord at `K`; otherwise
(bracket chords only) the old label set. -/
theorem evInv_step (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {oL : ℝ} {Λ : Set (Set Point)}
    (hInv : EvInv J S₂ oL Λ) {pK : ℕ} {tK : ℝ}
    (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hLst : (Lst J : ℝ) ≤ oW J (pK + tK)) (hoL : oL ≤ oW J (pK + tK))
    (hgap : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      ¬ (oL < oW J (q + s) ∧ oW J (q + s) < oW J (pK + tK)))
    {Λ' : Set (Set Point)}
    (hrule : (∃ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK ∧
        ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ oW J (q + s) = 0) ∨
      ((∃ Z ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W Z pK tK ∧ ¬ EvBrk J Z) ∧
        ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → ¬ EvBrk J e →
          EvSideLab J S₂ Λ' e) ∨
      ((∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → EvBrk J e) ∧ Λ' = Λ)) :
    EvInv J S₂ (oW J (pK + tK)) Λ' := by
  have hS₂a := hS₂.2.1
  have hS₂f := hS₂.1
  have hC := corr_right0 J hP hS₂a hS₂f
  by_cases hpock : ∃ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK ∧
      ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ oW J (q + s) = 0
  · obtain ⟨e, he, heK, q, s, hQ, hQ0⟩ := hpock
    have hne : sidePt (chainModel J.whole).W pK tK ≠ sidePt (chainModel J.whole).W q s := by
      intro h
      obtain ⟨rfl, rfl⟩ := hC.hM.attach_unique (hC.hF he) heK hQ h
      have := Lst_pos J
      linarith
    exact evInv_pocket he heK hQ hne hLst hQ0 Λ'
  push Not at hpock
  rcases hrule with h | ⟨⟨Z, hZ, hZK, hZb⟩, hlab⟩ | ⟨hbr, rfl⟩
  · obtain ⟨e, he, heK, q, s, hQ, hQ0⟩ := h
    exact absurd hQ0 (hpock e he heK q s hQ)
  · unfold EvBrk at hZb
    push Not at hZb
    obtain ⟨pz, tz, hZz, hzL⟩ := hZb
    exact evInv_anchor hP hS₂ hF (noTieV hP hS₂a) hpK htK0 htK1 hLst hZ hZK hZz hzL
      (fun e he heK q s hQ => hpock e he heK q s hQ)
      (fun e he heK hnb _ => hlab e he heK hnb)
  · refine evInv_mono hInv hoL fun e he q s hQ h1 h2 => ?_
    rcases h2.lt_or_eq with h2 | h2
    · exact absurd ⟨h1, h2⟩ (hgap e he q s hQ)
    · obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hQ.1 hpK hQ.2.1 hQ.2.2.1 htK0 htK1 h2
      exact hbr e he hQ

end Step

end Sweep

end

end Chazelle.Core
