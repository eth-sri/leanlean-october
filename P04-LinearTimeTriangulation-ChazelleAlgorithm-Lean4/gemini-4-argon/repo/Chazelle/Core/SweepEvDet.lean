module

public import Chazelle.Core.SweepEvAnchor2

/-!
# The sweep (WP-D), stage 3: completeness of the detection from the invariant

* `stop_of_brk`: a chord with no attachment in the open right stretch is a stop chord;
* `det_of_evInv` (**completeness**): from `EvInv` at a key `K`, the next cut key `K*` carries a stop
  chord, or a chord seen from an endpoint `a` (on `C₂`, neither the shared vertex nor the top of
  `C₂`) of a chord `c ∈ S₂` touching a region of the label set or a gap region — the RAM's
  detection origins;
* `partner_of_parent`: a second chord at a key of the `C₁` part (beyond the start) is a piece of the
  chord of `S₂` containing the first (the RAM finds it from the other end).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Det

variable {J : Merge.Junction}

/-- **A chord without attachment in the open right stretch is a stop chord.** -/
theorem stop_of_out (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {e : Set Point}
    (he : e ∈ F₂plus J S₂)
    (hout : ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      ¬ (0 < oW J (q + s) ∧ oW J (q + s) < Lst J)) : StopChord2 J S₂ e := by
  by_contra h
  have hns : ¬ StopChord J S₂ e := fun h' => h (Or.inl h')
  obtain ⟨pB, tB, hB, h1, h2, -, -⟩ := stretch_end J hP hS₂ hS₂f he hns
  exact hout pB tB hB ⟨h1, h2⟩

/-- **Completeness of the detection from the invariant.** -/
theorem det_of_evInv (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {oK : ℝ} {Λ : Set (Set Point)}
    (hLK : (Lst J : ℝ) ≤ oK) (hInv : EvInv J S₂ oK Λ) {pK : ℕ} {tK : ℝ}
    (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hoK : oK < oW J (pK + tK))
    (hgap : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      ¬ (oK < oW J (q + s) ∧ oW J (q + s) < oW J (pK + tK)))
    {e : Set Point} (he : e ∈ F₂plus J S₂) (heK : SideAttach (chainModel J.whole).W e pK tK) :
    (∃ s ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W s pK tK ∧ StopChord2 J S₂ s) ∨
    ∃ h ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W h pK tK ∧
      ∃ (a : Point) (σ : ℝ) (c V : Set Point), c ∈ S₂ ∧ V ∈ (chainModel J.right).regions S₂ ∧
        (V ∈ Λ ∨ GapLab J S₂ V) ∧ Chazelle.Chain.TouchesIn (chainModel J.right).D c V ∧
        ((σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c)) ∧ a ∈ J.right.set ∧
        a ≠ J.shared ∧ a ≠ J.right.top ∧ FreeAt J.whole a σ ∧ h = Merge.shoot J.whole a σ := by
  have hS₂a := hS₂.2.1
  have hS₂f := hS₂.1
  have hC := corr_right0 J hP hS₂a hS₂f
  have hM := hC.hM
  -- a non-cut position just before `K*`, after `K`
  obtain ⟨Rb, hRb, -, w, u, hw, hu, hncw, hfw, h1, h2, hgw⟩ := before_region_exists' hP hS₂a hS₂f
    hpK htK0 htK1 (by linarith) (show 0 < oW J (pK + tK) - oK by linarith)
  have hpos := hInv w u hw hu hncw (by linarith) (fun e' he' q s hQ h3 h4 =>
    absurd ⟨h3, by linarith⟩ (hgap e' he' q s hQ))
  rcases hpos with hE | hval
  · -- enclosed: every chord at `K*` is a stop chord
    left
    obtain ⟨e', he', qa, qb, sa, sb, hA, hB, hAB, hLa, hay, hby⟩ := hE
    have hqa : oW J (qa + sa) ≤ oK := by
      by_contra h; push Not at h; exact hgap e' he' qa sa hA ⟨h, by linarith⟩
    rcases hby with hby | hby
    · -- a bracket
      have hqb : oW J (pK + tK) ≤ oW J (qb + sb) := by
        by_contra h; push Not at h; exact hgap e' he' qb sb hB ⟨by linarith, h⟩
      rcases hqb.lt_or_eq with hqb | hqb
      · -- `K*` strictly inside: `e` is a bracket
        refine ⟨e, he, heK, stop_of_out hP hS₂a hS₂f he fun q s hQ h => ?_⟩
        by_cases hee : e' = e
        · subst hee
          rcases key_of_two hM (hC.hF he') hA hB hAB hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            linarith [h.2]
        · have := closed_nested hP hS₂a hS₂f he' he hee hA hB (by linarith) heK (by linarith) hqb hQ
          linarith [this.1, h.2]
      · -- `K*` is the closer: the bracket chord itself is a stop
        obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hB.1 hpK hB.2.1 hB.2.2.1 htK0 htK1 hqb.symm
        refine ⟨e', he', hB, stop_of_out hP hS₂a hS₂f he' fun q s hQ h => ?_⟩
        rcases key_of_two hM (hC.hF he') hA hB hAB hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          linarith [h.2]
    · -- a pocket: the chords after it are stops
      refine ⟨e, he, heK, stop_of_out hP hS₂a hS₂f he fun q s hQ h => ?_⟩
      have hee : e' ≠ e := by
        rintro rfl
        rcases key_of_two hM (hC.hF he') hA hB hAB heK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
      -- the other attachment of `e` in `(0, Lst)` would put `K*` inside `[0, A]`
      have := closed_nested hP hS₂a hS₂f he' he hee hB hA (by linarith) hQ (by linarith [h.1])
        (by linarith [h.2]) heK
      linarith [this.2]
  · -- a valid label: the next event of `next_event_origin`
    obtain ⟨L, hL, hLr, hv⟩ := hval Rb hRb hfw
    by_cases hstop : ∃ s ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W s pK tK ∧ StopChord J S₂ s
    · obtain ⟨s, hs, hsK, hss⟩ := hstop
      exact Or.inl ⟨s, hs, hsK, Or.inl hss⟩
    push Not at hstop
    obtain ⟨h, hh, hhK, a, σ, hσ, hfree, rfl, hcase⟩ := next_event_origin J hP hS₂ hF hRb hLr hv hw hu
      hncw hfw (show (Lst J : ℝ) < oW J (w + u) by linarith) hpK htK0 htK1 h2
      (fun x hx hx0 hxn ⟨h3, h4⟩ => hgw x hx hx0 hxn ⟨h3, h4⟩) he heK hstop
    rcases hcase with ⟨c, hc, ⟨V, hLV, hT⟩, hac, ha, hav⟩ | hat
    · by_cases hatop : a = J.right.top
      · subst hatop
        exact Or.inl ⟨_, hh, hhK, Or.inr ⟨σ, hσ, hfree, rfl⟩⟩
      right
      have hV : V ∈ (chainModel J.right).regions S₂ ∧ (V ∈ Λ ∨ GapLab J S₂ V) := by
        rcases hLV with rfl | hg
        · rcases hL with hL | hL
          · exact ⟨hLr, Or.inl hL⟩
          · exact ⟨hLr, Or.inr hL⟩
        · exact ⟨hg.2.1, Or.inr hg⟩
      exact ⟨_, hh, hhK, a, σ, c, V, hc, hV.1, hV.2, hT, hac, ha, hav, hatop, hfree, rfl⟩
    · subst hat
      exact Or.inl ⟨_, hh, hhK, Or.inr ⟨σ, hσ, hfree, rfl⟩⟩

/-- **The partner at a tie** (beyond the start): a second chord `e'` at the key of a chord `e`
inside `c ∈ S₂` is the chord seen from an end of `c`. -/
theorem partner_of_parent (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hNTV : NoTieV J S₂)
    {e e' c : Set Point} (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e ≠ e')
    (hc : c ∈ S₂) (hec : e ⊆ c) {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W e p t)
    (hA' : SideAttach (chainModel J.whole).W e' p t) (hL : (Lst J : ℝ) < oW J (p + t)) :
    (FreeAt J.whole (Merge.lend c) 1 ∧ e' = Merge.shoot J.whole (Merge.lend c) 1) ∨
      (FreeAt J.whole (Merge.rend c) (-1) ∧ e' = Merge.shoot J.whole (Merge.rend c) (-1)) := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hD : sidePt (chainModel J.whole).W p t ∈ J.right.dom := by
    rcases tie_dom hP hS₂ hS₂f he he' hne hA hA' (fun h => by linarith [h.2]) with h | h
    · exact h
    · exact (hNTV e he e' he' hne p t hA hA' h hL).elim
  obtain ⟨c', hc', hec', he'c'⟩ := tie_parent J hP hS₂ he he' (Ne.symm hne) hA hA' hD
  -- two distinct points of `e`
  obtain ⟨pb, tb, hB, hBne⟩ := hC.hM.other_attach (hC.hF he) hA
  have hcc : c' = c := parent_unique hS₂ hc' hc hBne (hec' hB.2.2.2.1) (hec' hA.2.2.2.1)
    (hec hB.2.2.2.1) (hec hA.2.2.2.1)
  subst hcc
  exact piece_of_parent J hP hS₂ he' hc' he'c' hA' hD

end Det

end Sweep

end

end Chazelle.Core
