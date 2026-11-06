module

public import Chazelle.Core.SweepEvStopLab3
public import Chazelle.Core.SweepEvStopLabSG

/-!
# The sweep (WP-D), stage 2: the side labels of an anchored stop chord (`LabTask`)

`labTask_of (h : SplitGapTask) : LabTask`.  For each side of the stop chord `e` attached at the
position `(gW + d, t)` of the open right stretch:

* the faced sides: the label faced at the counterpart position (`slb_faced`);
* away from the split vertex: the sides of the chord of `S₂` containing `e` (`slb_part1`), the
  middle region of a tie with a fused partner (`slb_middle_fused`; non-fused partners do not occur,
  `slb_nonfused_tie`);
* at the split vertex (case G): `split_step` for a chord inside a chord of `S₂`; the middle region
  of a tie is `TieOut` (`slb_tieOut`) or has a gap label (`SplitGapTask`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Sweep
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed

@[expose] public section

variable {J : Merge.Junction}

/-- **The faced sides, and the middle sides through a handler.** -/
theorem slb_part2_core (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {e : Set Point}
    (he : e ∈ F₂plus J S₂) {d : ℕ} (hd : d < Lst J) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hd1 : t = 0 → 1 ≤ d)
    (hA : SideAttach (chainModel J.whole).W e ((gW J + d) % (chainModel J.whole).W.n) t)
    {Va Vb : Set Point} (hVa : Va ∈ (chainModel J.right).regions S₂)
    (hVb : Vb ∈ (chainModel J.right).regions S₂)
    (ha : AfterFaces (chainModel J.right) (cpA J d) t Va)
    (hb0 : 0 < t → BeforeFaces (chainModel J.right) (cpA J d) t Vb)
    (hb1 : t = 0 → BeforeFaces (chainModel J.right) (cpB J d) 0 Vb)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hS : SideOf (chainModel J.whole) ρ e G)
    (hmid : ∀ e' ∈ F₂plus J S₂, e' ≠ e →
      SideAttach (chainModel J.whole).W e' ((gW J + d) % (chainModel J.whole).W.n) 0 → t = 0 →
      SideOf (chainModel J.whole) ρ e' G → EvVal J S₂ {Va, Vb} G) :
    EvVal J S₂ {Va, Vb} G := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hGM : GoodModel (chainModel J.whole) := Or.inl ⟨J.whole, hP, rfl⟩
  obtain ⟨dir, hdir1, hdir⟩ : ∃ dir : ℝ, (dir = 1 ∨ dir = -1) ∧
      ((dir = 1 ∧ ∀ z ∈ e, (sidePt (chainModel J.whole).W
          ((gW J + d) % (chainModel J.whole).W.n) t).1 ≤ z.1) ∨
        (dir = -1 ∧ ∀ z ∈ e, z.1 ≤ (sidePt (chainModel J.whole).W
          ((gW J + d) % (chainModel J.whole).W.n) t).1)) := by
    rcases hC.hM.attach_dir (hC.hF he) hA with h | h
    · exact ⟨1, Or.inl rfl, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨-1, Or.inr rfl, Or.inr ⟨rfl, h⟩⟩
  have hρd : ρ * dir = 1 ∨ ρ * dir = -1 := by
    rcases hρ with rfl | rfl <;> rcases hdir1 with rfl | rfl <;> norm_num
  have hfo := faced_or_middle hGM hF he hA hρ hG hS hdir
  have faced := fun (hfac : FacedSide (chainModel J.whole)
      ((gW J + d) % (chainModel J.whole).W.n) t ρ dir G) =>
    slb_faced hP hS₂ hd ht0 ht1 hd1 hG hfac hρd hVa hVb ha hb0 hb1
  by_cases huniq : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e'
      ((gW J + d) % (chainModel J.whole).W.n) t → e' = e
  · exact faced (hfo.1 huniq)
  push Not at huniq
  obtain ⟨e', he', hA', hne⟩ := huniq
  obtain ⟨ht, hne', hdn, hup⟩ := hfo.2 e' he' hne hA'
  subst ht
  rcases lt_or_gt_of_ne hne' with h | h
  · rcases hρ with rfl | rfl
    · exact hmid e' he' hne hA' rfl ((hdn h).1 rfl)
    · exact faced ((hdn h).2 rfl)
  · rcases hρ with rfl | rfl
    · exact faced ((hup h).2 rfl)
    · exact hmid e' he' hne hA' rfl ((hup h).1 rfl)

/-- **The middle region of a tie at the split vertex.** -/
theorem slb_split_middle (hSG : SplitGapTask) (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set (Set Point)} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {e e' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e) (hlt : rL1 J < Lst J)
    (hd0 : rL1 J ≠ 0)
    (hA : SideAttach (chainModel J.whole).W e ((gW J + rL1 J) % (chainModel J.whole).W.n) 0)
    (hA' : SideAttach (chainModel J.whole).W e' ((gW J + rL1 J) % (chainModel J.whole).W.n) 0)
    (hK : ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ (Lst J : ℝ) ≤ oW J (q + s))
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hS : SideOf (chainModel J.whole) ρ e G) (hS' : SideOf (chainModel J.whole) ρ e' G)
    {Λ : Set (Set Point)} {L : Set Point} (hL : L ∈ Λ)
    (hLr : L ∈ (chainModel J.right).regions S₂) : EvVal J S₂ Λ G := by
  by_cases hOff : OffOut J e' ((gW J + rL1 J) % (chainModel J.whole).W.n) 0
  · exact slb_evVal hL hLr (valid_of_tieOut J hP hS₂ hF hG
      (slb_tieOut hP hS₂ hF he he' hne hlt hd0 hA hA' hK hOff hρ hS hS') L)
  · unfold OffOut at hOff
    push Not at hOff
    obtain ⟨p', t', h1, h2, h3, h4⟩ := hOff
    obtain ⟨Vg, hgap, hRL⟩ := hSG J Q S₂ hP hS₂ hF (slb_rδ_pos hlt) e he e' he' hne hA hA' hK
      ⟨p', t', h1, h2, h3, h4⟩ ρ hρ G hG hS hS'
    rcases hRL with hRL | hVL
    · exact ⟨Vg, Or.inr hgap, hgap.2.1, valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hgap.2.1 hRL⟩
    · exact ⟨Vg, Or.inr hgap, hgap.2.1, valid_of_vlabel J hP hS₂ hF hG hgap.2.1 hVL⟩

/-- **`LabTask` from `SplitGapTask`.** -/
theorem labTask_of (hSG : SplitGapTask) : LabTask := by
  intro J Q S₂ e hP hS₂ hF he _hstop _hnp hK d t hd ht0 ht1 hd0 hA
  have hd1 : t = 0 → 1 ≤ d := fun h => Nat.one_le_iff_ne_zero.2 (hd0 h)
  by_cases hsp : t = 0 ∧ d = rL1 J
  · -- the split vertex
    obtain ⟨rfl, rfl⟩ := hsp
    have hd0'  := hd0 rfl
    have hlt  := hd
    have hδ := slb_rδ_pos hlt
    refine ⟨fun c hc hec Vu hVu Vd hVd hsu hsd => ?_, fun hnf Va hVa Vb hVb ha hb0 hb1 => ?_⟩
    · intro G hG ρ hρ hS
      have key : ∀ V, V ∈ ({Vu, Vd} : Set (Set Point)) → V ∈ (chainModel J.right).regions S₂ →
          SideOf (chainModel J.right) ρ c V → EvVal J S₂ {Vu, Vd} G := by
        intro V hVΛ hV hVs
        rcases split_step J hP hS₂ hF hδ he (subset_S₂x J S₂ hc) hec hA hρ hG hV hS hVs with
          hRL | ⟨-, Vg, hgVg, hRLg⟩ | ⟨-, f', hf', hf'ne, hf'A, hf'S, -⟩
        · exact slb_evVal hVΛ hV (valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hV hRL)
        · exact ⟨Vg, Or.inr hgVg, hgVg.2.1, valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hgVg.2.1 hRLg⟩
        · exact slb_split_middle hSG hP hS₂ hF he hf' hf'ne hlt hd0' hA hf'A hK hρ hG hS hf'S
            hVΛ hV
      rcases hρ with rfl | rfl
      · exact key Vu (Set.mem_insert _ _) hVu hsu
      · exact key Vd (Set.mem_insert_of_mem _ rfl) hVd hsd
    · intro G hG ρ hρ hS
      exact slb_part2_core hP hS₂ hF he hd le_rfl zero_lt_one hd1 hA hVa hVb ha hb0 hb1 hρ hG hS
        (fun e' he' hne hA' _ hS' => slb_split_middle hSG hP hS₂ hF he he' hne hlt hd0' hA hA'
          hK hρ hG hS hS' (Set.mem_insert _ _) hVa)
  · -- away from the split vertex
    have hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J := fun ht => ⟨hd0 ht, fun h => hsp ⟨ht, h⟩⟩
    refine ⟨fun c hc hec Vu hVu Vd hVd hsu hsd =>
      slb_part1 hP hS₂ hF he hc hec hd ht0 ht1 hsec hA hVu hVd hsu hsd,
      fun hnf Va hVa Vb hVb ha hb0 hb1 => ?_⟩
    intro G hG ρ hρ hS
    refine slb_part2_core hP hS₂ hF he hd ht0 ht1 hd1 hA hVa hVb ha hb0 hb1 hρ hG hS ?_
    intro e' he' hne hA' ht hS'
    subst ht
    obtain ⟨hd0', hdr⟩ := hsec rfl
    by_cases hfus : ∃ c' ∈ S₂, e' ⊆ c'
    · obtain ⟨c', hc', he'c'⟩ := hfus
      exact slb_middle_fused hP hS₂ hF he he' hne hnf hc' he'c' hd hd0' hdr hA hA' hρ hG hS'
        hVa hVb ha (hb1 rfl)
    · push Not at hfus
      exact (slb_nonfused_tie hP hS₂ he he' hne hnf hfus hd hd0' hdr hA hA').elim

end

end SweepEv

end Chazelle.Core
