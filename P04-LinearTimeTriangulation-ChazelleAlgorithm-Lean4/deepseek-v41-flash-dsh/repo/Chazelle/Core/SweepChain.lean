module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvent
public import Chazelle.Core.FactsTie

/-!
# The sweep (WP-D), part 8: chains of chords (lemma (E) without uniqueness)

At a walk vertex two chords of an admissible family can be attached at one position (a *tie*,
`FactsTie`): one goes east, one goes west, and one region lies on the same side of both (the
*middle* region, which faces no walk position near the vertex).  A region of `F₂⁺` above a fused
chord can therefore be a middle region at the `C₂` end of that chord, and its label must be found
further along the chain of collinear chords through the tie.

* `SideOf`: the region containing the points just on one side (`ρ = 1`: above, `ρ = -1`: below)
  of every point of a chord in the domain.
* `off_step`, `chord_bound`: the arithmetic of offsets behind the planarity argument: the
  positions facing a region on one side of a chord lie beyond the chord in walk order.
* `local_step`: at a position of the right stretch, the side of a fused chord is faced (and then
  carries a label), or the position is a tie whose other chord continues the chain.
* `half_walk`: walking along the chain in one direction gives a label or a bound.
* `label_side_gen` (**lemma (E)**): the labels of the region on the side `ρ` of a fused chord
  `e ⊆ c ∈ S₂` attached in the right stretch are the region on the side `ρ` of `c`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft freeIn regionsIn
  sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Jordan (offset)
open Chazelle.Geometry (lerp)
open WalkEmbed

namespace Sweep

/-! ## Sides of a chord -/

/-- `U` contains the points just on the side `ρ` (`1`: above, `-1`: below) of every point of the
chord `c` in the domain. -/
def SideOf (M : Model) (ρ : ℝ) (c U : Set Point) : Prop :=
  ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + ρ * δ) : Point) ∈ U

theorem sideOf_one_iff {M : Model} {c U : Set Point} : SideOf M 1 c U ↔ M.AboveOf c U := by
  unfold SideOf Model.AboveOf; simp

theorem sideOf_neg_one_iff {M : Model} {c U : Set Point} :
    SideOf M (-1) c U ↔ M.BelowOf c U := by
  unfold SideOf Model.BelowOf; simp [sub_eq_add_neg]

/-- Two regions on the same side of a chord (with a point in the domain) are equal. -/
theorem sideOf_eq {M : Model} {F : Set (Set Point)} {ρ : ℝ} {c U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) (h : SideOf M ρ c U) (h' : SideOf M ρ c U')
    {z : Point} (hz : z ∈ c) (hzD : z ∈ M.D) : U = U' :=
  region_eq_of_side hU hU' (h z hz hzD) (h' z hz hzD)

/-- A region on the side `ρ` of a horizontal chord contains the points just left of the chord
directed so that `ρ` is on its left. -/
theorem left_of_side {M : Model} {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {c U : Set Point}
    (h : SideOf M ρ c U) {a b : Point} (hab : a.2 = b.2) (hmid : lerp a b (1 / 2) ∈ c)
    (hmidD : lerp a b (1 / 2) ∈ M.D) (hpos : 0 < ρ * (b.1 - a.1)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset a b (1 / 2) δ ∈ U := by
  have hρρ : ρ * ρ = 1 := by rcases hρ with rfl | rfl <;> norm_num
  refine (eventually_mul_pos (h _ hmid hmidD) hpos).mono fun δ hδ => ?_
  Ξ offset_mid_ab hab
  convert hδ using 3
  linear_combination (-(δ * (b.1 - a.1))) * hρρ

/-! ## Offsets along a chain -/

/-- Offsets of a key outside a closed cyclic arc. -/
theorem off_not_arc {n g a b x : ℝ} (hg : 0 ≤ g) (hgn : g < n) (ha0 : 0 ≤ a) (han : a < n)
    (hb0 : 0 ≤ b) (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) (hab : a ≠ b) (hxa : x ≠ a)
    (hxb : x ≠ b) (h : ¬ sideInArc a b x) :
    (off n g a < off n g b → off n g x < off n g a ∨ off n g b < off n g x) ∧
    (off n g b < off n g a → off n g b < off n g x ∧ off n g x < off n g a) := by
  have hne : ∀ {u w : ℝ}, 0 ≤ u → u < n → 0 ≤ w → w < n → u ≠ w → off n g u ≠ off n g w :=
    fun hu hun hw hwn huw h => huw (off_inj hg hgn hu hun hw hwn h)
  refine ⟨fun hlt => ?_, fun hlt => ?_⟩
  · rw [sideInArc_iff_off hg hgn ha0 han hb0 hbn hx0 hxn hlt] at h
    push Not at h
    have h1 := hne hx0 hxn ha0 han hxa
    have h2 := hne hx0 hxn hb0 hbn hxb
    by_contra hc
    push Not at hc
    exact h2 (le_antisymm hc.2 (h (lt_of_le_of_ne hc.1 (Ne.symm h1))))
  · rw [Chazelle.Chain.sideInArc_swap hab hxa hxb, not_not,
      sideInArc_iff_off hg hgn hb0 hbn ha0 han hx0 hxn hlt] at h
    exact h

/-- **One step along a chain** (arithmetic).  With `θ = 1`, the key `x` is outside the closed
arc from the far end `F` to the near end `N`; with `θ = -1`, outside the arc from `N` to `F`.
If `x` is in the stretch `(0, L)`, the near end is in the stretch and `x` is beyond the far end
(or the far end is outside the stretch), then `x` is beyond the near end. -/
theorem off_step {L oF oN ox θ : ℝ} (hθ : θ = 1 ∨ θ = -1)
    (h1 : θ = 1 → (oF < oN → ox < oF ∨ oN < ox) ∧ (oN < oF → oN < ox ∧ ox < oF))
    (h2 : θ = -1 → (oN < oF → ox < oN ∨ oF < ox) ∧ (oF < oN → oF < ox ∧ ox < oN))
    (hNF : oN ≠ oF) (hx0 : 0 < ox) (hxL : ox < L) (hN0 : 0 < oN) (hNL : oN < L)
    (hpre : 0 < θ * (ox - oF) ∨ L ≤ oF ∨ oF ≤ 0) : 0 < θ * (ox - oN) := by
  rcases hθ with rfl | rfl
  · obtain ⟨h1a, h1b⟩ := h1 rfl
    rcases lt_or_gt_of_ne hNF with h | h
    · have := h1b h
      rcases hpre with hp | hp | hp <;> nlinarith
    · rcases h1a h with h' | h'
      · rcases hpre with hp | hp | hp <;> nlinarith
      · linarith
  · obtain ⟨h2a, h2b⟩ := h2 rfl
    rcases lt_or_gt_of_ne hNF with h | h
    · rcases h2a h with h' | h'
      · linarith
      · rcases hpre with hp | hp | hp <;> nlinarith
    · have := h2b h
      rcases hpre with hp | hp | hp <;> nlinarith

/-! ## Faced sides and middle regions at an attachment -/

/-- The faced side of a chord at an attachment: if the chord goes in direction `dir` from the
point of the position, the side `-dir` is faced just after and the side `dir` just before. -/
def FacedSide (M : Model) (p : ℕ) (t ρ dir : ℝ) (U : Set Point) : Prop :=
  (ρ * dir = -1 → AfterFaces M p t U) ∧ (ρ * dir = 1 → BeforeFaces M p t U)

/-- A point of an attached admissible chord in the domain. -/
theorem exists_mem_dom {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ}
    {t : ℝ} (hA : SideAttach M.W c p t) : ∃ z ∈ c, z ∈ M.D := by
  obtain ⟨e, -, -, hce, hopen, -⟩ := hM.attach_other_end hc hA
  refine ⟨lerp (sidePt M.W p t) e (1 / 2), ?_, hopen _ ⟨⊛, by norm_num⟩⟩
  Ξ hce
  exact Geometry.lerp_mem_segment _ _ (⊛) (by norm_num)

/-- An attached admissible chord is not vertical: it does not lie on both sides of the point of
its attachment. -/
theorem dir_not_both {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ}
    {t : ℝ} (hA : SideAttach M.W c p t) (h1 : ∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1)
    (h2 : ∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1) : False := by
  obtain ⟨w, hwne, hwy, hce, -⟩ := hM.attach_other_end hc hA
  have hw : w ∈ c := by rw [hce]; exact Geometry.right_mem_segment _ _
  exact hwne (Geometry.point_ext (le_antisymm (h2 w hw) (h1 w hw)) hwy)

/-- **The regions at an attachment.**  For a chord `e` of a chord family of a good model,
attached at `(p, t)` and going in direction `dir` from its point, and the region `U` on its side
`ρ`:
* if no other chord of the family is attached there, `U` is faced on the side given by
  `FacedSide`;
* if another chord `e'` is attached there (a tie: `t = 0`), then according to the direction of the
  leaving walk edge either `U` is faced as above, or `U` is the middle region, on the same side of
  `e'` (above both chords when the leaving edge goes down, below both when it goes up). -/
theorem faced_or_middle {M : Model} {Q : Polygon} {F : Set (Set Point)} (hGM : GoodModel M)
    (hFam : M.ChordFamily Q F) {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W e p t) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {U : Set Point}
    (hU : U ∈ M.regions F) (hS : SideOf M ρ e U) {dir : ℝ}
    (hdir : (dir = 1 ∧ ∀ z ∈ e, (sidePt M.W p t).1 ≤ z.1) ∨
      (dir = -1 ∧ ∀ z ∈ e, z.1 ≤ (sidePt M.W p t).1)) :
    ((∀ e' ∈ F, SideAttach M.W e' p t → e' = e) → FacedSide M p t ρ dir U) ∧
    (∀ e' ∈ F, e' ≠ e → SideAttach M.W e' p t → t = 0 ∧ (M.wb p).2 ≠ (M.wa p).2 ∧
      ((M.wb p).2 < (M.wa p).2 → (ρ = 1 → SideOf M ρ e' U) ∧ (ρ = -1 → FacedSide M p t ρ dir U)) ∧
      ((M.wa p).2 < (M.wb p).2 → (ρ = -1 → SideOf M ρ e' U) ∧ (ρ = 1 → FacedSide M p t ρ dir U))) := by
  have hM := walkAx_of_goodModel hGM
  have hF := hFam.2.1
  have hfin : F.Finite := hFam.1
  obtain ⟨z₀, hz₀, hz₀D⟩ := exists_mem_dom hM (hF he) hA
  have hn0 : 0 < M.W.n := by have := hA.1; omega
  refine ⟨fun huniq => ?_, fun e' he' hne hA' => ?_⟩
  · -- a unique attachment: `UpSideSpec`
    obtain ⟨U', V', hU', hV', -, ⟨δ, hδ, hfac⟩, hleft, hright⟩ :=
      upSide M Q F hGM hFam e he p t hA huniq
    have hpt : Geometry.lerp (M.wa p) (M.wb p) t = sidePt M.W p t := rfl
    rw [hpt] at hleft hright
    have hafter : AfterFaces M p t U' := ⟨δ, hδ, fun s h0 h1 h2 =>
      (hfac p (t + s) hA.1 (by linarith [hA.2.1]) h2).1 (Or.inl ⟨by linarith,
        by linarith⟩)⟩
    have hbefore : BeforeFaces M p t V' := by
      refine ⟨min δ 1, lt_min hδ one_pos, fun ht s h0 h1 h2 => ?_, fun ht s h0 h1 => ?_⟩
      · have h1' : s < δ := lt_of_lt_of_le h1 (min_le_left _ _)
        exact (hfac p (t - s) hA.1 (by linarith) (by linarith [hA.2.2.1])).2
          (Or.inl ⟨by linarith, by linarith⟩)
      subst ht
      have h1' : s < δ := lt_of_lt_of_le h1 (min_le_left _ _)
      have h1'' : s < 1 := lt_of_lt_of_le h1 (min_le_right _ _)
      have hs1 : 1 - s < 1 := by linarith
      refine (hfac _ (1 - s) (Nat.mod_lt _ hn0) (by linarith) hs1).2 ?_
      rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · subst hp0
        right
        rw [show (0 + M.W.n - 1) % M.W.n = M.W.n - 1 by
          rw [Nat.mod_eq_of_lt (show 0 + M.W.n - 1 < M.W.n by omega)]; omega,
          Nat.cast_sub (by omega)]
        push_cast
        constructor <;> linarith
      · left
        rw [prev_mod hA.1 hp0, Nat.cast_sub (by omega)]
        push_cast
        constructor <;> linarith
    rcases hdir with ⟨rfl, hd⟩ | ⟨rfl, hd⟩
    · obtain ⟨hb, ha⟩ := hleft hd
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hρ' : ρ = -1 := by linarith
        subst hρ'
        rw [sideOf_eq hU hU' hS (sideOf_neg_one_iff.2 hb) hz₀ hz₀D]; exact hafter
      · have hρ' : ρ = 1 := by linarith
        subst hρ'
        rw [sideOf_eq hU hV' hS (sideOf_one_iff.2 ha) hz₀ hz₀D]; exact hbefore
    · obtain ⟨ha, hb⟩ := hright hd
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hρ' : ρ = 1 := by linarith
        subst hρ'
        rw [sideOf_eq hU hU' hS (sideOf_one_iff.2 ha) hz₀ hz₀D]; exact hafter
      · have hρ' : ρ = -1 := by linarith
        subst hρ'
        rw [sideOf_eq hU hV' hS (sideOf_neg_one_iff.2 hb) hz₀ hz₀D]; exact hbefore
  · -- a tie
    have hne' : e ≠ e' := Ne.symm hne
    have hnot2 : ∀ {c : Set Point}, c ∈ F → SideAttach M.W c p t →
        (∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1) → (∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1) → False :=
      fun hc hAc h1 h2 => dir_not_both hM (hF hc) hAc h1 h2
    obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW, hrole⟩ : ∃ ce cw, ce ∈ F ∧ cw ∈ F ∧
        SideAttach M.W ce p t ∧ SideAttach M.W cw p t ∧
        (∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) ∧ (∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1) ∧
        ((dir = 1 ∧ ce = e ∧ cw = e') ∨ (dir = -1 ∧ cw = e ∧ ce = e')) := by
      rcases hM.tie_pair hF he he' hne' hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨e, e', he, he', hA, hA', h1, h2, Or.inl ⟨?_, rfl, rfl⟩⟩
        rcases hdir with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exact (hnot2 he hA h1 h).elim
      · refine ⟨e', e, he', he, hA', hA, h2, h1, Or.inr ⟨?_, rfl, rfl⟩⟩
        rcases hdir with ⟨-, h⟩ | ⟨h, -⟩
        · exact (hnot2 he hA h h1).elim
        · exact h
    obtain ⟨ht0, hhor, -⟩ := hM.tie_shape hF hce hcw hAe hAw hE hW
    refine ⟨ht0, hhor, fun hdown => ?_, fun hup => ?_⟩
    · obtain ⟨-, U₁, V₁, R, hU₁, hV₁, hR, hbU, hbV, haRe, haRw, ⟨δ₁, hδ₁, hf₁⟩,
        ⟨δ₂, hδ₂, hf₂⟩, -⟩ := hM.tie_down hF hfin hce hcw hAe hAw hE hW hdown
      subst ht0
      refine ⟨fun hρ1 => ?_, fun hρ1 => ?_⟩
      · subst hρ1
        have hUR : U = R := by
          rcases hrole with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
          · exact sideOf_eq hU hR hS (sideOf_one_iff.2 haRe) hz₀ hz₀D
          · exact sideOf_eq hU hR hS (sideOf_one_iff.2 haRw) hz₀ hz₀D
        rw [hUR]
        rcases hrole with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
        · exact sideOf_one_iff.2 haRw
        · exact sideOf_one_iff.2 haRe
      · subst hρ1
        rcases hrole with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
        · refine ⟨fun _ => ?_, fun h => by norm_num at h⟩
          rw [sideOf_eq hU hU₁ hS (sideOf_neg_one_iff.2 hbU) hz₀ hz₀D]
          exact ⟨δ₁, hδ₁, fun s h0 h1 _ => by rw [zero_add]; exact hf₁ s h0 h1⟩
        · refine ⟨fun h => by norm_num at h, fun _ => ?_⟩
          rw [sideOf_eq hU hV₁ hS (sideOf_neg_one_iff.2 hbV) hz₀ hz₀D]
          exact ⟨δ₂, hδ₂, fun h => absurd h (lt_irrefl 0), fun _ s h0 h1 =>
            hf₂ (1 - s) (by linarith) (by linarith)⟩
    · obtain ⟨-, U₁, V₁, R, hU₁, hV₁, hR, haU, haV, hbRe, hbRw, ⟨δ₁, hδ₁, hf₁⟩,
        ⟨δ₂, hδ₂, hf₂⟩, -⟩ := hM.tie_up hF hfin hce hcw hAe hAw hE hW hup
      subst ht0
      refine ⟨fun hρ1 => ?_, fun hρ1 => ?_⟩
      · subst hρ1
        have hUR : U = R := by
          rcases hrole with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
          · exact sideOf_eq hU hR hS (sideOf_neg_one_iff.2 hbRe) hz₀ hz₀D
          · exact sideOf_eq hU hR hS (sideOf_neg_one_iff.2 hbRw) hz₀ hz₀D
        rw [hUR]
        rcases hrole with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
        · exact sideOf_neg_one_iff.2 hbRw
        · exact sideOf_neg_one_iff.2 hbRe
      · subst hρ1
        rcases hrole with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
        · refine ⟨fun h => by norm_num at h, fun _ => ?_⟩
          rw [sideOf_eq hU hV₁ hS (sideOf_one_iff.2 haV) hz₀ hz₀D]
          exact ⟨δ₂, hδ₂, fun h => absurd h (lt_irrefl 0), fun _ s h0 h1 =>
            hf₂ (1 - s) (by linarith) (by linarith)⟩
        · refine ⟨fun _ => ?_, fun h => by norm_num at h⟩
          rw [sideOf_eq hU hU₁ hS (sideOf_one_iff.2 haU) hz₀ hz₀D]
          exact ⟨δ₁, hδ₁, fun s h0 h1 _ => by rw [zero_add]; exact hf₁ s h0 h1⟩

/-! ## Bounds along a chain -/

/-- The positions inside walk edges, not cuts, facing `G`, with offset (from `g`) in `(0, L)`, lie
beyond the offset `o` in the direction `θ`. -/
def Bound (M : Model) (F : Set (Set Point)) (G : Set Point) (g L θ o : ℝ) : Prop :=
  ∀ (p : ℕ) (t : ℝ), p < M.W.n → t ∈ Ioo (0 : ℝ) 1 → ¬ M.IsCut F (p + t) → M.Faces p t G →
    0 < off M.W.n g (p + t) → off M.W.n g (p + t) < L → 0 < θ * (off M.W.n g (p + t) - o)

/-- **The bound across one chord.**  Let `f ∈ F` be attached at a near position `N` and a far
position `Fr` (distinct points), `G` on its side `ρ`, oriented by `θ` (`G` is on the left of `f`
directed from `Fr` to `N` if `θ = 1`, from `N` to `Fr` if `θ = -1`).  If the near offset is in
`(0, L)` and every position facing `G` is beyond the far offset (or the far offset is outside
`(0, L)`), then every position facing `G` is beyond the near offset. -/
theorem chord_bound {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {f : Set Point} (hf : f ∈ F) {pn pf : ℕ} {tn tf : ℝ} (hN : SideAttach M.W f pn tn)
    (hFr : SideAttach M.W f pf tf) (hNF : sidePt M.W pn tn ≠ sidePt M.W pf tf) {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point} (hG : G ∈ M.regions F) (hS : SideOf M ρ f G)
    {θ : ℝ} (hθ : θ = 1 ∨ θ = -1)
    (hori : 0 < θ * ρ * ((sidePt M.W pn tn).1 - (sidePt M.W pf tf).1)) {g L : ℝ}
    (hg0 : 0 ≤ g) (hgn : g < M.W.n) (hN0 : 0 < off M.W.n g (pn + tn))
    (hNL : off M.W.n g (pn + tn) < L)
    (hpre : ∀ (p : ℕ) (t : ℝ), p < M.W.n → t ∈ Ioo (0 : ℝ) 1 → ¬ M.IsCut F (p + t) →
      M.Faces p t G → 0 < off M.W.n g (p + t) → off M.W.n g (p + t) < L →
      0 < θ * (off M.W.n g (p + t) - off M.W.n g (pf + tf)) ∨ L ≤ off M.W.n g (pf + tf) ∨
        off M.W.n g (pf + tf) ≤ 0) :
    Bound M F G g L θ (off M.W.n g (pn + tn)) := by
  intro p t hp ht hnc hfG h0 hL
  obtain ⟨kN0, kNn⟩ := Corr.key_mem hN.1 hN.2.1 hN.2.2.1
  obtain ⟨kF0, kFn⟩ := Corr.key_mem hFr.1 hFr.2.1 hFr.2.2.1
  obtain ⟨kx0, kxn⟩ := Corr.key_mem hp ht.1.le ht.2
  have hkNF : (pn : ℝ) + tn ≠ pf + tf := WalkAx.key_ne_of_pt_ne hN hFr hNF
  have hxN : (p : ℝ) + t ≠ pn + tn := fun h => hnc ⟨f, hf, pn, tn, hN, h⟩
  have hxF : (p : ℝ) + t ≠ pf + tf := fun h => hnc ⟨f, hf, pf, tf, hFr, h⟩
  have hoNF : off M.W.n g (pn + tn) ≠ off M.W.n g (pf + tf) :=
    fun h => hkNF (off_inj hg0 hgn kN0 kNn kF0 kFn h)
  obtain ⟨hfseg, hy, hopen, -, -⟩ := hM.attach_seg (hF hf) hN hFr hNF
  have hmid : lerp (sidePt M.W pn tn) (sidePt M.W pf tf) (1 / 2) ∈ f := by
    rw [hfseg]; exact Geometry.lerp_mem_segment _ _ (⊛) (by norm_num)
  have hmidD := hopen (1 / 2) ⟨⊛, ⊛⟩
  have hsym : lerp (sidePt M.W pf tf) (sidePt M.W pn tn) (1 / 2) =
      lerp (sidePt M.W pn tn) (sidePt M.W pf tf) (1 / 2) := by
    apply Geometry.point_ext <;> simp [Geometry.lerp] <;> ring
  refine off_step hθ (fun hθ1 => ?_) (fun hθ1 => ?_) hoNF h0 hL hN0 hNL
    (hpre p t hp ht hnc hfG h0 hL)
  · subst hθ1
    have hleft := left_of_side hρ hS (a := sidePt M.W pf tf) (b := sidePt M.W pn tn) hy.symm
      (by rw [hsym]; exact hmid) (by rw [hsym]; exact hmidD) (⟡)
    have hnot : ¬ sideInArc (pf + tf) (pn + tn) (p + t) := fun hin =>
      hM.not_left_of_after hF hf hFr hN (Ne.symm hNF) hG hp ht hin hfG hleft
    have := off_not_arc hg0 hgn kF0 kFn kN0 kNn kx0 kxn (Ne.symm hkNF) hxF hxN hnot
    exact this
  · subst hθ1
    have hleft := left_of_side hρ hS (a := sidePt M.W pn tn) (b := sidePt M.W pf tf) hy hmid
      hmidD (⟡)
    have hnot : ¬ sideInArc (pn + tn) (pf + tf) (p + t) := fun hin =>
      hM.not_left_of_after hF hf hN hFr hNF hG hp ht hin hfG hleft
    exact off_not_arc hg0 hgn kN0 kNn kF0 kFn kx0 kxn hkNF hxN hxF hnot

/-! ## Junction facts for the chains -/

section JunctionFacts

variable (J : Merge.Junction)

/-- **`RLabel` from the positions just after a position of the right stretch.** -/
theorem rlabel_after (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {G V : Set Point}
    (hW : AfterFaces (chainModel J.whole)
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t G)
    (hW₂ : AfterFaces (chainModel J.right)
      ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n) t V) :
    RLabel J S₂ G V := by
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨δ, hδ, h1⟩ := hW
  obtain ⟨δ₂, hδ₂, h2⟩ := hW₂
  obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_after hC.hM hC.hF hC.hfin
    ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t)).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min (min δ δ₂) (1 - t) from
      lt_min (lt_min hδ hδ₂) (⟡)))).exists
  have hs1 : s < δ := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : s < δ₂ := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : t + s < 1 := by linarith [lt_of_lt_of_le hs.2 (min_le_right _ _)]
  refine ⟨d, hd, t + s, ⟨by linarith [hs.1], hs3⟩, ?_, h1 s hs.1 hs1 hs3, h2 s hs.1 hs2 hs3⟩
  rw [← add_assoc]; exact hnc

/-- **`RLabel` from the positions just before a position of the right stretch.** -/
theorem rlabel_before (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J) {G V : Set Point}
    (hW : BeforeFaces (chainModel J.whole)
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t G)
    (hW₂ : BeforeFaces (chainModel J.right)
      ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n) t V) :
    RLabel J S₂ G V := by
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨δ, hδ, h1a, h1b⟩ := hW
  obtain ⟨δ₂, hδ₂, h2a, h2b⟩ := hW₂
  rcases ht0.lt_or_eq with htpos | ht00
  · obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
      ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min (min δ δ₂) t from
        lt_min (lt_min hδ hδ₂) htpos))).exists
    have hs1 : s < δ := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_left _ _))
    have hs2 : s < δ₂ := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_right _ _))
    have hs3 : s < t := lt_of_lt_of_le hs.2 (min_le_right _ _)
    refine ⟨d, hd, t - s, ⟨by linarith, by linarith [hs.1]⟩, ?_, h1a htpos s hs.1 hs1 hs3,
      h2a htpos s hs.1 hs2 hs3⟩
    rw [show ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + (t - s)) =
      (((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t - s by ring]
    exact hnc
  · subst ht00
    obtain ⟨hd0, -⟩ := hsec rfl
    have hn0 := hC.n_pos
    have hn₂ := hC.n₂_pos
    set P := (6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n with hPdef
    set P' := (P + (chainModel J.whole).W.n - 1) % (chainModel J.whole).W.n with hP'def
    have hPm : (6 + tpos J.whole J.m₁ + (d - 1)) % (chainModel J.whole).W.n = P' := by
      rw [hP'def, hPdef, mod_pred_mod hn0 _ (show 1 ≤ d by omega)]
    have hdq0 : 1 ≤ dq (rL1 J) (rδ J) d := by unfold dq; split_ifs <;> omega
    have hdq1 : dq (rL1 J) (rδ J) (d - 1) = dq (rL1 J) (rδ J) d - 1 := by
      have := (hsec rfl).2; unfold dq; split_ifs <;> omega
    have hPm₂ : (6 + tpos J.right 0 + dq (rL1 J) (rδ J) (d - 1)) % (chainModel J.right).W.n =
        ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n +
          (chainModel J.right).W.n - 1) % (chainModel J.right).W.n := by
      rw [hdq1, mod_pred_mod hn₂ _ hdq0]
    obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
      (((P' : ℕ) : ℝ) + 1)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min (min δ δ₂) 1 from
        lt_min (lt_min hδ hδ₂) one_pos))).exists
    have hs1 : s < δ := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_left _ _))
    have hs2 : s < δ₂ := lt_of_lt_of_le hs.2 ((min_le_left _ _).trans (min_le_right _ _))
    have hs3 : s < 1 := lt_of_lt_of_le hs.2 (min_le_right _ _)
    refine ⟨d - 1, by omega, 1 - s, ⟨by linarith, by linarith [hs.1]⟩, ?_, ?_, ?_⟩
    · rw [hPm, show ((P' : ℕ) : ℝ) + (1 - s) = ((P' : ℕ) : ℝ) + 1 - s by ring]; exact hnc
    · rw [hPm]; exact h1b rfl s hs.1 hs1
    · rw [hPm₂]; exact h2b rfl s hs.1 hs2

/-- **The shared vertex is outside the right stretch** (in offsets). -/
theorem off_shared_out (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ}
    (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hv : sidePt (chainModel J.whole).W p t = J.shared) :
    ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) <
        ((rL1 J + rL2 J : ℕ) : ℝ)) := by
  rintro ⟨h0, hL⟩
  have hC := corr_right0 J hP hS₂ hS₂f
  obtain ⟨hpd, hoff⟩ := hC.decomp hp ht0 ht1
  set d := dOf (chainModel J.whole).W.n (6 + tpos J.whole J.m₁) p with hddef
  rw [hoff] at h0 hL
  have hdL : d < rL1 J + rL2 J := by
    have : (d : ℝ) < ((rL1 J + rL2 J : ℕ) : ℝ) := ⟡
    exact_mod_cast this
  have hpt := hC.sidePt_eq hdL t
  rw [hpd] at hpt
  rw [hpt] at hv
  apply hC.noV _ (Nat.mod_lt _ hC.n₂_pos) t ht0 ht1
  · Ξ hC.off_M₂ hdL ht0 ht1
    have : d ≤ dq (rL1 J) (rδ J) d := by unfold dq; split_ifs <;> omega
    have : (d : ℝ) ≤ dq (rL1 J) (rδ J) d := by exact_mod_cast this
    linarith
  · Ξ hC.off_M₂ hdL ht0 ht1
    have h1 : dq (rL1 J) (rδ J) d + 1 ≤ rL1 J + rδ J + rL2 J := by
      have := hC.dq_lt hdL; have := hC.hL₂; unfold dq at *; split_ifs at * <;> omega
    have h2 : ((dq (rL1 J) (rδ J) d : ℕ) : ℝ) + 1 ≤ ((rL1 J + rδ J + rL2 J : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2 ⊢
    linarith
  · rw [hv]; exact (right_vtx0 J).symm

/-- A point of a segment off a set containing its open part, other than its start, is its end. -/
theorem seg_end {D : Set Point} {a b z : Point} (hz : z ∈ Chazelle.segment a b) (hzD : z ∉ D)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ D) (hza : z ≠ a) : z = b := by
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
  rcases hs0.lt_or_eq with hs0 | hs0
  · rcases hs1.lt_or_eq with hs1 | hs1
    · exact absurd (hopen s ⟨hs0, hs1⟩) hzD
    · Ξ hs1, Geometry.lerp_one
  · exact absurd (Ρ ← hs0, Geometry.lerp_zero) hza

/-- Two chords of `S₂` containing one chord of `F₂⁺` are equal. -/
theorem s2_eq_of_sub {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {c c' e : Set Point} (hc : c ∈ S₂) (hc' : c' ∈ S₂) (he : e ∈ Merge.augChords J.whole)
    (hec : e ⊆ c) (hec' : e ⊆ c') : c = c' := by
  obtain ⟨y₁, a₁, b₁, hH₁, -, rfl⟩ := he
  obtain ⟨y, a, b, hH, -, hcdef, -, -⟩ := Merge.augChords_spec (hS₂ hc)
  obtain ⟨y', a', b', hH', -, hc'def, -, -⟩ := Merge.augChords_spec (hS₂ hc')
  have hab := hH₁.lt
  have hm : (((a₁ + b₁) / 2, y₁) : Point) ∈ Visibility.hseg y₁ a₁ b₁ :=
    ⟨rfl, by simp only; linarith, by simp only; linarith⟩
  have hmc := hec hm
  have hmc' := hec' hm
  rw [hcdef] at hmc hec ⊢
  rw [hc'def] at hmc' hec' ⊢
  have hl := hec (show ((a₁, y₁) : Point) ∈ Visibility.hseg y₁ a₁ b₁ from ⟨rfl, le_rfl, hab.le⟩)
  have hr := hec (show ((b₁, y₁) : Point) ∈ Visibility.hseg y₁ a₁ b₁ from ⟨rfl, hab.le, le_rfl⟩)
  rcases Chain.hchordIn_inter hH hH' hmc hmc' with ⟨rfl, rfl, rfl⟩ | ⟨h1, -⟩
  · rfl
  · exfalso
    obtain ⟨-, hl1, -⟩ := hl
    obtain ⟨-, -, hr1⟩ := hr
    simp only at hl1 hr1
    rcases h1 with h1 | h1 <;> have := congrArg Prod.fst h1 <;> simp only at this <;> linarith

end JunctionFacts

/-! ## The local step at a position of the right stretch -/

section Local

variable (J : Merge.Junction)

end Local

/-! ## Walking along a chain -/

section Walk

variable (J : Merge.Junction)

/-- The chords of `F` with a point beyond `q` in the direction of decreasing `κ x`. -/
def beyond (F : Set (Set Point)) (κ : ℝ) (q : Point) : Set (Set Point) :=
  {h | h ∈ F ∧ ∃ z ∈ h, 0 < κ * (q.1 - z.1)}

/-- Opposite directions of the two chords of a tie. -/
theorem tie_opposite {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {f f' : Set Point} (hf : f ∈ F) (hf' : f' ∈ F) (hne : f' ≠ f) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W f p t) (hA' : SideAttach M.W f' p t) {a b : Point} (ha : a ∈ f)
    (hb : b ∈ f') (ha1 : a.1 ≠ (sidePt M.W p t).1) (hb1 : b.1 ≠ (sidePt M.W p t).1) :
    (a.1 - (sidePt M.W p t).1) * (b.1 - (sidePt M.W p t).1) < 0 := by
  rcases hM.attach_dir (hF hf) hA with h | h <;> rcases hM.attach_dir (hF hf') hA' with h' | h'
  · exact absurd (hM.attach_east_unique hF hf' hf hA' hA h' h) hne
  · have := lt_of_le_of_ne (h a ha) (Ne.symm ha1)
    have := lt_of_le_of_ne (h' b hb) hb1
    nlinarith
  · have := lt_of_le_of_ne (h a ha) ha1
    have := lt_of_le_of_ne (h' b hb) (Ne.symm hb1)
    nlinarith
  · exact absurd (hM.attach_west_unique hF hf' hf hA' hA h' h) hne

/-- A sign making a nonzero quantity positive. -/
theorem exists_sign {ρ r : ℝ} (hρ : ρ = 1 ∨ ρ = -1) (hr : r ≠ 0) :
    ∃ θ : ℝ, (θ = 1 ∨ θ = -1) ∧ 0 < θ * ρ * r := by
  rcases lt_or_gt_of_ne hr with h | h <;> rcases hρ with rfl | rfl
  · exact ⟨-1, Or.inr rfl, ⟡⟩
  · exact ⟨1, Or.inl rfl, ⟡⟩
  · exact ⟨1, Or.inl rfl, ⟡⟩
  · exact ⟨-1, Or.inr rfl, ⟡⟩

end Walk

end Sweep
