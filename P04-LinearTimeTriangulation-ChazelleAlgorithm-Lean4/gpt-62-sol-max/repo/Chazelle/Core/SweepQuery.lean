module

public import Chazelle.Core.SweepLabelJG

/-!
# The sweep (WP-D), part 6: queries (lemma (Q))

A query point `z` of the sweep (on the walk of `C₁`) whose ray, in the model of `C = J.whole`,
starts in the region `G` of `F₂⁺` and first hits `C` at a point `w` of `C₂` (not of `C₁`): then
the ray starts in a region `V` of `S₂` (in the model of `C₂`) and `V` is the label of `G`
(`RLabel`).  With lemma (K) (`label_right`) the label of `G` is unique, so the sweep, which knows
the label of the current region, answers the query by local shooting in `V` (and in the region of
`S₁` of the query, `SweepAnswer`).

## Generic part

* `approach_edge`, `approach_vertex`: a ray approaching a walk position from inside its left
  sector, inside a region `U`: the position is not a cut and faces `U` (inside a walk edge), or
  the positions just after / just before face `U` (at a walk vertex; when a chord is attached
  there, on the side given by the direction of the ray).  These are the facing statements from
  `SweepLocal`, used so that they can be used in two models with the same walk locally.
* `Corr.sideNext_eq`, `Corr.sidePrev_eq`, `Corr.sideLeft_eq`: the correspondence preserves
  sectors.

## The junction

* `pos_tour_of_mem_set`, `right_cover₂`, `right_vtx0`, `right_split_top`, `dom_right`,
  `dom_left`: bookkeeping.
* `query_right`: **lemma (Q)**.
* `answer_of_label`: **answering a query below both tops from its region of `S₁` and the label
  of its region of `F₂⁺`** (first hit on the arcs of the two regions = first hit of `C`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn sideLeft_edge sideLeft_zero sideLeft_not_self sideKey_inj
  sideCcw_smul)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset SectorSide)
open WalkEmbed

namespace Sweep

/-! ## Approaching a walk position -/

section Approach

variable {M : Model}

/-- **A ray approaching a walk vertex**: if no chord is attached there, the positions just after
and just before face the region of the ray; if a chord is attached there, the ray turns
counterclockwise from the next walk edge or clockwise from the previous one, and the positions
on that side face the region of the ray. -/
theorem approach_vertex (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n) (hp1 : 1 ≤ p) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1)
    (hsec : ∀ s > 0, sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ s))
    (happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∈ U) :
    (¬ M.IsCut F ((p : ℝ) + 0) → (∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces (p - 1) (1 - s) U) ∧
    (M.IsCut F ((p : ℝ) + 0) →
      (0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((τ, 0) : Point) ∨
        0 < sideCross ((τ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p)) ∧
      (0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((τ, 0) : Point) →
        ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) ∧
      (0 < sideCross ((τ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p) →
        ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces (p - 1) (1 - s) U)) := by
  simpa only [prev_mod hp hp1] using approach_vertex_cyclic hM hF hfin hU hp hτ hsec happ

end Approach

/-! ## Non-cut keys near a key -/

/-! ## Two walks along a correspondence: sectors -/

namespace Corr

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

end Corr

namespace Corr0

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

section

variable (hC : Corr0 M M₂ F S g g' L1 L2 δ) {d : ℕ} (hd : d < L1 + L2)
include hC hd

/-- Agreeing next points. -/
theorem sideNext_eq :
    sideNext M.W ((g + d) % M.W.n) = sideNext M₂.W ((g' + dq L1 δ d) % M₂.W.n) := by
  unfold dq
  split_ifs with h
  · exact hC.A1.sideNext_eq h
  · have := hC.A2.sideNext_eq (d := d - L1) (by omega)
    rwa [show g + L1 + (d - L1) = g + d by omega,
      show g' + L1 + δ + (d - L1) = g' + (d + δ) by omega] at this

/-- Agreeing previous points (away from the base and the split vertex). -/
theorem sidePrev_eq {t : ℝ}
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ L1) :
    sidePrev M.W ((g + d) % M.W.n) t = sidePrev M₂.W ((g' + dq L1 δ d) % M₂.W.n) t := by
  unfold dq
  split_ifs with h
  · exact hC.A1.sidePrev_eq hC.n_pos hC.n₂_pos h (fun h0 => by have := (hsec h0).1; omega)
  · have := hC.A2.sidePrev_eq hC.n_pos hC.n₂_pos (d := d - L1) (by omega) (t := t)
      (fun h0 => by have := (hsec h0).2; omega)
    rwa [show g + L1 + (d - L1) = g + d by omega,
      show g' + L1 + δ + (d - L1) = g' + (d + δ) by omega] at this

/-- Agreeing left sectors (away from the base and the split vertex). -/
theorem sideLeft_eq {t : ℝ}
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ L1) :
    sideLeft M.W ((g + d) % M.W.n) t = sideLeft M₂.W ((g' + dq L1 δ d) % M₂.W.n) t := by
  funext x
  unfold sideLeft
  rw [hC.sidePrev_eq hd hsec, hC.sidePt_eq hd, hC.sideNext_eq hd]

end

end Corr0

/-! ## Chain facts for the queries -/

/-- A position of the walk of a chain model whose point is a point of the chain other than its
top is a position of the tour, before its last vertex. -/
theorem pos_tour_of_mem_set (C : Chain) (β : Bool) {p : ℕ} (hp : p < (C.sideWalk β).n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (h : sidePt (C.sideWalk β) p t ∈ C.set)
    (hne : sidePt (C.sideWalk β) p t ≠ C.top) : ∃ i, i < 2 * C.m ∧ p = i + 6 := by
  have hb := C.abs_le_coordBound_of_mem_set h
  have hcb := C.coordBound_lt_radius
  have htop := C.snd_le_top_of_mem_set h
  have htopR := C.top_snd_lt_radius
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := C.sidePt_box β t
  rcases C.sideWalk_pos_cases β hp ht with (hp5 | ⟨rfl, htp⟩) | ⟨i, hi, rfl, hit⟩
  · exfalso
    interval_cases p
    · rw [h0] at hb; simp only at hb; have := (abs_le.1 hb.2).2; linarith
    · rw [h1] at hb; simp only at hb; have := (abs_le.1 hb.1).1; linarith
    · rw [h2] at hb; simp only at hb; have := (abs_le.1 hb.2).1; linarith
    · rw [h3] at hb; simp only at hb; have := (abs_le.1 hb.1).2; linarith
    · rw [h4] at hb; simp only at hb; have := (abs_le.1 hb.2).2; linarith
    · rw [h5] at htop; simp only at htop; nlinarith
  · exfalso
    rw [h6] at htop; simp only at htop; nlinarith
  · refine ⟨i, ?_, rfl⟩
    rcases lt_or_eq_of_le hi with hi | rfl
    · exact hi
    simp_all

/-- A horizontal subchord through an endpoint of a horizontal chord contains the start of the
ray from that endpoint along the chord. -/
theorem ray_sub_hseg {y a b y' a' b' : ℝ} (hab' : a' < b')
    (hsub : Visibility.hseg y' a' b' ⊆ Visibility.hseg y a b) {w : Point}
    (hw : w ∈ Visibility.hseg y' a' b') (hwend : w = (a, y) ∨ w = (b, y)) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) :
    ∃ ε > 0, ∀ s, 0 < s → s < ε → rayPt w τ s ∈ Visibility.hseg y a b →
      rayPt w τ s ∈ Visibility.hseg y' a' b' := by
  obtain ⟨hwy, hwa, hwb⟩ := hw
  obtain ⟨hy1, ha1, hb1⟩ : ((a', y') : Point) ∈ Visibility.hseg y a b :=
    hsub ⟨rfl, le_rfl, hab'.le⟩
  obtain ⟨hy2, ha2, hb2⟩ : ((b', y') : Point) ∈ Visibility.hseg y a b :=
    hsub ⟨rfl, hab'.le, le_rfl⟩
  simp only at hy1 ha1 hb1 hy2 ha2 hb2
  rcases hτ with rfl | rfl <;> rcases hwend with rfl | rfl <;> simp only at hwy hwa hwb
  · refine ⟨b' - a, by linarith, fun s hs0 hs1 _ => ⟨?_, ?_, ?_⟩⟩ <;>
      simp only [rayPt_fst, rayPt_snd] <;> linarith
  · refine ⟨1, one_pos, fun s hs0 _ hc => ?_⟩
    exfalso
    obtain ⟨-, -, h⟩ := hc
    simp only [rayPt_fst] at h
    linarith
  · refine ⟨1, one_pos, fun s hs0 _ hc => ?_⟩
    exfalso
    obtain ⟨-, h, -⟩ := hc
    simp only [rayPt_fst] at h
    linarith
  · refine ⟨b - a', by linarith, fun s hs0 hs1 _ => ⟨?_, ?_, ?_⟩⟩ <;>
      simp only [rayPt_fst, rayPt_snd] <;> linarith

section Junction

variable (J : Merge.Junction)

/-- Points of the domain of `C` not above the top of `C₂` are in the domain of `C₂`. -/
theorem dom_right {x : Point} (hx : x ∈ J.whole.dom) (hx2 : x.2 ≤ J.right.top.2) :
    x ∈ J.right.dom := by
  by_contra h
  rcases (Merge.not_mem_dom_iff J.right hx2).1 h with h1 | h1
  · apply h1
    rw [FuseMath.radius_of_P J (C' := J.right) rfl]
    exact J.whole.dom_subset_box hx
  · exact J.whole.not_mem_set_of_mem_dom hx (J.right_set_subset h1)

/-- The base of the walk of `C₂` is the shared vertex. -/
theorem right_vtx0 : J.rightModel.W.vtx (6 + tpos J.right 0) = J.shared := by
  have hn₂ := cm_n J.right
  have hτ := tpos_lt J.right 0
  have := walk_tour J.right 0 0 (by omega)
  rwa [add_zero, Nat.mod_eq_of_lt (by rw [hn₂]; omega), tourV_right_zero] at this

/-- In case G, the vertex after the gap is the top of `C₂`. -/
theorem right_split_top (h : 0 < rδ J) :
    J.rightModel.W.vtx ((6 + tpos J.right 0 + (rL1 J + rδ J)) %
      J.rightModel.W.n) = J.right.top := by
  
  have e : rL1 J + rδ J = 2 * J.right.m - tpos J.right 0 + 7 := by
    unfold rL1 rδ at *
    split_ifs at h ⊢ <;> omega
  rw [e, show 6 + tpos J.right 0 + (2 * J.right.m - tpos J.right 0 + 7) =
    6 + tpos J.right 0 + (2 * J.right.m - tpos J.right 0) + 7 by omega]
  exact walk_box J.right 0 7 le_rfl

/-- **Every tour position of `C₂` (before its last vertex) is covered by the correspondence.** -/
theorem right_cover₂ {i : ℕ} (hi : i < 2 * J.right.m) :
    ∃ d < rL1 J + rL2 J, dq (rL1 J) (rδ J) d =
      dOf J.rightModel.W.n (6 + tpos J.right 0) (6 + i) := by
  have hτ' := tpos_lt J.right 0
  have hn₂ := cm_n J.right
  have hm2 : J.right.m = J.m₂ := rfl
  rw [hn₂, FuseMath.dOf_six (by omega) (by omega)]
  refine ⟨if (if tpos J.right 0 ≤ i then i - tpos J.right 0
      else i + (2 * J.right.m + 7) - tpos J.right 0) < rL1 J
    then (if tpos J.right 0 ≤ i then i - tpos J.right 0
      else i + (2 * J.right.m + 7) - tpos J.right 0)
    else (if tpos J.right 0 ≤ i then i - tpos J.right 0
      else i + (2 * J.right.m + 7) - tpos J.right 0) - rδ J, ?_, ?_⟩ <;>
  · simp only [rL1, rL2, rδ, dq]
    split_ifs <;> omega

end Junction

/-! ## Lemma (Q) -/

section Query

variable (J : Merge.Junction)

/-- **Lemma (Q): a query sees `C₂` from the label of its region.**  Let the initial part of the
horizontal ray from `z` (not above the top of `C₂`) lie in the region `G` of `F₂⁺` (model of `C`),
and let the first hit of the ray in `C` be a point of `C₂` not on `C₁`.  Then the initial part of
the ray lies in a region `V` of `S₂` (model of `C₂`), and `V` is a label of `G`. -/
theorem query_right (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂)) {z : Point}
    (hz : z.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hini : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ G)
    (hw2 : rayPt z σ (J.whole.hitParam z σ) ∈ J.right.set)
    (hw1 : rayPt z σ (J.whole.hitParam z σ) ∉ J.left.set) :
    ∃ V ∈ J.rightModel.regions S₂, (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ V) ∧
      RLabel J S₂ G V := by
  have hCorr := corr_right0 J hP hS₂ hS₂f
  have hM := hCorr.hM
  have hM₂ := hCorr.hM₂
  have hFs : F₂plus J S₂ ⊆ Merge.augChords J.whole := F₂plus_subset J hS₂
  have hFf : (F₂plus J S₂).Finite := F₂plus_finite J hS₂f
  have hGd : G ∈ regionsIn J.whole.dom (F₂plus J S₂) := hG
  have hGfree : G ⊆ freeIn J.whole.dom (F₂plus J S₂) := Chazelle.Chain.regionsIn_subset hGd
  have hfree : Merge.FreeAt J.whole z σ := hini.mono fun t ht => (hGfree ht).1
  have hz' : z.2 ≤ J.whole.top.2 := hz.trans J.right_top_le
  obtain ⟨hT, hwD, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
  set T := J.whole.hitParam z σ with hTdef
  set w := rayPt z σ T with hwdef
  have hray := ray_subset_region J.whole hFs hGd hσ hT hdom hini
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hback : ∀ s, rayPt w (-σ) s = rayPt z σ (T - s) := by
    intro s; apply point_ext <;> simp [rayPt, hwdef]; ring
  have hwy : w.2 = z.2 := by simp [hwdef, rayPt]
  have hbackG : ∀ s, 0 < s → s < T → rayPt w (-σ) s ∈ G := fun s h0 h1 => by
    simp_all  
  have happG : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ G := by
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    exact hbackG s hs.1 hs.2
  have hbackD : ∀ s, 0 < s → s < T → rayPt w (-σ) s ∈ J.right.dom := fun s h0 h1 => by
    refine dom_right J ?_ ?_
    · rw [hback]; exact hdom _ (by linarith) (by linarith)
    assumption
  -- the hit point is neither the shared vertex nor the top of `C₂`
  have hwv : w ≠ J.shared := fun h => hw1 (h ▸ J.shared_mem_left)
  have hwt : w ≠ J.right.top := by
    intro hwt
    have hkt : J.m₁ + J.right.topIdx ≤ J.whole.m := by
      have := J.right.topIdx_le
      simp only [Merge.Junction.whole_m, Merge.Junction.right_m] at this ⊢
      omega
    have hvert : J.whole.vertex (J.m₁ + J.right.topIdx) = J.right.top :=
      Merge.Junction.whole_vertex_add J _
    have hdf : J.whole.DirFree (J.m₁ + J.right.topIdx) (-σ) := by
      unfold Chain.DirFree
      filter_upwards [Ioo_mem_nhdsGT hT] with s hs
      rw [hvert, ← hwt, hback]
      exact hdom _ (by linarith [hs.2]) (by linarith [hs.1])
    have he : J.whole.chordSet (J.m₁ + J.right.topIdx) (-σ) ∈ F₂plus J S₂ :=
      Or.inr ⟨-σ, hnσ, hdf, rfl⟩
    obtain ⟨hpar, -, -⟩ := Merge.hit_of_freeAt J.whole (J.whole.vertex_snd_le_top hkt) hnσ hdf
    have hpar' : 0 < J.whole.chordParam (J.m₁ + J.right.topIdx) (-σ) := hpar
    set s := min (T / 2) (J.whole.chordParam (J.m₁ + J.right.topIdx) (-σ) / 2) with hs
    have hs0 : 0 < s := lt_min (by linarith) (by linarith)
    have hsT : s < T := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsP : s < J.whole.chordParam (J.m₁ + J.right.topIdx) (-σ) :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hmem : rayPt w (-σ) s ∈ J.whole.chordSet (J.m₁ + J.right.topIdx) (-σ) := by
      rw [J.whole.chordSet_eq_openChordSet_union hkt hnσ hdf]
      left
      refine ⟨s, ⟨hs0, hsP⟩, ?_⟩
      rw [hvert, ← hwt]
    exact (hGfree (hbackG s hs0 hsT)).2 ⟨_, he, hmem⟩
  -- a position of the walk of `C₂` at the hit point, whose sector contains the backward ray
  have hT2' : (0 : ℝ) < T / 2 := by linarith
  have hee : w ≠ rayPt w (-σ) (T / 2) := by
    intro h
    have := congrArg Prod.fst h
    simp only [rayPt_fst] at this
    rcases hσ with rfl | rfl <;> linarith
  have hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w (rayPt w (-σ) (T / 2)) s ∈ J.right.dom := by
    intro s hs
    have e : lerp w (rayPt w (-σ) (T / 2)) s = rayPt w (-σ) (s * (T / 2)) := by
      apply point_ext <;> simp [lerp, rayPt]; ring
    rw [e]
    exact hbackD _ (by nlinarith [hs.1]) (by nlinarith [hs.2])
  have hP₂ : J.right.P.Simple := hP
  obtain ⟨p₂, t₂, hp₂, ht₂, ht₂1, hpt₂, hl₂⟩ :=
    J.right.sideSees_chordEnd hP₂ J.right.sideBeta hee (by simp [rayPt]) hopen (Or.inl hw2)
  obtain ⟨i, hi, rfl⟩ := pos_tour_of_mem_set J.right J.right.sideBeta hp₂ ht₂ ht₂1
    (by rwa [hpt₂]) (by rwa [hpt₂])
  -- the corresponding position of the walk of `C`
  obtain ⟨d, hd, hdq⟩ := right_cover₂ J hi
  have hn₂ := cm_n J.right
  
  have hg' : 6 + tpos J.right 0 < J.rightModel.W.n := hCorr.hg'
  have hpos₂ : (6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % J.rightModel.W.n = i + 6 := by
    rw [hdq, show i + 6 = 6 + i by ring]
    exact add_dOf hg' (by rw [hn₂]; omega)
  have hpt₂' : sidePt J.rightModel.W (i + 6) t₂ = w := hpt₂
  set P := (6 + tpos J.whole J.m₁ + d) % J.wholeModel.W.n with hPdef
  have hPn : P < J.wholeModel.W.n := Nat.mod_lt _ hCorr.n_pos
  have hptW : sidePt J.wholeModel.W P t₂ = w := by
    rwa [hPdef, hCorr.sidePt_eq hd t₂, hpos₂]
  have hL1pos : 0 < rL1 J := by
    have := tpos_lt J.right 0
    have hm2 : J.right.m = J.m₂ := rfl
    have := J.one_le_m₂
    unfold rL1; split_ifs <;> omega
  have hsecd : t₂ = 0 → d ≠ 0 ∧ d ≠ rL1 J := by
    intro h0
    refine ⟨fun hd0 => hwv ?_, fun hdL => hwt ?_⟩
    · rw [← hpt₂', h0, Chazelle.Chain.sidePt_zero, ← hpos₂, hd0,
        show dq (rL1 J) (rδ J) 0 = 0 by unfold dq; split_ifs; omega, add_zero,
        Nat.mod_eq_of_lt hg']
      exact right_vtx0 J
    · have hδ : 0 < rδ J := by
        by_contra hδ0
        have := hCorr.hδ (by omega)
        omega
      rw [← hpt₂', h0, Chazelle.Chain.sidePt_zero, ← hpos₂, hdL,
        show dq (rL1 J) (rδ J) (rL1 J) = rL1 J + rδ J by simp [dq]]
      exact right_split_top J hδ
  have hsecEq : sideLeft J.wholeModel.W P t₂ =
      sideLeft J.rightModel.W (i + 6) t₂ := by
    rw [hPdef, hCorr.sideLeft_eq hd hsecd, hpos₂]
  have hsec₂ : ∀ s > 0, sideLeft J.rightModel.W (i + 6) t₂
      (rayPt (sidePt J.rightModel.W (i + 6) t₂) (-σ) s) := by
    intro s hs
    have hl' : sideLeft J.rightModel.W (i + 6) t₂
        (rayPt (sidePt J.rightModel.W (i + 6) t₂) (-σ) (T / 2)) := by
      rwa [hpt₂']
    exact (sideLeft_rayPt_iff _ _ t₂ (-σ) hT2' hs).1 hl'
  have hsecW : ∀ s > 0, sideLeft J.wholeModel.W P t₂
      (rayPt (sidePt J.wholeModel.W P t₂) (-σ) s) := by
    simp only [hsecEq, hptW, ← hpt₂'] <;> omega
  have happW : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      rayPt (sidePt J.wholeModel.W P t₂) (-σ) s ∈ G := by
    rwa [hptW]
  -- the region of `S₂` of the backward ray
  have hnearS : ∀ c ∈ S₂, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∉ c := by
    intro c hc
    obtain ⟨hL, hR⟩ := J.end_mem_fusion hP (empty_subset _) hS₂ (Or.inr hc)
    obtain ⟨y, a, b, hH, -, rfl, hl, hr⟩ := Merge.augChords_spec (hS₂ hc)
    by_cases hwc : w ∈ Visibility.hseg y a b
    · have hwD₂ : w ∉ J.right.dom := fun h => J.right.not_mem_set_of_mem_dom h hw2
      have hwend : w = (a, y) ∨ w = (b, y) := by
        obtain ⟨hq2, hqa, hqb⟩ := hwc
        rcases hqa.lt_or_eq with h1 | h1
        · rcases hqb.lt_or_eq with h2 | h2
          · exact absurd (show w ∈ J.right.dom by
              rw [show w = (w.1, y) from Prod.ext rfl hq2]
              exact hH.open_mem w.1 h1 h2) hwD₂
          · right; exact Prod.ext h2 hq2
        · left; exact Prod.ext h1.symm hq2
      obtain ⟨e, he, hwe, hec⟩ : ∃ e ∈ J.fusion ∅ S₂, w ∈ e ∧ e ⊆ Visibility.hseg y a b := by
        rcases hwend with h | h
        · have hlw : Merge.lend (Visibility.hseg y a b) = w := by rw [hl, h]
          rw [hlw] at hL
          exact hL hwv
        · have hrw : Merge.rend (Visibility.hseg y a b) = w := by rw [hr, h]
          rw [hrw] at hR
          exact hR hwv
      obtain ⟨y', a', b', hH', -, rfl⟩ := F₂plus_subset J hS₂ (Or.inl he)
      obtain ⟨ε, hε, hsub⟩ := ray_sub_hseg hH'.lt hec hwe hwend hnσ
      filter_upwards [Ioo_mem_nhdsGT (lt_min hε hT)] with s hs hsc
      have hsε : s < ε := lt_of_lt_of_le hs.2 (min_le_left _ _)
      have hsT : s < T := lt_of_lt_of_le hs.2 (min_le_right _ _)
      exact (hGfree (hbackG s hs.1 hsT)).2 ⟨_, Or.inl he, hsub s hs.1 hsε hsc⟩
    · have hcont : Tendsto (fun s => rayPt w (-σ) s) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
        have := ((Chazelle.Visibility.continuous_rayPt w (-σ)).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        rwa [Chazelle.Visibility.rayPt_zero] at this
      exact hcont ((Chazelle.Chain.isClosed_hseg y a b).isOpen_compl.mem_nhds hwc)
  have hfreeS₂ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ freeIn J.right.dom S₂ := by
    have hall := (hS₂f.eventually_all (p := fun c s => rayPt w (-σ) s ∉ c)).2 hnearS
    filter_upwards [hall, Ioo_mem_nhdsGT hT] with s hs hsT
    refine ⟨hbackD s hsT.1 hsT.2, ?_⟩
    rintro ⟨c, hc, hxc⟩
    exact hs c hc hxc
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hfreeS₂
  have hε₀' : (0 : ℝ) < ε₀ := hε₀
  have hx₀ : rayPt w (-σ) (ε₀ / 2) ∈ freeIn J.right.dom S₂ :=
    hε₀sub ⟨by linarith, by linarith⟩
  set V := connectedComponentIn (freeIn J.right.dom S₂) (rayPt w (-σ) (ε₀ / 2)) with hVdef
  have hV : V ∈ J.rightModel.regions S₂ := Chazelle.Chain.mem_regionsIn hx₀
  have hsubV : rayPt w (-σ) '' Ioo 0 ε₀ ⊆ V := by
    refine subset_region hV (isPreconnected_Ioo.image _
      (Chazelle.Visibility.continuous_rayPt w (-σ)).continuousOn) ?_
      ⟨ε₀ / 2, ⟨by linarith, by linarith⟩, rfl⟩ (mem_connectedComponentIn hx₀)
    rintro _ ⟨s, hs, rfl⟩
    exact hε₀sub hs
  have happV : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ V := by
    filter_upwards [Ioo_mem_nhdsGT hε₀'] with s hs
    exact hsubV ⟨s, hs, rfl⟩
  have hzV : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ V := by
    have hall := ray_subset_region J.right hS₂ hV hnσ hT hbackD happV
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    have := hall (T - s) (by linarith [hs.2]) (by linarith [hs.1])
    rwa [hback, show T - (T - s) = s by ring] at this
  refine ⟨V, hV, hzV, ?_⟩
  have happV' : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      rayPt (sidePt J.rightModel.W (i + 6) t₂) (-σ) s ∈ V := by
    rwa [hpt₂']
  have hFs' : F₂plus J S₂ ⊆ J.wholeModel.Adm := hFs
  have hS₂' : S₂ ⊆ J.rightModel.Adm := hS₂
  rcases ht₂.lt_or_eq with htpos | ht0
  · -- inside a walk edge: the position itself
    have ht' : t₂ ∈ Ioo (0 : ℝ) 1 := ⟨htpos, ht₂1⟩
    obtain ⟨hcutW, hfW⟩ := approach_edge hM hFs' hFf hG hPn ht' hnσ hsecW happW
    obtain ⟨-, hfV⟩ := approach_edge hM₂ hS₂' hS₂f hV hp₂ ht' hnσ hsec₂ happV'
    exact ⟨d, hd, t₂, ht', hcutW, hfW, by rwa [hpos₂]⟩
  -- at a walk vertex: a side where both walks face the regions
  subst ht0
  obtain ⟨hd0, hdL⟩ := hsecd rfl
  have hP1 : 1 ≤ P := by
    by_contra hP0
    have hP0' : P = 0 := by omega
    have h0 := (J.whole.sidePt_box J.whole.sideBeta 0).1
    have h1 : sidePt J.wholeModel.W P 0 =
        (J.whole.top.1 + 0 * (-J.whole.radius - J.whole.top.1), J.whole.radius) := by
      rw [hP0']; try exact h0
    have hy := congrArg Prod.snd (hptW.symm.trans h1)
    simp only at hy
    have := J.whole.top_snd_lt_radius
    rw [hwy] at hy
    linarith
  have hvv : J.wholeModel.W.vtx P = J.rightModel.W.vtx (i + 6) := by
    rw [← Chazelle.Chain.sidePt_zero, ← Chazelle.Chain.sidePt_zero, hptW, hpt₂']
  have hbb : J.wholeModel.W.vtx ((P + 1) % J.wholeModel.W.n) =
      J.rightModel.W.vtx ((i + 6 + 1) % J.rightModel.W.n) := by
    have := hCorr.sideNext_eq hd
    rwa [hpos₂] at this
  have haa : J.wholeModel.W.vtx ((P + J.wholeModel.W.n - 1) %
      J.wholeModel.W.n) = J.rightModel.W.vtx ((i + 6 + J.rightModel.W.n - 1) %
      J.rightModel.W.n) := by
    have := hCorr.sidePrev_eq hd (t := 0) hsecd
    rw [hpos₂] at this
    unfold sidePrev at this
    rwa [ite_eq_left rfl, ite_eq_left rfl] at this
  obtain ⟨hWnc, hWc⟩ := approach_vertex hM hFs' hFf hG hPn hP1 hnσ hsecW happW
  obtain ⟨hVnc, hVc⟩ := approach_vertex hM₂ hS₂' hS₂f hV hp₂ (by omega) hnσ hsec₂ happV'
  rw [hbb, haa, hvv] at hWc
  have key : (∀ᶠ s in 𝓝[>] (0 : ℝ), J.wholeModel.Faces P s G ∧
        J.rightModel.Faces (i + 6) s V) ∨
      (∀ᶠ s in 𝓝[>] (0 : ℝ), J.wholeModel.Faces (P - 1) (1 - s) G ∧
        J.rightModel.Faces (i + 6 - 1) (1 - s) V) := by
    by_cases hcW : J.wholeModel.IsCut (F₂plus J S₂) ((P : ℝ) + 0)
    · obtain ⟨hd1, hA, hB⟩ := hWc hcW
      rcases hd1 with h | h
      · left
        have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), J.rightModel.Faces (i + 6) s V := by
          by_cases hc2 : J.rightModel.IsCut S₂ (((i + 6 : ℕ) : ℝ) + 0)
          · exact (hVc hc2).2.1 h
          · exact (hVnc hc2).1
        exact (hA h).and h2
      · right
        have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), J.rightModel.Faces (i + 6 - 1) (1 - s) V := by
          by_cases hc2 : J.rightModel.IsCut S₂ (((i + 6 : ℕ) : ℝ) + 0)
          · exact (hVc hc2).2.2 h
          · exact (hVnc hc2).2
        exact (hB h).and h2
    · by_cases hc2 : J.rightModel.IsCut S₂ (((i + 6 : ℕ) : ℝ) + 0)
      · obtain ⟨hd2, hA2, hB2⟩ := hVc hc2
        rcases hd2 with h | h
        · left; exact (hWnc hcW).1.and (hA2 h)
        · right; exact (hWnc hcW).2.and (hB2 h)
      · left; exact (hWnc hcW).1.and (hVnc hc2).1
  rcases key with key | key
  · obtain ⟨s, ⟨⟨hfW, hfV⟩, hnc⟩, hs⟩ := ((key.and
      (eventually_not_cut_after hM hFs' hFf (P : ℝ))).and (Ioo_mem_nhdsGT one_pos)).exists
    exact ⟨d, hd, s, hs, hnc, hfW, by rwa [hpos₂]⟩
  · obtain ⟨s, ⟨⟨hfW, hfV⟩, hnc⟩, hs⟩ := ((key.and
      (eventually_not_cut_before hM hFs' hFf (P : ℝ))).and (Ioo_mem_nhdsGT one_pos)).exists
    have hn0 : 0 < J.wholeModel.W.n := hCorr.n_pos
    have hPm : (6 + tpos J.whole J.m₁ + (d - 1)) % J.wholeModel.W.n = P - 1 := by
      rw [← mod_pred_mod hn0 _ (show 1 ≤ d by omega)]
      exact prev_mod hPn hP1
    have hdq1 : dq (rL1 J) (rδ J) (d - 1) = dq (rL1 J) (rδ J) d - 1 := by
      unfold dq; split_ifs <;> omega
    have hdq0 : 1 ≤ dq (rL1 J) (rδ J) d := by unfold dq; split_ifs <;> omega
    have hPm₂ : (6 + tpos J.right 0 + dq (rL1 J) (rδ J) (d - 1)) % J.rightModel.W.n =
        i + 6 - 1 := by
      rw [hdq1, ← mod_pred_mod hCorr.n₂_pos _ hdq0, hpos₂]
      exact prev_mod hp₂ (by omega)
    refine ⟨d - 1, by omega, 1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_, ?_, ?_⟩
    · rw [hPm, Nat.cast_sub hP1]
      push_cast
      rwa [show (P : ℝ) - 1 + (1 - s) = P - s by ring]
    · rwa [hPm]
    · rwa [hPm₂]

end Query

/-! ## Answering a query from the label -/

section Answer

variable (J : Merge.Junction)

/-- Points of the domain of `C` not above the top of `C₁` are in the domain of `C₁`. -/
theorem dom_left {x : Point} (hx : x ∈ J.whole.dom) (hx2 : x.2 ≤ J.left.top.2) :
    x ∈ J.left.dom := by
  by_contra h
  rcases (Merge.not_mem_dom_iff J.left hx2).1 h with h1 | h1
  · apply h1
    rw [FuseMath.radius_of_P J (C' := J.left) rfl]
    exact J.whole.dom_subset_box hx
  · exact J.whole.not_mem_set_of_mem_dom hx (J.left_set_subset h1)

end Answer

end Sweep

end

end Chazelle.Core
