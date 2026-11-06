module

public import Chazelle.Core.SweepEvStopM

/-!
# The sweep (WP-D), stage 2: the origins of the stop chords (mathematics)

A stop record `(e, h, kind, k, b)` names the chord `stopSet J Q N kind k b`, the chord of `C` seen
from the origin `stOrig J Q N kind k b` (the shared vertex, the end of chord `k` of `N₂` in the
direction `dirOf b`, or the top of `C₂`) in the direction `dirOf b` (`stopSet_eq`).

* `StOK`: the admissible codes (the end of a wall chord lies on a vertical side of the box);
* `stOrig_facts`: the origin is off the domain of `C`, not above the top of `C₂`, a point of `C`
  or of a vertical side of the box;
* `stop_mem`: a free direction gives a chord of `F₂⁺` that is a stop chord;
* `stop_complete`: every stop chord is the chord of some admissible code;
* `free_left`, `free_right`: freeness for `C` gives freeness for `C₁` and `C₂`;
* `hit_cases`, `hit_min`: the first hit of `C` is that of `C₂` or (not above the top of `C₁`)
  that of `C₁`, and the least of a set of candidates off the domain containing it.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace SweepStop

open Sweep SweepIo

variable {J : Merge.Junction}

/-- **The origin of a stop record.** -/
noncomputable def stOrig (J : Merge.Junction) (Q : Polygon) (N : NF) (kind k b : ℕ) : Point :=
  if kind = 0 then J.shared
  else if kind = 1 then endOrigin J Q N (2 * k + (if dirOf b = 1 then 0 else 1))
  else J.right.top

theorem stopSet_eq (J : Merge.Junction) (Q : Polygon) (N : NF) (kind k b : ℕ) :
    stopSet J Q N kind k b = Merge.shoot J.whole (stOrig J Q N kind k b) (dirOf b) := by
  unfold stopSet stOrig
  split_ifs <;> rfl

theorem dirOf_one : dirOf 1 = 1 := by simp [dirOf]

theorem dirOf_zero : dirOf 0 = -1 := by simp [dirOf]

/-- The end index of a wall record. -/
theorem wall_j {k b : ℕ} (hb : b ≤ 1) :
    2 * k + (if dirOf b = 1 then 0 else 1) = 2 * k + (1 - b) := by
  rw [show (if dirOf b = 1 then 0 else 1) = 1 - b by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;> norm_num [dirOf]]

/-- **The admissible codes** of a stop record. -/
def StOK (_P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) : Prop :=
  kind ≤ 2 ∧ b ≤ 1 ∧ (kind = 1 → k < N.nChords ∧ (endPos N k (1 - b)).edge < 6) ∧
    (kind = 2 → J.right.topIdx ≠ 0)

/-- The chord records of a normal form are chords of its family. -/
theorem chord_mem {M : Model} {Q : Polygon} {N : NF} {k : ℕ} (hk : k < N.nChords) :
    (N.chord k).toSet M Q ∈ N.F M Q := by
  refine ⟨N.chord k, ?_, rfl⟩
  unfold NF.chord
  rw [NFLoc.getD_of_lt _ hk]
  exact List.getElem_mem _

/-- A position on a vertical side of the box has the abscissa `±R`. -/
theorem wall_abs (C : Chain) (Q : Polygon) {x : WPos} (h : x.edge = 1 ∨ x.edge = 3) :
    |((chainModel C).pos Q x).1| = C.radius := by
  show |(sidePt (chainModel C).W x.edge ((chainModel C).param Q x)).1| = _
  obtain ⟨-, b1, -, b3, -, -, -⟩ := C.sidePt_box C.sideBeta ((chainModel C).param Q x)
  rw [cm_W]
  rcases h with h | h
  · rw [h, b1]; simp only; rw [abs_neg, abs_of_pos C.radius_pos]
  · rw [h, b3]; simp only; rw [abs_of_pos C.radius_pos]

/-- A point with abscissa `±R` is off the chain. -/
theorem not_mem_set_of_abs (C : Chain) {z : Point} (h : |z.1| = C.radius) : z ∉ C.set := by
  intro hm
  have := (C.abs_le_coordBound_of_mem_set hm).1
  have := C.coordBound_lt_radius
  linarith

/-- **The end of a chord record off `C₂`**: its walk edge is below `6` (a vertical side of the
box), and conversely; the end is a position of the class of `convS`. -/
theorem end_off_iff (_hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) (Qof P) N) {k s : ℕ} (hk : k < N.nChords) :
    PosClass J.right (Qof P) (endPos N k s) ∧
    ((chainModel J.right).pos (Qof P) (endPos N k s) ∉ J.right.set ↔ (endPos N k s).edge < 6) := by
  have hS₂ := hN.1
  have hc : (N.chord k).toSet (chainModel J.right) (Qof P) ∈ N.F (chainModel J.right) (Qof P) :=
    chord_mem hk
  have hA := hN.2.2.1 k hk
  have hatt : SideAttach (chainModel J.right).W ((N.chord k).toSet (chainModel J.right) (Qof P))
      (endPos N k s).edge ((chainModel J.right).param (Qof P) (endPos N k s)) := by
    unfold endPos; split_ifs
    · exact hA.1
    · exact hA.2
  obtain ⟨y, l, r, hH, hy, heq, -, -⟩ := Merge.augChords_spec (hS₂.2.1 hc)
  have hpt : (chainModel J.right).pos (Qof P) (endPos N k s) ∈
      (N.chord k).toSet (chainModel J.right) (Qof P) := hatt.2.2.2.1
  rw [heq] at hpt
  have hyy : ((chainModel J.right).pos (Qof P) (endPos N k s)).2 = y := hpt.1
  have hboxy : |y| < J.right.radius := by
    have hmid := hH.open_mem ((l + r) / 2) (by linarith [hH.lt]) (by linarith [hH.lt])
    exact (J.right.dom_subset_box hmid).2
  have hcl := posClass_of (C := J.right) hatt.1 hatt.2.1 hatt.2.2.1 (by rwa [hyy])
    (Or.inl (by rwa [hyy]))
  refine ⟨hcl, ⟨fun hn => ?_, fun h6 => ?_⟩⟩
  · rcases hcl with (h | h) | ⟨h6, hlt⟩ | ⟨h6, hz⟩
    · omega
    · omega
    · exfalso; apply hn
      have hm := J.right.sideWalk_tour_pt_mem J.right.sideBeta (i := (endPos N k s).edge - 6)
        (t := (chainModel J.right).param (Qof P) (endPos N k s)) (by omega)
        (fun h'' => by omega) hatt.2.1 hatt.2.2.1
      rwa [show (endPos N k s).edge - 6 + 6 = (endPos N k s).edge by omega] at hm
    · exfalso; apply hn
      have hm := J.right.sideWalk_tour_pt_mem J.right.sideBeta (i := 2 * J.right.m) (t := 0)
        le_rfl (fun _ => rfl) le_rfl one_pos
      show sidePt (chainModel J.right).W _ _ ∈ _
      rwa [cm_W, h6, hz]
  · rcases hcl with (h | h) | ⟨h6', -⟩ | ⟨h6', -⟩
    · exact not_mem_set_of_abs J.right (wall_abs J.right (Qof P) (Or.inl h))
    · exact not_mem_set_of_abs J.right (wall_abs J.right (Qof P) (Or.inr h))
    · omega
    · omega

/-! ## The origins -/

/-- The radius of the box of `C₂` is that of `C`. -/
theorem radius_right : J.right.radius = J.whole.radius := rfl

/-- The origin of a wall record is the end `1 - b` of the chord `k`. -/
theorem stOrig_wall {Q : Polygon} {N : NF} (hN : IsNF (chainModel J.right) Q N) {k b : ℕ}
    (hk : k < N.nChords) (hb : b ≤ 1) :
    stOrig J Q N 1 k b = (chainModel J.right).pos Q (endPos N k (1 - b)) ∧
      ((b = 1 ∧ stOrig J Q N 1 k b = Merge.lend ((N.chord k).toSet (chainModel J.right) Q)) ∨
        (b = 0 ∧ stOrig J Q N 1 k b = Merge.rend ((N.chord k).toSet (chainModel J.right) Q))) := by
  have hj : 2 * k + (1 - b) < 2 * N.nChords := by omega
  obtain ⟨hEO, -⟩ := endOrigin_eq J hN hj
  have e1 : (2 * k + (1 - b)) / 2 = k := by omega
  have e2 : (2 * k + (1 - b)) % 2 = 1 - b := by omega
  rw [e1, e2] at hEO
  have hs : stOrig J Q N 1 k b = endOrigin J Q N (2 * k + (1 - b)) := by
    unfold stOrig; rw [ite_eq_right (by norm_num), ite_eq_left rfl, wall_j hb]
  refine ⟨hs.trans hEO, ?_⟩
  rw [hs]
  unfold endOrigin
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl
  · right; refine ⟨rfl, ?_⟩
    rw [ite_eq_right (by omega), show (2 * k + (1 - 0)) / 2 = k by omega]
  · left; refine ⟨rfl, ?_⟩
    rw [ite_eq_left (by omega), show (2 * k + (1 - 1)) / 2 = k by omega]

/-- **The facts of an origin**: off the domain of `C`, not above the top of `C₂`, strictly inside
the height band of the box, a point of `C` (shared vertex, top) or of a vertical side of the box
(wall ends). -/
theorem stOrig_facts (hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) (Qof P) N) {kind k b : ℕ} (hok : StOK P J N kind k b) :
    stOrig J (Qof P) N kind k b ∉ J.whole.dom ∧
      (stOrig J (Qof P) N kind k b).2 ≤ J.right.top.2 ∧
      |(stOrig J (Qof P) N kind k b).2| < J.whole.radius ∧
      (kind ≠ 1 → stOrig J (Qof P) N kind k b ∈ J.right.set) ∧
      (kind = 1 → |(stOrig J (Qof P) N kind k b).1| = J.whole.radius) := by
  obtain ⟨hk2, hb, hw, -⟩ := hok
  have hset : ∀ z ∈ J.right.set, z ∉ J.whole.dom ∧ z.2 ≤ J.right.top.2 ∧
      |z.2| < J.whole.radius := fun z hz =>
    ⟨fun hd => J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset hz),
      J.right.snd_le_top_of_mem_set hz, by
        rw [← radius_right]
        exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set hz).2
          J.right.coordBound_lt_radius⟩
  by_cases h1 : kind = 1
  · subst h1
    obtain ⟨hkN, h6⟩ := hw rfl
    obtain ⟨hcl, hiff⟩ := end_off_iff hP hN hkN (s := 1 - b)
    obtain ⟨hpos, -⟩ := stOrig_wall hN hkN hb
    rw [hpos]
    have hwall : (endPos N k (1 - b)).edge = 1 ∨ (endPos N k (1 - b)).edge = 3 := by
      rcases hcl with h | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · omega
      · omega
    have hx := wall_abs J.right (Qof P) hwall
    -- the end lies on the chord: its height
    have hc := chord_mem (M := chainModel J.right) (Q := Qof P) hkN
    have hA := hN.2.2.1 k hkN
    have hatt : SideAttach (chainModel J.right).W ((N.chord k).toSet (chainModel J.right) (Qof P))
        (endPos N k (1 - b)).edge ((chainModel J.right).param (Qof P) (endPos N k (1 - b))) := by
      unfold endPos; split_ifs
      · exact hA.1
      · exact hA.2
    obtain ⟨y, l, r, hH, hy, heq, -, -⟩ := Merge.augChords_spec (hN.1.2.1 hc)
    have hpt : (chainModel J.right).pos (Qof P) (endPos N k (1 - b)) ∈
        (N.chord k).toSet (chainModel J.right) (Qof P) := hatt.2.2.2.1
    rw [heq] at hpt
    have hyy : ((chainModel J.right).pos (Qof P) (endPos N k (1 - b))).2 = y := hpt.1
    have hboxy : |y| < J.right.radius := by
      have hmid := hH.open_mem ((l + r) / 2) (by linarith [hH.lt]) (by linarith [hH.lt])
      exact (J.right.dom_subset_box hmid).2
    refine ⟨fun hd => ?_, by rwa [hyy], by rwa [hyy, ← radius_right],
      fun h => absurd rfl h, fun _ => by rwa [← radius_right]⟩
    have hb' := (J.whole.dom_subset_box hd).1
    rw [← radius_right, hx] at hb'
    exact lt_irrefl _ hb'
  · have hmem : stOrig J (Qof P) N kind k b ∈ J.right.set := by
      unfold stOrig
      split_ifs
      · exact J.shared_mem_right
      · exact J.right.top_mem_set
    obtain ⟨a1, a2, a3⟩ := hset _ hmem
    exact ⟨a1, a2, a3, fun _ => hmem, fun h => absurd h h1⟩

/-- **The chord of an admissible code with a free direction** is a stop chord of `F₂⁺`. -/
theorem stop_mem (hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) (Qof P) N) {kind k b : ℕ} (hok : StOK P J N kind k b)
    (hf : FreeAt J.whole (stOrig J (Qof P) N kind k b) (dirOf b)) :
    stopSet J (Qof P) N kind k b ∈ F₂plus J (N.F (chainModel J.right) (Qof P)) ∧
      StopChord2 J (N.F (chainModel J.right) (Qof P)) (stopSet J (Qof P) N kind k b) := by
  rw [stopSet_eq]
  obtain ⟨hk2, hb, hw, -⟩ := hok
  have hσ := dirOf_cases' b
  by_cases h0 : kind = 0
  · subst h0
    have hv : stOrig J (Qof P) N 0 k b = J.whole.vertex J.m₁ := by
      unfold stOrig; rw [ite_eq_left rfl]; rfl
    rw [hv] at hf ⊢
    refine ⟨Or.inl (Or.inr ⟨dirOf b, hσ, (Merge.freeAt_vertex _ _ _).1 hf, rfl⟩),
      Or.inl (Or.inl ⟨dirOf b, hσ, hf, rfl⟩)⟩
  by_cases h1 : kind = 1
  · subst h1
    obtain ⟨hkN, h6⟩ := hw rfl
    obtain ⟨-, hiff⟩ := end_off_iff hP hN hkN (s := 1 - b)
    obtain ⟨hpos, hcase⟩ := stOrig_wall hN hkN hb
    have hc := chord_mem (M := chainModel J.right) (Q := Qof P) hkN
    have hoff : stOrig J (Qof P) N 1 k b ∉ J.right.set := by rw [hpos]; exact hiff.2 h6
    have ha : (dirOf b = 1 ∧ stOrig J (Qof P) N 1 k b =
          Merge.lend ((N.chord k).toSet (chainModel J.right) (Qof P))) ∨
        (dirOf b = -1 ∧ stOrig J (Qof P) N 1 k b =
          Merge.rend ((N.chord k).toSet (chainModel J.right) (Qof P))) := by
      rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
      · exact Or.inl ⟨dirOf_one, h⟩
      · exact Or.inr ⟨dirOf_zero, h⟩
    exact ⟨shoot_end_mem hc ha hf, Or.inl (Or.inr ⟨_, hc, _, _, ha, hoff, hf, rfl⟩)⟩
  · have h2 : kind = 2 := by omega
    subst h2
    have hv : stOrig J (Qof P) N 2 k b = J.whole.vertex (J.m₁ + J.right.topIdx) := by
      unfold stOrig; rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num), Merge.Junction.whole_vertex_add]
      rfl
    have hf' := hf
    rw [hv] at hf'
    refine ⟨Or.inr ⟨dirOf b, hσ, (Merge.freeAt_vertex _ _ _).1 hf', by rw [hv]; rfl⟩,
      Or.inr ⟨dirOf b, hσ, ?_, ?_⟩⟩
    · unfold stOrig at hf; rwa [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at hf
    · unfold stOrig; rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]

/-- A code `b ≤ 1` for a direction. -/
theorem code_of_dir {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ b, b ≤ 1 ∧ dirOf b = σ := by
  rcases hσ with rfl | rfl
  · exact ⟨1, le_rfl, dirOf_one⟩
  · exact ⟨0, zero_le_one, dirOf_zero⟩

/-- A chord of a normal form is a chord record. -/
theorem chord_of_mem {M : Model} {Q : Polygon} {N : NF} {c : Set Point} (hc : c ∈ N.F M Q) :
    ∃ k, k < N.nChords ∧ c = (N.chord k).toSet M Q := by
  obtain ⟨r, hr, rfl⟩ := hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  refine ⟨k, hk, ?_⟩
  unfold NF.chord
  rw [NFLoc.getD_of_lt _ hk]

/-- **Every stop chord is the chord of an admissible code** with a free direction. -/
theorem stop_complete (hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) (Qof P) N) {e : Set Point}
    (hs : StopChord2 J (N.F (chainModel J.right) (Qof P)) e) :
    ∃ kind k b, StOK P J N kind k b ∧ FreeAt J.whole (stOrig J (Qof P) N kind k b) (dirOf b) ∧
      e = stopSet J (Qof P) N kind k b := by
  rcases hs with (⟨σ, hσ, hf, rfl⟩ | ⟨c, hc, a, σ, ha, hoff, hf, rfl⟩) | ⟨σ, hσ, hf, rfl⟩
  · obtain ⟨b, hb, rfl⟩ := code_of_dir hσ
    refine ⟨0, 0, b, ⟨by norm_num, hb, fun h => absurd h (by norm_num), fun h => absurd h
      (by norm_num)⟩, ?_, ?_⟩
    · unfold stOrig; rwa [ite_eq_left rfl]
    · rw [stopSet_eq]; unfold stOrig; rw [ite_eq_left rfl]
  · obtain ⟨k, hk, rfl⟩ := chord_of_mem hc
    have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
    obtain ⟨b, hb, rfl⟩ := code_of_dir hσ
    obtain ⟨hpos, hcase⟩ := stOrig_wall (Q := Qof P) hN hk hb
    have hab : stOrig J (Qof P) N 1 k b = a := by
      rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h, h2]
      · rw [dirOf_one] at h1; norm_num at h1
      · rw [dirOf_zero] at h1; norm_num at h1
      · rw [h, h2]
    obtain ⟨-, hiff⟩ := end_off_iff hP hN hk (s := 1 - b)
    refine ⟨1, k, b, ⟨by norm_num, hb, fun _ => ⟨hk, hiff.1 (by rwa [← hpos, hab])⟩,
      fun h => absurd h (by norm_num)⟩, by rwa [hab], ?_⟩
    rw [stopSet_eq, hab]
  · obtain ⟨b, hb, rfl⟩ := code_of_dir hσ
    by_cases ht : J.right.topIdx = 0
    · have hv : J.right.top = J.shared := by
        show J.right.vertex J.right.topIdx = _
        rw [ht, ← Merge.Junction.whole_vertex_add, Nat.add_zero]; rfl
      refine ⟨0, 0, b, ⟨by norm_num, hb, fun h => absurd h (by norm_num), fun h => absurd h
        (by norm_num)⟩, ?_, ?_⟩
      · unfold stOrig; rwa [ite_eq_left rfl, ← hv]
      · rw [stopSet_eq]; unfold stOrig; rw [ite_eq_left rfl, hv]
    · refine ⟨2, 0, b, ⟨le_rfl, hb, fun h => absurd h (by norm_num), fun _ => ht⟩, ?_, ?_⟩
      · unfold stOrig; rwa [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]
      · rw [stopSet_eq]; unfold stOrig; rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]

/-! ## The first hit of `C` -/

/-- **Freeness for `C`** gives freeness for `C₁` (not above its top). -/
theorem free_left {a : Point} {σ : ℝ} (hf : FreeAt J.whole a σ) (ha : a.2 ≤ J.left.top.2) :
    FreeAt J.left a σ := by
  filter_upwards [hf] with t ht
  exact J.mem_left_dom_of_whole (by rwa [rayPt_snd]) ht

/-- **Freeness for `C`** gives freeness for `C₂` (not above its top). -/
theorem free_right {a : Point} {σ : ℝ} (hf : FreeAt J.whole a σ) (ha : a.2 ≤ J.right.top.2) :
    FreeAt J.right a σ := by
  filter_upwards [hf] with t ht
  exact J.mem_right_dom_of_whole (by rwa [rayPt_snd]) ht

/-- **The first hit of `C`** is that of `C₂`, or (not above the top of `C₁`) that of `C₁`. -/
theorem hit_cases {a : Point} (ha : a.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    J.whole.hitParam a σ = J.right.hitParam a σ ∨
      (a.2 ≤ J.left.top.2 ∧ J.whole.hitParam a σ = J.left.hitParam a σ) := by
  rw [whole_hitParam_eq_min J (le_trans ha J.right_top_le) hσ, right_hitParam_eq J ha]
  by_cases h₁ : a.2 ≤ J.left.top.2
  · rw [left_hitParam_eq J h₁]
    rcases le_total (J.left.hitParam a σ) (J.right.hitParam a σ) with h | h
    · exact Or.inr ⟨h₁, min_eq_left h⟩
    · exact Or.inl (min_eq_right h)
  · push Not at h₁
    left
    rw [rayHit_eq_empty_of_above J.left h₁, ← right_hitParam_eq J ha]
    apply min_eq_right
    exact csInf_le_csInf (Merge.rayHitSet_bddBelow _ _ _ _) (Merge.rayHitSet_nonempty _ _ _ hσ)
      (fun t ht => ⟨ht.1, by rcases ht.2 with h | h; exact Or.inl h; exact absurd h (by simp)⟩)

/-- **The least candidate is the first hit**: candidates are positive parameters of points off
the domain of `C`, and the first hit is a candidate. -/
theorem hit_min {a : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : a.2 ≤ J.whole.top.2)
    (hf : FreeAt J.whole a σ) {L : Set ℝ} (hL : ∀ τ ∈ L, 0 < τ ∧ rayPt a σ τ ∉ J.whole.dom)
    (hmem : J.whole.hitParam a σ ∈ L) {τm : ℝ} (hτm : τm ∈ L) (hmin : ∀ τ' ∈ L, τm ≤ τ') :
    τm = J.whole.hitParam a σ := by
  obtain ⟨-, -, hin⟩ := Merge.hit_of_freeAt J.whole ha hσ hf
  refine le_antisymm (hmin _ hmem) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨hpos, hon⟩ := hL τm hτm
  exact hon (hin τm hpos hlt)

end SweepStop

end

end Chazelle.Core
