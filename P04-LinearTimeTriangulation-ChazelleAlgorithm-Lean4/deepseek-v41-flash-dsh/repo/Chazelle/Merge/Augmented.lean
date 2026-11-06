module

public import Chazelle.Golf

public import Chazelle.Merge.Union
public import Chazelle.Merge.Removal

/-!
# Augmented chords of a chain and shooting along chords

Chazelle's submaps after a merge contain chords that "need not be incident upon any vertex of
`∂C`, hence the notion of augmented maps and submaps" (Remark 1, p. 507; augmented maps are
introduced on p. 493).  This file provides the augmented chords in the subchain model and the
elementary Euclidean operations on them used by the fusion (`Chazelle.Merge.Fusion`).

## Main definitions

* `lend c`, `rend c`: the left and right endpoints of a horizontal segment (`lend_hseg`,
  `rend_hseg`; `hseg_inj`: a nonempty `hseg` determines its parameters).
* `augChords C`: the horizontal chords of the domain `C.dom` (open part inside, endpoints off it)
  at heights `≤ C.top.2`.  Vertex chords are augmented chords (`chords_subset_augChords`).
* `FreeAt C p σ`: the initial part of the ray from `p` in direction `σ` is in the domain
  (`freeAt_vertex : FreeAt C (C.vertex k) σ ↔ C.DirFree k σ`).
* `shoot C p σ`: the chord seen from `p` in direction `σ` — the segment from `p` to the first
  point of `(C.dom)ᶜ` on the ray (`shoot_vertex : shoot C (C.vertex k) σ = C.chordSet k σ`).
* `throughChord C p`: the augmented chord through a point `p` of the domain.

## Main results

* `augChordSystem`: **every finite family of augmented chords is a `ChordSystem` of `C.dom`**
  (the endpoints are anchorable: `anchorable_left`, `anchorable_right`), hence
  `ncard_regionsIn_aug` (`k` chords, `k + 1` regions), `dual_isTree_aug`, and the removal API of
  `Chazelle.Merge.Removal` (`regionsIn_erase_aug`, `dualAdjIn_sdiff_iff_aug`).
* `hit_of_freeAt`, `shoot_mem_augChords`: shooting from a free point off the domain (possibly on
  the box perimeter) produces an augmented chord; `shoot_subset_pos`/`neg`: shooting along a
  segment whose far end is off the domain stays inside the segment; `hseg_eq_shoot`: every
  augmented chord is the shot from either of its endpoints.
* `throughChord_spec`, `throughChord_subset`: every point of the domain lies on an augmented chord,
  contained in any horizontal segment through the point with both ends off the domain.
* `finite_left_ends`, `finite_augChords_at`: **there are finitely many augmented chords at any
  given height** (their left ends are the left side of the box or right ends of the
  intersections of the chain edges with the line).
* `augChord_mem_region` (**regions are closed under visibility**, p. 502): the open part of an
  augmented chord not in a submap lies in one region of it, and its two endpoints in the
  closure of that region.
-/

namespace Chazelle.Merge

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd rayPt_zero continuous_rayPt hseg
  segment_horizontal_eq_hseg)
open Chazelle.Chain (IsHChordIn ChordSystem freeIn regionsIn mem_regionsIn openHSeg
  hseg_inter_eq_openHSeg isPreconnected_openHSeg openHSeg_nonempty mem_openHSeg_iff
  TouchesIn DualAdjIn)

/-! ### Horizontal segments and their endpoints -/

theorem fst_image_hseg (y a b : ℝ) : Prod.fst '' hseg y a b = Icc a b := by
  ext x
  constructor
  · rintro ⟨p, ⟨-, h1, h2⟩, rfl⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(x, y), ⟨rfl, h1, h2⟩, rfl⟩

/-- The heights of a nonempty horizontal segment. -/
theorem snd_image_hseg {y a b : ℝ} (h : a ≤ b) : Prod.snd '' hseg y a b = {y} := by
  ext t
  constructor
  · rintro ⟨p, ⟨hp, -, -⟩, rfl⟩
    exact hp
  · rintro rfl
    exact ⟨(a, t), ⟨rfl, le_rfl, h⟩, rfl⟩

/-- The left endpoint of a horizontal segment. -/
noncomputable def lend (c : Set Point) : Point := (sInf (Prod.fst '' c), sSup (Prod.snd '' c))

/-- The right endpoint of a horizontal segment. -/
noncomputable def rend (c : Set Point) : Point := (sSup (Prod.fst '' c), sSup (Prod.snd '' c))

/-- The left endpoint of `hseg y a b` (for `a ≤ b`) is `(a, y)`. -/
theorem lend_hseg {y a b : ℝ} (h : a ≤ b) : lend (hseg y a b) = (a, y) := by
  ϴ lend, fst_image_hseg, snd_image_hseg h, csInf_Icc h, csSup_singleton

/-- The right endpoint of `hseg y a b` (for `a ≤ b`) is `(b, y)`. -/
theorem rend_hseg {y a b : ℝ} (h : a ≤ b) : rend (hseg y a b) = (b, y) := by
  ϴ rend, fst_image_hseg, snd_image_hseg h, csSup_Icc h, csSup_singleton

/-- A nonempty horizontal segment determines its height and abscissae. -/
theorem hseg_inj {y a b y' a' b' : ℝ} (hab : a ≤ b) (h : hseg y a b = hseg y' a' b') :
    y = y' ∧ a = a' ∧ b = b' := by
  have hne : a' ≤ b' := by
    have : ((a, y) : Point) ∈ hseg y' a' b' := h ▸ (⟨rfl, le_rfl, hab⟩ : ((a, y) : Point) ∈ hseg y a b)
    exact this.2.1.trans this.2.2
  have h1 := lend_hseg hab (y := y)
  have h2 := rend_hseg hab (y := y)
  rw [h, lend_hseg hne] at h1
  rw [h, rend_hseg hne] at h2
  obtain ⟨e1, e2⟩ := Prod.ext_iff.1 h1
  obtain ⟨e3, -⟩ := Prod.ext_iff.1 h2
  exact ⟨e2.symm, e1.symm, e3.symm⟩

/-- A rightward ray segment as an `hseg`. -/
theorem segment_rayPt_pos (p : Point) {T : ℝ} (hT : 0 ≤ T) :
    Chazelle.segment p (rayPt p 1 T) = hseg p.2 p.1 (p.1 + T) := by
  rw [segment_horizontal_eq_hseg (rayPt_snd p 1 T).symm, rayPt_fst, one_mul,
    min_eq_left (⟡), max_eq_right (by linarith)]

/-- A leftward ray segment as an `hseg`. -/
theorem segment_rayPt_neg (p : Point) {T : ℝ} (hT : 0 ≤ T) :
    Chazelle.segment p (rayPt p (-1) T) = hseg p.2 (p.1 - T) p.1 := by
  rw [segment_horizontal_eq_hseg (rayPt_snd p (-1) T).symm, rayPt_fst, neg_one_mul,
    min_eq_right (⟡), max_eq_left (by linarith), ← sub_eq_add_neg]

/-! ### Augmented chords -/

/-- The **augmented chords** of a chain: horizontal chords of its domain (open part in the
domain, both endpoints off it) at heights not above the top of the chain. -/
def augChords (C : Chain) : Set (Set Point) :=
  {c | ∃ y a b : ℝ, IsHChordIn C.dom y a b ∧ y ≤ C.top.2 ∧ c = hseg y a b}

/-- Vertex chords are augmented chords. -/
theorem chords_subset_augChords (C : Chain) : C.chords ⊆ augChords C := by
  intro c hc
  obtain ⟨k, σ, hk, -, -, rfl, hh⟩ := C.chords_spec hc
  exact ⟨_, _, _, hh, C.vertex_snd_le_top hk, C.chordSet_eq_hseg k σ⟩

/-- Unpacking an augmented chord: its parameters and endpoints. -/
theorem augChords_spec {C : Chain} {c : Set Point} (hc : c ∈ augChords C) :
    ∃ y a b : ℝ, IsHChordIn C.dom y a b ∧ y ≤ C.top.2 ∧ c = hseg y a b ∧
      lend c = (a, y) ∧ rend c = (b, y) := by
  obtain ⟨y, a, b, h, hy, rfl⟩ := hc
  exact ⟨y, a, b, h, hy, rfl, lend_hseg h.lt.le, rend_hseg h.lt.le⟩

/-- The left endpoint of a horizontal chord of the domain is anchorable. -/
theorem anchorable_left (C : Chain) {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    C.Anchorable ((a, y) : Point) := by
  have hmid := h.open_mem ((a + b) / 2) (by linarith [h.lt]) (by linarith [h.lt])
  have hy : |y| < C.radius := (C.dom_subset_box hmid).2
  by_cases hbox : ((a, y) : Point) ∈ Chain.box C.radius
  · have hnd := h.left_not
    rw [C.mem_dom_iff] at hnd
    by_cases hs : ((a, y) : Point) ∈ C.set
    · exact Or.inl hs
    · right; left
      by_contra hsl
      exact hnd ⟨hbox, hs, hsl⟩
  · right; right; left
    have hge : C.radius ≤ |a| := by
      by_contra hlt
      push Not at hlt
      exact hbox ⟨hlt, hy⟩
    refine le_antisymm ?_ hge
    by_contra hgt
    push Not at hgt
    rcases lt_abs.1 hgt with h1 | h1
    · have := (C.dom_subset_box hmid).1
      rw [abs_lt] at this
      linarith [h.lt]
    · -- `a < -R`: a point of the open chord just right of `a` is outside the box
      have hx1 : a < (a + min b (-C.radius)) / 2 := by
        have : a < min b (-C.radius) := lt_min h.lt (⟡)
        linarith
      have hx2 : (a + min b (-C.radius)) / 2 < b := by
        have := min_le_left b (-C.radius)
        linarith
      have hx3 : (a + min b (-C.radius)) / 2 < -C.radius := by
        have := min_le_right b (-C.radius)
        linarith
      have := (C.dom_subset_box (h.open_mem _ hx1 hx2)).1
      rw [abs_lt] at this
      linarith [this.1]

/-- The right endpoint of a horizontal chord of the domain is anchorable. -/
theorem anchorable_right (C : Chain) {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    C.Anchorable ((b, y) : Point) := by
  have hmid := h.open_mem ((a + b) / 2) (by linarith [h.lt]) (by linarith [h.lt])
  have hy : |y| < C.radius := (C.dom_subset_box hmid).2
  by_cases hbox : ((b, y) : Point) ∈ Chain.box C.radius
  · have hnd := h.right_not
    rw [C.mem_dom_iff] at hnd
    by_cases hs : ((b, y) : Point) ∈ C.set
    · exact Or.inl hs
    · right; left
      by_contra hsl
      exact hnd ⟨hbox, hs, hsl⟩
  · right; right; left
    have hge : C.radius ≤ |b| := by
      by_contra hlt
      push Not at hlt
      exact hbox ⟨hlt, hy⟩
    refine le_antisymm ?_ hge
    by_contra hgt
    push Not at hgt
    rcases lt_abs.1 hgt with h1 | h1
    · have hx1 : a < (max a C.radius + b) / 2 := by
        have : max a C.radius < b := max_lt h.lt h1
        have := le_max_left a C.radius
        linarith
      have hx2 : (max a C.radius + b) / 2 < b := by
        have : max a C.radius < b := max_lt h.lt h1
        linarith
      have hx3 : C.radius < (max a C.radius + b) / 2 := by
        have : max a C.radius < b := max_lt h.lt h1
        have := le_max_right a C.radius
        linarith
      have := (C.dom_subset_box (h.open_mem _ hx1 hx2)).1
      rw [abs_lt] at this
      linarith [this.2]
    · have := (C.dom_subset_box hmid).1
      rw [abs_lt] at this
      linarith [h.lt]

/-- **Every finite family of augmented chords is a chord system of the domain.** -/
theorem augChordSystem (C : Chain) {F : Set (Set Point)} (hF : F ⊆ augChords C)
    (hfin : F.Finite) : ChordSystem C.dom F where
  isOpen := C.isOpen_dom
  finite := hfin
  hchord := by
    intro c hc
    obtain ⟨y, a, b, h, -, rfl⟩ := hF hc
    exact ⟨y, a, b, h, rfl⟩
  walk := by
    intro c hc z hz hzd
    obtain ⟨y, a, b, h, -, rfl⟩ := hF hc
    have hseg_eq : Chazelle.segment ((a, y) : Point) (b, y) = hseg y a b := by
      Ξ segment_horizontal_eq_hseg (a := ((a, y) : Point)) (b := ((b, y) : Point)) rfl
      dsimp only
      Ξ min_eq_left h.lt.le, max_eq_right h.lt.le
    rw [← hseg_eq] at hz ⊢
    exact C.exists_walk_parity_flip (anchorable_left C h) (anchorable_right C h)
      (by simp only [ne_eq]; exact h.lt.ne) hz hzd

/-! ### Removal in augmented submaps -/

/-! ### Shooting along a chord -/

/-- The initial part of the ray from `p` in direction `σ` lies in the domain. -/
def FreeAt (C : Chain) (p : Point) (σ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt p σ t ∈ C.dom

/-- The chord of `C` seen from `p` in direction `σ`: the segment from `p` to the first point of
`(C.dom)ᶜ` on the ray (Chazelle's "point of `∂C` seen by `p`"). -/
noncomputable def shoot (C : Chain) (p : Point) (σ : ℝ) : Set Point :=
  Chazelle.segment p (rayPt p σ (C.hitParam p σ))

/-- Shooting from a chain vertex gives its vertex chord. -/
theorem shoot_vertex (C : Chain) (k : ℕ) (σ : ℝ) : shoot C (C.vertex k) σ = C.chordSet k σ := rfl

/-- Freeness at a chain vertex is `DirFree`. -/
theorem freeAt_vertex (C : Chain) (k : ℕ) (σ : ℝ) : FreeAt C (C.vertex k) σ ↔ C.DirFree k σ :=
  Iff.rfl

/-- **The first hit from a free point** at height `≤ C.top.2` (the point may be on the box
perimeter). -/
theorem hit_of_freeAt (C : Chain) {p : Point} (hp : p.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (h : FreeAt C p σ) :
    0 < C.hitParam p σ ∧ rayPt p σ (C.hitParam p σ) ∉ C.dom ∧
      ∀ t, 0 < t → t < C.hitParam p σ → rayPt p σ t ∈ C.dom := by
  Ξ hitParam_eq_rayHit C hp
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  rw [mem_Ioi] at hu
  have hle : u ≤ rayHit C.radius C.set p σ := le_rayHit hσ fun t ht1 ht2 => by
    have hd : rayPt p σ t ∈ C.dom := hsub ⟨ht1, ht2⟩
    exact ⟨C.dom_subset_box hd, C.not_mem_set_of_mem_dom hd⟩
  have hpos := lt_of_lt_of_le hu hle
  obtain ⟨h1, h2⟩ := rayHit_spec (r := C.radius) C.isClosed_set p hσ
  have hsnd : ∀ t, (rayPt p σ t).2 ≤ C.top.2 := fun t => by rw [rayPt_snd]; exact hp
  refine ⟨hpos, (not_mem_dom_iff C (hsnd _)).2 (h2 hpos), fun t ht1 ht2 => ?_⟩
  by_contra hnd
  obtain ⟨hb, hs⟩ := h1 t ht1 ht2
  rcases (not_mem_dom_iff C (hsnd t)).1 hnd with h' | h'
  · exact h' hb
  · exact hs h'

/-- The chord seen from a free point off the domain is an augmented chord. -/
theorem shoot_mem_augChords (C : Chain) {p : Point} (hp : p.2 ≤ C.top.2) (hnd : p ∉ C.dom)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : FreeAt C p σ) : shoot C p σ ∈ augChords C := by
  obtain ⟨hpos, hend, hint⟩ := hit_of_freeAt C hp hσ h
  set T := C.hitParam p σ with hT
  rcases hσ with rfl | rfl
  · refine ⟨p.2, p.1, p.1 + T, ⟨⟡, hnd, ?_, fun x hx1 hx2 => ?_⟩, hp,
      segment_rayPt_pos p hpos.le⟩
    · have : ((p.1 + T, p.2) : Point) = rayPt p 1 T := ⊚ rayPt
      rw [this]; exact hend
    · have := hint (x - p.1) (⟡) (by linarith)
      have e : rayPt p 1 (x - p.1) = ((x, p.2) : Point) := by
        ϴ rayPt, one_mul, add_sub_cancel
      rwa [e] at this
  · refine ⟨p.2, p.1 - T, p.1, ⟨⟡, ?_, hnd, fun x hx1 hx2 => ?_⟩, hp,
      segment_rayPt_neg p hpos.le⟩
    · have : ((p.1 - T, p.2) : Point) = rayPt p (-1) T := ⊚ rayPt, sub_eq_add_neg
      rw [this]; exact hend
    · have := hint (p.1 - x) (⟡) (by linarith)
      have e : rayPt p (-1) (p.1 - x) = ((x, p.2) : Point) := by
        ϴ rayPt, neg_one_mul, neg_sub, add_sub_cancel
      rwa [e] at this

/-- Shooting rightwards from the left end of a segment whose right end is off the domain stays
inside the segment. -/
theorem shoot_subset_pos (C : Chain) {y a b : ℝ} (hab : a < b)
    (hb : ((b, y) : Point) ∉ C.dom) : shoot C ((a, y) : Point) 1 ⊆ hseg y a b := by
  have hle : C.hitParam ((a, y) : Point) 1 ≤ b - a := by
    refine C.hitParam_le_of_not_mem_dom _ 1 (⟡) ?_
    have : rayPt ((a, y) : Point) 1 (b - a) = ((b, y) : Point) := by
      ϴ rayPt, one_mul, add_sub_cancel
    rw [this]; exact hb
  have h := segment_rayPt_subset ((a, y) : Point) 1 (hitParam_nonneg C _ 1) hle
  have e : Chazelle.segment ((a, y) : Point) (rayPt ((a, y) : Point) 1 (b - a)) = hseg y a b := by
    rw [segment_rayPt_pos _ (⟡)]
    dsimp only
    Ξ add_sub_cancel
  rw [e] at h
  exact h

/-- Shooting leftwards from the right end of a segment whose left end is off the domain stays
inside the segment. -/
theorem shoot_subset_neg (C : Chain) {y a b : ℝ} (hab : a < b)
    (ha : ((a, y) : Point) ∉ C.dom) : shoot C ((b, y) : Point) (-1) ⊆ hseg y a b := by
  have hle : C.hitParam ((b, y) : Point) (-1) ≤ b - a := by
    refine C.hitParam_le_of_not_mem_dom _ (-1) (⟡) ?_
    have : rayPt ((b, y) : Point) (-1) (b - a) = ((a, y) : Point) := by
      ϴ rayPt, neg_one_mul, neg_sub, add_sub_cancel
    rw [this]; exact ha
  have h := segment_rayPt_subset ((b, y) : Point) (-1) (hitParam_nonneg C _ (-1)) hle
  have e : Chazelle.segment ((b, y) : Point) (rayPt ((b, y) : Point) (-1) (b - a)) =
      hseg y a b := by
    rw [segment_rayPt_neg _ (⟡)]
    dsimp only
    Ξ sub_sub_cancel
  rw [e] at h
  exact h

/-! ### Vertex chords as shots -/

/-! ### The chord through a point, and finiteness of the chords at one height -/

/-- Every point of the (open) domain is free in every direction. -/
theorem freeAt_of_mem_dom (C : Chain) {p : Point} (hp : p ∈ C.dom) (σ : ℝ) : FreeAt C p σ := by
  have hcont : ContinuousAt (rayPt p σ) 0 := (continuous_rayPt p σ).continuousAt
  have hmem : C.dom ∈ 𝓝 (rayPt p σ 0) := by
    rw [rayPt_zero]; exact C.isOpen_dom.mem_nhds hp
  exact nhdsWithin_le_nhds (hcont.preimage_mem_nhds hmem)

/-- The left end of a horizontal chord of the domain is free rightwards. -/
theorem freeAt_of_isHChordIn_left (C : Chain) {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    FreeAt C ((a, y) : Point) 1 := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < b - a by linarith [h.lt])] with t ht
  have e : rayPt ((a, y) : Point) 1 t = ((a + t, y) : Point) := ⊚ rayPt
  Ξ e
  exact h.open_mem _ (by linarith [ht.1]) (by linarith [ht.2])

/-- The right end of a horizontal chord of the domain is free leftwards. -/
theorem freeAt_of_isHChordIn_right (C : Chain) {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    FreeAt C ((b, y) : Point) (-1) := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < b - a by linarith [h.lt])] with t ht
  have e : rayPt ((b, y) : Point) (-1) t = ((b - t, y) : Point) := by
    Θ rayPt, sub_eq_add_neg
  Ξ e
  exact h.open_mem _ (by linarith [ht.2]) (by linarith [ht.1])

/-- A horizontal chord of the domain is the chord shot from its left end. -/
theorem hseg_eq_shoot (C : Chain) {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    hseg y a b = shoot C ((a, y) : Point) 1 := by
  have hT : C.hitParam ((a, y) : Point) 1 = b - a := by
    refine C.hitParam_eq_of_first _ 1 (by linarith [h.lt]) ?_ fun s hs1 hs2 => ?_
    · have : rayPt ((a, y) : Point) 1 (b - a) = ((b, y) : Point) := by
        ϴ rayPt, one_mul, add_sub_cancel
      rw [this]; exact h.right_not
    · have e : rayPt ((a, y) : Point) 1 s = ((a + s, y) : Point) := ⊚ rayPt
      Ξ e
      exact h.open_mem _ (⟡) (by linarith)
  unfold shoot
  Ξ hT, segment_rayPt_pos _ (by linarith [h.lt])
  dsimp only
  Ξ add_sub_cancel

/-- A horizontal chord of the domain is the chord shot from its right end. -/
theorem hseg_eq_shoot_neg (C : Chain) {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    hseg y a b = shoot C ((b, y) : Point) (-1) := by
  have hT : C.hitParam ((b, y) : Point) (-1) = b - a := by
    refine C.hitParam_eq_of_first _ (-1) (by linarith [h.lt]) ?_ fun s hs1 hs2 => ?_
    · have : rayPt ((b, y) : Point) (-1) (b - a) = ((a, y) : Point) := by
        ϴ rayPt, neg_one_mul, neg_sub, add_sub_cancel
      rw [this]; exact h.left_not
    · have e : rayPt ((b, y) : Point) (-1) s = ((b - s, y) : Point) := by
        Θ rayPt, sub_eq_add_neg
      Ξ e
      exact h.open_mem _ (⟡) (by linarith)
  unfold shoot
  Ξ hT, segment_rayPt_neg _ (by linarith [h.lt])
  dsimp only
  Ξ sub_sub_cancel

/-! ### Regions are closed under visibility -/

end

end Chazelle.Merge
