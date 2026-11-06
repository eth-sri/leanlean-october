module

public import Chazelle.Golf

public import Chazelle.Visibility.Ray
public import Chazelle.Existence.Convex
public import Mathlib.Data.Set.Card

/-!
# Vertex chords of the horizontal visibility map

At a vertex `v = P.vtx i` and for a horizontal direction `σ ∈ {1, -1}` (`1` = right, `-1` =
left), the points `rayPt v σ t = (v.1 + σ t, v.2)` for all small `t > 0` are

* all interior (`DirInterior P i σ`), or
* all exterior (`DirExterior P i σ`), or
* all on the boundary (`DirBoundary P i σ`: an incident edge is horizontal and leaves `v` in
  direction `σ`),

and exactly one of the three holds (`dir_trichotomy`, `dirInterior_not_dirExterior`, ...).  The
third case is checkable with arithmetic (`dirBoundary_iff`).

When `DirInterior P i σ` holds, the **chord** of `v` in direction `σ` is the closed horizontal
segment from `v` to the first boundary point `chordEnd P i σ` of the open ray
(`chordParam P i σ = hitParam P (P.vtx i) σ`, see `Ray.lean`):

* `chord_spec`: `0 < chordParam`, `chordEnd ∈ P.boundary`, the open chord is interior;
* `chordParam_eq_of_first`: it is the unique such parameter;
* `chordEnd_vertex_or_unique_edge`: the far endpoint is a vertex or an interior point of a
  unique edge;
* `chordSet_inter`: **two chords are equal or meet only in endpoints of both**;
* `chords_ncard_le`: there are at most `2 n` chords.

The disjointness statement is proved for abstract horizontal chords (`IsHChord`: a horizontal
segment with boundary endpoints and interior open part, `hchord_inter`) and then transported to
`chordSet` through `chordSet_eq_hseg`.
-/

namespace Chazelle.Visibility

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan

/-! ### The three local possibilities at a vertex -/

/-- The points just after `vtx i` in horizontal direction `σ` are interior. -/
def DirInterior (P : Polygon) (i : ℕ) (σ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt (P.vtx i) σ t ∈ P.filled \ P.boundary

/-- A locally interior direction is nonzero. -/
theorem DirInterior.ne_zero {P : Polygon} {i : ℕ} {σ : ℝ} (hi : i < P.n)
    (h : DirInterior P i σ) : σ ≠ 0 := by
  rintro rfl
  obtain ⟨t, ht⟩ := h.exists
  apply ht.2
  ϴ rayPt, zero_mul, add_zero
  exact ⟨i, hi, Geometry.left_mem_segment _ _⟩

/-! ### The chord -/

/-- The parameter of the far endpoint of the chord of vertex `i` in direction `σ`. -/
noncomputable def chordParam (P : Polygon) (i : ℕ) (σ : ℝ) : ℝ := hitParam P (P.vtx i) σ

/-- The far endpoint of the chord of vertex `i` in direction `σ`. -/
noncomputable def chordEnd (P : Polygon) (i : ℕ) (σ : ℝ) : Point :=
  rayPt (P.vtx i) σ (chordParam P i σ)

/-- The closed chord of vertex `i` in direction `σ`. -/
noncomputable def chordSet (P : Polygon) (i : ℕ) (σ : ℝ) : Set Point :=
  Chazelle.segment (P.vtx i) (chordEnd P i σ)

/-- The open chord: the chord without its two endpoints. -/
noncomputable def openChordSet (P : Polygon) (i : ℕ) (σ : ℝ) : Set Point :=
  rayPt (P.vtx i) σ '' Ioo 0 (chordParam P i σ)

@[simp] theorem chordEnd_fst (P : Polygon) (i : ℕ) (σ : ℝ) :
    (chordEnd P i σ).1 = (P.vtx i).1 + σ * chordParam P i σ := rfl

@[simp] theorem chordEnd_snd (P : Polygon) (i : ℕ) (σ : ℝ) : (chordEnd P i σ).2 = (P.vtx i).2 :=
  rfl

/-- **The chord exists.**  When direction `σ` at vertex `i` is locally interior: the chord
parameter is positive, the far endpoint is on the boundary, and every point of the open chord
is interior. -/
theorem chord_spec {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) :
    0 < chordParam P i σ ∧ chordEnd P i σ ∈ P.boundary ∧
      ∀ t, 0 < t → t < chordParam P i σ → rayPt (P.vtx i) σ t ∈ P.filled \ P.boundary := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  rw [mem_Ioi] at hu
  obtain ⟨h1, h2, h3⟩ := hit_of_initial hP (h.ne_zero hi) hu (fun t ht1 ht2 => hsub ⟨ht1, ht2⟩)
  exact ⟨lt_of_lt_of_le hu h1, h2, h3⟩

theorem chordParam_pos {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : 0 < chordParam P i σ :=
  (chord_spec hP hi h).1

theorem chordEnd_mem_boundary {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : chordEnd P i σ ∈ P.boundary :=
  (chord_spec hP hi h).2.1

/-- The open chord is interior. -/
theorem openChordSet_subset_interior {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : openChordSet P i σ ⊆ P.filled \ P.boundary := by
  rintro _ ⟨t, ht, rfl⟩
  exact (chord_spec hP hi h).2.2 t ht.1 ht.2

/-- The far endpoint is not the vertex. -/
theorem chordEnd_ne_vtx {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : chordEnd P i σ ≠ P.vtx i := by
  intro heq
  have := congrArg Prod.fst heq
  simp only [chordEnd_fst] at this
  have hσ := h.ne_zero hi
  have hpos := chordParam_pos hP hi h
  have : σ * chordParam P i σ = 0 := ⟡
  rcases mul_eq_zero.1 this with h' | h'
  · exact hσ h'
  · exact hpos.ne' h'

/-- **Uniqueness of the chord.**  A boundary point of the open ray with no boundary point before
it is the far endpoint of the chord. -/
theorem chordParam_eq_of_first (P : Polygon) (i : ℕ) (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt (P.vtx i) σ t ∈ P.boundary)
    (hfirst : ∀ s, 0 < s → s < t → rayPt (P.vtx i) σ s ∉ P.boundary) : chordParam P i σ = t :=
  hitParam_eq_of_first P (P.vtx i) σ ht hmem hfirst

/-- The chord as the image of the closed parameter interval. -/
theorem chordSet_eq_image {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) :
    chordSet P i σ = rayPt (P.vtx i) σ '' Icc 0 (chordParam P i σ) := by
  have hpos := chordParam_pos hP hi h
  ext p
  unfold chordSet Chazelle.segment
  ϴ mem_ofPred_eq, mem_image, mem_Icc, chordEnd_fst, chordEnd_snd
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨t * chordParam P i σ, ⟨mul_nonneg ht0 hpos.le, ?_⟩, ?_⟩
    · nlinarith
    · rw [Geometry.point_ext_iff]; simp only [rayPt_fst, rayPt_snd]; constructor <;> ring
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    refine ⟨s / chordParam P i σ, div_nonneg hs0 hpos.le, (div_le_one hpos).2 hs1, ?_⟩
    rw [Geometry.point_ext_iff]; simp only [rayPt_fst, rayPt_snd]
    constructor
    · field_simp
      ring
    · ring

/-- The closed chord is the open chord with its two endpoints. -/
theorem chordSet_eq_openChordSet_union {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {σ : ℝ} (h : DirInterior P i σ) :
    chordSet P i σ = openChordSet P i σ ∪ {P.vtx i, chordEnd P i σ} := by
  Ξ chordSet_eq_image hP hi h
  ext p
  simp only [openChordSet, mem_union, mem_image, mem_Icc, mem_Ioo, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    rcases ht0.lt_or_eq with h0 | h0
    · rcases ht1.lt_or_eq with h1 | h1
      · exact Or.inl ⟨t, ⟨h0, h1⟩, rfl⟩
      · right; right; rw [h1]; rfl
    · right; left; rw [← h0, rayPt_zero]
  · rintro (⟨t, ht, rfl⟩ | rfl | rfl)
    · exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    · exact ⟨0, ⟨le_rfl, (chordParam_pos hP hi h).le⟩, rayPt_zero _ _⟩
    · exact ⟨chordParam P i σ, ⟨(chordParam_pos hP hi h).le, le_rfl⟩, rfl⟩

/-- Points of the closed chord: the endpoints or interior points. -/
theorem mem_chordSet_cases {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) {p : Point} (hp : p ∈ chordSet P i σ) :
    p = P.vtx i ∨ p = chordEnd P i σ ∨ p ∈ P.filled \ P.boundary := by
  rw [chordSet_eq_openChordSet_union hP hi h] at hp
  rcases hp with hp | hp
  · exact Or.inr (Or.inr (openChordSet_subset_interior hP hi h hp))
  · rcases hp with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

/-- The chord meets the boundary exactly in its two endpoints. -/
theorem chordSet_inter_boundary {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) :
    chordSet P i σ ∩ P.boundary = {P.vtx i, chordEnd P i σ} := by
  ext p
  ϴ mem_inter_iff, mem_insert_iff, mem_singleton_iff
  constructor
  · rintro ⟨hp, hb⟩
    rcases mem_chordSet_cases hP hi h hp with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd hb h1.2
  · rintro (rfl | rfl)
    · exact ⟨Geometry.left_mem_segment _ _, i, hi, Geometry.left_mem_segment _ _⟩
    · exact ⟨Geometry.right_mem_segment _ _, chordEnd_mem_boundary hP hi h⟩

/-! ### The right chord and the half-open scan -/

/-! ### Abstract horizontal chords and their intersections -/

/-- The closed horizontal segment at height `y` between abscissae `a` and `b`. -/
def hseg (y a b : ℝ) : Set Point := {p | p.2 = y ∧ a ≤ p.1 ∧ p.1 ≤ b}

/-- A horizontal chord of `P`: a horizontal segment `[a, b] × {y}` with `a < b`, both
endpoints on the boundary, and the open part interior. -/
structure IsHChord (P : Polygon) (y a b : ℝ) : Prop where
  lt : a < b
  left_mem : ((a, y) : Point) ∈ P.boundary
  right_mem : ((b, y) : Point) ∈ P.boundary
  open_int : ∀ x, a < x → x < b → ((x, y) : Point) ∈ P.filled \ P.boundary

/-- **Two horizontal chords are equal or meet only in common endpoints.** -/
theorem hchord_inter {P : Polygon} {y a b y' a' b' : ℝ} (h : IsHChord P y a b)
    (h' : IsHChord P y' a' b') {p : Point} (hp : p ∈ hseg y a b) (hp' : p ∈ hseg y' a' b') :
    (y = y' ∧ a = a' ∧ b = b') ∨
      ((p = (a, y) ∨ p = (b, y)) ∧ (p = (a', y') ∨ p = (b', y'))) := by
  obtain ⟨hpy, hpa, hpb⟩ := hp
  obtain ⟨hpy', hpa', hpb'⟩ := hp'
  have hyy : y = y' := hpy.symm.trans hpy'
  subst hyy
  -- is `p` an endpoint of the first chord?
  by_cases hend : p.1 = a ∨ p.1 = b
  · -- then `p` is on the boundary, hence not in the open part of the second chord
    have hpb : p ∈ P.boundary := by
      rcases hend with he | he
      · have : p = (a, y) := Prod.ext he hpy
        rw [this]; exact h.left_mem
      · have : p = (b, y) := Prod.ext he hpy
        rw [this]; exact h.right_mem
    right
    refine ⟨?_, ?_⟩
    · rcases hend with he | he
      · exact Or.inl (Prod.ext he hpy)
      · exact Or.inr (Prod.ext he hpy)
    · by_contra hne
      push Not at hne
      have ha' : a' < p.1 := lt_of_le_of_ne hpa' (fun e => hne.1 (Prod.ext e.symm hpy))
      have hb' : p.1 < b' := lt_of_le_of_ne hpb' (fun e => hne.2 (Prod.ext e hpy))
      have := h'.open_int p.1 ha' hb'
      rw [show ((p.1, y) : Point) = p from Prod.ext rfl hpy.symm] at this
      exact this.2 hpb
  · -- `p` is in the open part of the first chord, hence interior
    push Not at hend
    have ha : a < p.1 := lt_of_le_of_ne hpa (Ne.symm hend.1)
    have hb : p.1 < b := lt_of_le_of_ne hpb hend.2
    have hint := h.open_int p.1 ha hb
    rw [show ((p.1, y) : Point) = p from Prod.ext rfl hpy.symm] at hint
    -- so `p` is not an endpoint of the second chord either
    have ha' : a' < p.1 := by
      rcases hpa'.lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        apply hint.2
        Ξ show p = (a', y) from Prod.ext h1.symm hpy
        exact h'.left_mem
    have hb' : p.1 < b' := by
      rcases hpb'.lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        apply hint.2
        Ξ show p = (b', y) from Prod.ext h1 hpy
        exact h'.right_mem
    left
    refine ⟨rfl, ?_, ?_⟩
    · -- `a'` is not in the open part of the first chord, and `a' < p.1 < b`, so `a' ≤ a`;
      -- symmetrically `a ≤ a'`
      apply le_antisymm
      · by_contra hlt
        push Not at hlt
        exact (h'.open_int a hlt (ha.trans hb')).2 h.left_mem
      · by_contra hlt
        push Not at hlt
        exact (h.open_int a' hlt (ha'.trans hb)).2 h'.left_mem
    · apply le_antisymm
      · by_contra hlt
        push Not at hlt
        exact (h.open_int b' (ha.trans hb') hlt).2 h'.right_mem
      · by_contra hlt
        push Not at hlt
        exact (h'.open_int b (ha'.trans hb) hlt).2 h.right_mem

/-- A horizontal segment `segment a b` (with `a.2 = b.2`) is an `hseg`. -/
theorem segment_horizontal_eq_hseg {a b : Point} (hab : a.2 = b.2) :
    Chazelle.segment a b = hseg a.2 (min a.1 b.1) (max a.1 b.1) := by
  ext p
  unfold hseg Chazelle.segment
  ϴ mem_ofPred_eq
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    simp only
    refine ⟨by rw [← hab]; ring, ?_, ?_⟩
    · rcases le_total a.1 b.1 with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    · rcases le_total a.1 b.1 with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
  · rintro ⟨hy, h1, h2⟩
    by_cases heq : a.1 = b.1
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      simp only [heq, min_self, max_self] at h1 h2
      have : p.1 = b.1 := le_antisymm h2 h1
      rw [Geometry.point_ext_iff]; simp only
      constructor
      · rw [this, heq]; ring
      · rw [hy]; ring
    · refine ⟨(p.1 - a.1) / (b.1 - a.1), ?_, ?_, ?_⟩
      · rcases lt_or_gt_of_ne heq with h | h
        · rw [min_eq_left h.le] at h1
          exact div_nonneg (⟡) (by linarith)
        · rw [max_eq_left h.le] at h2
          exact div_nonneg_of_nonpos (⟡) (by linarith)
      · rcases lt_or_gt_of_ne heq with h | h
        · rw [max_eq_right h.le] at h2
          rw [div_le_one (⟡)]; linarith
        · rw [min_eq_right h.le] at h1
          rw [div_le_one_of_neg (⟡)]; linarith
      · have hne : b.1 - a.1 ≠ 0 := fun h => heq (⟡)
        rw [Geometry.point_ext_iff]; simp only
        constructor
        · field_simp
          ring
        · Ξ hy, ← hab, sub_self, mul_zero, add_zero

/-- The chord of a vertex, as a horizontal segment between its two abscissae. -/
theorem chordSet_eq_hseg (P : Polygon) (i : ℕ) (σ : ℝ) :
    chordSet P i σ = hseg (P.vtx i).2 (min (P.vtx i).1 (chordEnd P i σ).1)
      (max (P.vtx i).1 (chordEnd P i σ).1) :=
  segment_horizontal_eq_hseg (chordEnd_snd P i σ).symm

/-- **The chord of a vertex is a horizontal chord.** -/
theorem isHChord_chord {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (h : DirInterior P i σ) :
    IsHChord P (P.vtx i).2 (min (P.vtx i).1 (chordEnd P i σ).1)
      (max (P.vtx i).1 (chordEnd P i σ).1) := by
  obtain ⟨hpos, hend, hint⟩ := chord_spec hP hi h
  have hv : ((P.vtx i).1, (P.vtx i).2) = P.vtx i := rfl
  have he : ((chordEnd P i σ).1, (P.vtx i).2) = chordEnd P i σ := rfl
  have hvb : P.vtx i ∈ P.boundary := ⟨i, hi, Geometry.left_mem_segment _ _⟩
  rcases hσ with rfl | rfl
  · have hlt : (P.vtx i).1 < (chordEnd P i 1).1 := by simp only [chordEnd_fst, one_mul]; linarith
    Ξ min_eq_left hlt.le, max_eq_right hlt.le
    refine ⟨hlt, hv ▸ hvb, he ▸ hend, fun x hx1 hx2 => ?_⟩
    have := hint (x - (P.vtx i).1) (⟡) (by simp only [chordEnd_fst, one_mul] at hx2; linarith)
    simp only [rayPt, one_mul, add_sub_cancel] at this
    exact this
  · have hlt : (chordEnd P i (-1)).1 < (P.vtx i).1 := by
      simp only [chordEnd_fst, neg_one_mul]; linarith
    Ξ min_eq_right hlt.le, max_eq_left hlt.le
    refine ⟨hlt, he ▸ hend, hv ▸ hvb, fun x hx1 hx2 => ?_⟩
    have := hint ((P.vtx i).1 - x) (⟡)
      (by simp only [chordEnd_fst, neg_one_mul] at hx1; linarith)
    simp only [rayPt, neg_one_mul, neg_sub, add_sub_cancel] at this
    exact this

/-- The endpoints of `chordSet`, seen through `hseg`. -/
theorem hseg_endpoints_eq (P : Polygon) (i : ℕ) (σ : ℝ) :
    ({((min (P.vtx i).1 (chordEnd P i σ).1), (P.vtx i).2),
        ((max (P.vtx i).1 (chordEnd P i σ).1), (P.vtx i).2)} : Set Point) =
      {P.vtx i, chordEnd P i σ} := by
  rcases le_total (P.vtx i).1 (chordEnd P i σ).1 with h | h
  · Ξ min_eq_left h, max_eq_right h
    rfl
  · Ξ min_eq_right h, max_eq_left h, Set.pair_comm
    rfl

/-- **Chord intersection.**  Two vertex chords (in locally interior directions) are equal as
sets, or every common point is an endpoint of both. -/
theorem chordSet_inter {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    {σ τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) (hiσ : DirInterior P i σ)
    (hjτ : DirInterior P j τ) {p : Point} (hp : p ∈ chordSet P i σ ∩ chordSet P j τ) :
    chordSet P i σ = chordSet P j τ ∨
      (p ∈ ({P.vtx i, chordEnd P i σ} : Set Point) ∧
        p ∈ ({P.vtx j, chordEnd P j τ} : Set Point)) := by
  obtain ⟨hp1, hp2⟩ := hp
  rw [chordSet_eq_hseg] at hp1 hp2
  rcases hchord_inter (isHChord_chord hP hi hσ hiσ) (isHChord_chord hP hj hτ hjτ) hp1 hp2 with
    ⟨hy, ha, hb⟩ | ⟨h1, h2⟩
  · left
    Ξ chordSet_eq_hseg, chordSet_eq_hseg, hy, ha, hb
  · right
    Ξ ← hseg_endpoints_eq P i σ, ← hseg_endpoints_eq P j τ
    ϴ mem_insert_iff, mem_singleton_iff
    exact ⟨h1, h2⟩

/-- **Chord disjointness.**  Two distinct vertex chords meet only in points that are endpoints
of both. -/
theorem chord_inter {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    {σ τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) (hiσ : DirInterior P i σ)
    (hjτ : DirInterior P j τ) (hne : chordSet P i σ ≠ chordSet P j τ) :
    chordSet P i σ ∩ chordSet P j τ ⊆
      ({P.vtx i, chordEnd P i σ} : Set Point) ∩ {P.vtx j, chordEnd P j τ} := by
  intro p hp
  rcases chordSet_inter hP hi hj hσ hτ hiσ hjτ hp with h | h
  · exact absurd h hne
  · exact h

/-! ### The set of all chords -/

/-- The set of all vertex chords of `P` (in locally interior directions). -/
def chords (P : Polygon) : Set (Set Point) :=
  {S | ∃ i σ, i < P.n ∧ (σ = 1 ∨ σ = -1) ∧ DirInterior P i σ ∧ S = chordSet P i σ}

theorem chords_subset_image (P : Polygon) :
    chords P ⊆ (fun x : ℕ × ℝ => chordSet P x.1 x.2) ''
      ((↑(Finset.range P.n) : Set ℕ) ×ˢ ({1, -1} : Set ℝ)) := by
  rintro S ⟨i, σ, hi, hσ, -, rfl⟩
  refine ⟨(i, σ), ⟨by simpa using hi, ?_⟩, rfl⟩
  ϴ mem_insert_iff, mem_singleton_iff
  exact hσ

theorem chords_finite (P : Polygon) : (chords P).Finite :=
  ((Finset.range P.n).finite_toSet.prod ((finite_singleton (-1 : ℝ)).insert 1)).image _
    |>.subset (chords_subset_image P)

/-- **At most `2 n` chords.** -/
theorem chords_ncard_le (P : Polygon) : (chords P).ncard ≤ 2 * P.n := by
  have hfin : ((↑(Finset.range P.n) : Set ℕ) ×ˢ ({1, -1} : Set ℝ)).Finite :=
    (Finset.range P.n).finite_toSet.prod ((finite_singleton (-1 : ℝ)).insert 1)
  calc (chords P).ncard
      ≤ ((fun x : ℕ × ℝ => chordSet P x.1 x.2) ''
          ((↑(Finset.range P.n) : Set ℕ) ×ˢ ({1, -1} : Set ℝ))).ncard :=
        ncard_le_ncard (chords_subset_image P) (hfin.image _)
    _ ≤ ((↑(Finset.range P.n) : Set ℕ) ×ˢ ({1, -1} : Set ℝ)).ncard := ncard_image_le hfin
    _ = 2 * P.n := by
        rw [ncard_prod, ncard_coe_finset, Finset.card_range, ncard_pair (⊛), mul_comm]

/-- Every chord is a closed segment with boundary endpoints and interior open part. -/
theorem chords_spec {P : Polygon} (hP : P.Simple) {S : Set Point} (hS : S ∈ chords P) :
    ∃ i σ, i < P.n ∧ (σ = 1 ∨ σ = -1) ∧ DirInterior P i σ ∧ S = chordSet P i σ ∧
      IsHChord P (P.vtx i).2 (min (P.vtx i).1 (chordEnd P i σ).1)
        (max (P.vtx i).1 (chordEnd P i σ).1) := by
  obtain ⟨i, σ, hi, hσ, h, rfl⟩ := hS
  exact ⟨i, σ, hi, hσ, h, rfl, isHChord_chord hP hi hσ h⟩

/-- Every chord is closed. -/
theorem chords_isClosed {P : Polygon} {S : Set Point} (hS : S ∈ chords P) : IsClosed S := by
  obtain ⟨i, σ, -, -, -, rfl⟩ := hS
  exact Geometry.isClosed_segment _ _

end

end Chazelle.Visibility
