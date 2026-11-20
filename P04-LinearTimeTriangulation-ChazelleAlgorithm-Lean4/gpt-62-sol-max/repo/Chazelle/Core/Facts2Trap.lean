module

public import Chazelle.Core.FactsChain

/-! Segment obstacles in an open box, horizontal chords, and the trapezoid data.
The construction and its degree bound are in `DownPhaseDegTrap` and `DownPhaseDegCount`,
including the case of horizontal obstacles and tied heights. -/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (point_ext)

namespace SegObs

/-! ## The setting -/

/-- The abscissa at height `y` of the line of the segment `s` (lower end `s.1`, upper end
`s.2`). -/
noncomputable def xAt (s : Point × Point) (y : ℝ) : ℝ :=
  s.1.1 + (y - s.1.2) / (s.2.2 - s.1.2) * (s.2.1 - s.1.1)

/-- The closed segment of `s`. -/
def seg (s : Point × Point) : Set Point := Chazelle.segment s.1 s.2

/-- The obstacle: the union of the segments. -/
def obs (S : Set (Point × Point)) : Set Point := ⋃ s ∈ S, seg s

/-- The domain: the open box minus the obstacle. -/
def dom (R : ℝ) (S : Set (Point × Point)) : Set Point := box R \ obs S

/-- A vertex: an endpoint of a segment. -/
def IsVert (S : Set (Point × Point)) (v : Point) : Prop := ∃ s ∈ S, v = s.1 ∨ v = s.2

/-- **The hypotheses on the obstacle segments.** -/
structure Good (R : ℝ) (S : Set (Point × Point)) : Prop where
  fin : S.Finite
  up : ∀ s ∈ S, s.1.2 < s.2.2
  inbox : ∀ s ∈ S, ∀ p ∈ seg s, |p.1| ≤ R ∧ |p.2| ≤ R
  sideL : ((-R, -R), (-R, R)) ∈ S
  sideR : ((R, -R), (R, R)) ∈ S
  cross : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ∀ p ∈ seg s, p ∈ seg s' → IsVert S p
  distinct : ∀ v w, IsVert S v → IsVert S w → |v.2| < R → v.2 = w.2 → v = w

/-- **The chord family contains the vertex chords**: a domain point seen horizontally from a
vertex (through the domain) lies on a chord of `G`. -/
def FullAt (R : ℝ) (S : Set (Point × Point)) (G : Set (Set Point)) : Prop :=
  ∀ v, IsVert S v → |v.2| < R → ∀ z ∈ dom R S, z.2 = v.2 →
    (∀ x, min v.1 z.1 < x → x < max v.1 z.1 → ((x, v.2) : Point) ∈ dom R S) → z ∈ ⋃₀ G

variable {R : ℝ} {S : Set (Point × Point)}

/-! ## Segments -/

section

variable {s : Point × Point} (hs : s.1.2 < s.2.2)

include hs in
theorem mem_seg_iff {p : Point} :
    p ∈ seg s ↔ s.1.2 ≤ p.2 ∧ p.2 ≤ s.2.2 ∧ p.1 = xAt s p.2 := by
  have hd := sub_pos.2 hs
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨by simp only; nlinarith, by simp only; nlinarith, ?_⟩
    simp only [xAt]
    field_simp
    ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(p.2 - s.1.2) / (s.2.2 - s.1.2), div_nonneg (by linarith) hd.le,
      (div_le_one hd).2 (by linarith), ?_⟩
    apply point_ext
    · assumption
    · simp only
      field_simp
      ring

theorem xAt_lo (s : Point × Point) : xAt s s.1.2 = s.1.1 := by simp [xAt]

include hs in
theorem xAt_hi : xAt s s.2.2 = s.2.1 := by
  have hd := (sub_pos.2 hs).ne'
  simp [xAt, div_self hd]

theorem continuous_xAt (s : Point × Point) : Continuous (xAt s) := by
  unfold xAt
  fun_prop

theorem lo_mem_seg (s : Point × Point) : s.1 ∈ seg s := Geometry.left_mem_segment _ _

theorem hi_mem_seg (s : Point × Point) : s.2 ∈ seg s := Geometry.right_mem_segment _ _

include hs in
/-- The point of the line of `s` at a height of its range lies on `s`. -/
theorem pt_mem_seg {y : ℝ} (h1 : s.1.2 ≤ y)
    (h2 : y ≤ s.2.2) : ((xAt s y, y) : Point) ∈ seg s :=
  (mem_seg_iff hs).2 ⟨h1, h2, rfl⟩

include hs in
/-- A point of `s` at its lowest height is its lower end. -/
theorem eq_lo {p : Point} (hp : p ∈ seg s)
    (h : p.2 = s.1.2) : p = s.1 := by
  obtain ⟨-, -, h3⟩ := (mem_seg_iff hs).1 hp
  exact point_ext (by rw [h3, h, xAt_lo]) h

include hs in
/-- A point of `s` at its highest height is its upper end. -/
theorem eq_hi {p : Point} (hp : p ∈ seg s)
    (h : p.2 = s.2.2) : p = s.2 := by
  obtain ⟨-, -, h3⟩ := (mem_seg_iff hs).1 hp
  exact point_ext (by rw [h3, h, xAt_hi hs]) h

end

theorem seg_subset_obs {s : Point × Point} (hs : s ∈ S) : seg s ⊆ obs S :=
  fun _ hp => mem_biUnion hs hp

theorem vert_mem_obs {v : Point} (hv : IsVert S v) : v ∈ obs S := by
  obtain ⟨s, hs, rfl | rfl⟩ := hv
  · exact seg_subset_obs hs (lo_mem_seg s)
  · exact seg_subset_obs hs (hi_mem_seg s)

theorem box_of_dom {p : Point} (hp : p ∈ dom R S) : |p.1| < R ∧ |p.2| < R := hp.1

theorem finite_verts (hf : S.Finite) : {v | IsVert S v}.Finite := by
  refine ((hf.image Prod.fst).union (hf.image Prod.snd)).subset ?_
  rintro v ⟨s, hs, rfl | rfl⟩
  · exact Or.inl ⟨s, hs, rfl⟩
  · tauto

/-- A hit point seen from a point off the chords is not a vertex. -/
theorem hit_not_vert {G : Set (Set Point)} (hfull : FullAt R S G) {q : Point}
    (hq : q ∈ dom R S) (hqG : q ∉ ⋃₀ G) {a : ℝ}
    (hin : ∀ x, min a q.1 < x → x < max a q.1 → ((x, q.2) : Point) ∈ dom R S) :
    ¬ IsVert S ((a, q.2) : Point) :=
  fun hv => hqG (hfull _ hv (box_of_dom hq).2 q hq rfl hin)

/-! ## The trapezoid data -/

/-- The trapezoid data of a point `q`: its walls `sL`, `sR` and the heights of the bottom and top
sides. -/
structure Trap (R : ℝ) (S : Set (Point × Point)) (q : Point) (sL sR : Point × Point)
    (y₁ y₂ : ℝ) : Prop where
  hL : sL ∈ S
  hR : sR ∈ S
  lt_q : xAt sL q.2 < q.1
  q_lt : q.1 < xAt sR q.2
  hseg : ∀ x, xAt sL q.2 < x → x < xAt sR q.2 → ((x, q.2) : Point) ∈ dom R S
  bot_lt : y₁ < q.2
  lt_top : q.2 < y₂
  botL : sL.1.2 ≤ y₁
  botR : sR.1.2 ≤ y₁
  topL : y₂ ≤ sL.2.2
  topR : y₂ ≤ sR.2.2
  no_vertex : ∀ v, IsVert S v → y₁ < v.2 → v.2 < y₂ → xAt sL v.2 ≤ v.1 → v.1 ≤ xAt sR v.2 →
    False
  top_vertex : ∃ v, IsVert S v ∧ v.2 = y₂ ∧
    (xAt sL y₂ ≤ xAt sR y₂ → xAt sL y₂ ≤ v.1 ∧ v.1 ≤ xAt sR y₂)
  bot_vertex : ∃ v, IsVert S v ∧ v.2 = y₁ ∧
    (xAt sL y₁ ≤ xAt sR y₁ → xAt sL y₁ ≤ v.1 ∧ v.1 ≤ xAt sR y₁)

/-! ## The trapezoid -/

/-- The open trapezoid between the lines of `sL` and `sR` and the heights `y₁ < y₂`. -/
def tr (sL sR : Point × Point) (y₁ y₂ : ℝ) : Set Point :=
  {p | y₁ < p.2 ∧ p.2 < y₂ ∧ xAt sL p.2 < p.1 ∧ p.1 < xAt sR p.2}

/-- The closed trapezoid. -/
def ctr (sL sR : Point × Point) (y₁ y₂ : ℝ) : Set Point :=
  {p | y₁ ≤ p.2 ∧ p.2 ≤ y₂ ∧ xAt sL p.2 ≤ p.1 ∧ p.1 ≤ xAt sR p.2}

theorem isOpen_tr (sL sR : Point × Point) (y₁ y₂ : ℝ) : IsOpen (tr sL sR y₁ y₂) := by
  have h1 : IsOpen {p : Point | y₁ < p.2} := isOpen_lt continuous_const continuous_snd
  have h2 : IsOpen {p : Point | p.2 < y₂} := isOpen_lt continuous_snd continuous_const
  have h3 := isOpen_lt ((continuous_xAt sL).comp continuous_snd) continuous_fst
  have h4 := isOpen_lt continuous_fst ((continuous_xAt sR).comp continuous_snd)
  have : tr sL sR y₁ y₂ = {p : Point | y₁ < p.2} ∩ ({p : Point | p.2 < y₂} ∩
      ({p : Point | xAt sL p.2 < p.1} ∩ {p : Point | p.1 < xAt sR p.2})) := by
    ext p; simp [tr]
  rw [this]
  exact h1.inter (h2.inter (h3.inter h4))

theorem isClosed_ctr (sL sR : Point × Point) (y₁ y₂ : ℝ) : IsClosed (ctr sL sR y₁ y₂) := by
  have h1 : IsClosed {p : Point | y₁ ≤ p.2} := isClosed_le continuous_const continuous_snd
  have h2 : IsClosed {p : Point | p.2 ≤ y₂} := isClosed_le continuous_snd continuous_const
  have h3 := isClosed_le ((continuous_xAt sL).comp continuous_snd) continuous_fst
  have h4 := isClosed_le continuous_fst ((continuous_xAt sR).comp continuous_snd)
  have : ctr sL sR y₁ y₂ = {p : Point | y₁ ≤ p.2} ∩ ({p : Point | p.2 ≤ y₂} ∩
      ({p : Point | xAt sL p.2 ≤ p.1} ∩ {p : Point | p.1 ≤ xAt sR p.2})) := by
    ext p; simp [ctr]
  rw [this]
  exact h1.inter (h2.inter (h3.inter h4))

theorem closure_tr_subset (sL sR : Point × Point) (y₁ y₂ : ℝ) :
    closure (tr sL sR y₁ y₂) ⊆ ctr sL sR y₁ y₂ :=
  closure_minimal (fun _ hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩)
    (isClosed_ctr sL sR y₁ y₂)

/-- The abscissa of the line of a segment is affine in the height. -/
theorem xAt_combo (s : Point × Point) {a b : ℝ} (hab : a + b = 1) (y y' : ℝ) :
    xAt s (a * y + b * y') = a * xAt s y + b * xAt s y' := by
  have e : ∀ z, xAt s z = s.1.1 + (z - s.1.2) * ((s.2.1 - s.1.1) / (s.2.2 - s.1.2)) := by
    intro z; unfold xAt; ring
  rw [e, e, e]
  have hb : b = 1 - a := by linarith
  subst hb
  ring

/-- Strict inequalities are preserved by convex combinations. -/
theorem combo_lt_combo {a b a' b' s s' : ℝ} (h1 : a < a') (h2 : b < b') (hs : 0 ≤ s)
    (hs' : 0 ≤ s') (h : s + s' = 1) : s * a + s' * b < s * a' + s' * b' := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · have : s' = 1 := by linarith
    subst this; linarith
  · nlinarith [mul_lt_mul_of_pos_left h1 hs, mul_le_mul_of_nonneg_left h2.le hs']

/-- The open trapezoid is convex. -/
theorem convex_tr (sL sR : Point × Point) (y₁ y₂ : ℝ) : Convex ℝ (tr sL sR y₁ y₂) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · show y₁ < (a • x + b • y).2
    simp only [Geometry.add_snd, Geometry.smul_snd]
    exact Jordan.combo_lt hx1 hy1 ha hb hab
  · show (a • x + b • y).2 < y₂
    simp only [Geometry.add_snd, Geometry.smul_snd]
    exact Jordan.combo_gt hx2 hy2 ha hb hab
  · show xAt sL (a • x + b • y).2 < (a • x + b • y).1
    simp only [Geometry.add_snd, Geometry.smul_snd, Geometry.add_fst, Geometry.smul_fst]
    rw [xAt_combo sL hab]
    exact combo_lt_combo hx3 hy3 ha hb hab
  · show (a • x + b • y).1 < xAt sR (a • x + b • y).2
    simp only [Geometry.add_snd, Geometry.smul_snd, Geometry.add_fst, Geometry.smul_fst]
    rw [xAt_combo sR hab]
    exact combo_lt_combo hx4 hy4 ha hb hab

/-- A zero of a continuous function between a point where it is positive and one where it is
not. -/
theorem exists_zero_between {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (ha : 0 < f a)
    (hb : f b ≤ 0) : ∃ c, f c = 0 ∧ min a b ≤ c ∧ c ≤ max a b ∧ c ≠ a := by
  rcases le_total a b with hab | hab
  · obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hab hf.continuousOn ⟨hb, ha.le⟩
    refine ⟨c, hfc, by simp_all, by simp_all,
      fun e => ?_⟩
    rw [e] at hfc; linarith
  · obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hf.continuousOn ⟨hb, ha.le⟩
    refine ⟨c, hfc, by simp_all, by simp_all,
      fun e => ?_⟩
    rw [e] at hfc; linarith

/-- Clamping a height into the range of a segment containing another height. -/
theorem exists_clamp {lo hi p q : ℝ} (hp1 : lo ≤ p) (hp2 : p ≤ hi) :
    ∃ y, lo ≤ y ∧ y ≤ hi ∧ min p q ≤ y ∧ y ≤ max p q ∧ (y = q ∨ y = lo ∨ y = hi) := by
  by_cases h1 : q < lo
  · refine ⟨lo, le_rfl, hp1.trans hp2, (min_le_right _ _).trans h1.le, hp1.trans (le_max_left _ _),
      Or.inr (Or.inl rfl)⟩
  · by_cases h2 : hi < q
    · refine ⟨hi, hp1.trans hp2, le_rfl, (min_le_left _ _).trans hp2,
        h2.le.trans (le_max_right _ _), Or.inr (Or.inr rfl)⟩
    · push Not at h1 h2
      exact ⟨q, h1, h2, min_le_right _ _, le_max_right _ _, Or.inl rfl⟩

namespace Trap

variable {q : Point} {sL sR : Point × Point} {y₁ y₂ : ℝ}

theorem q_mem (h : Trap R S q sL sR y₁ y₂) : q ∈ tr sL sR y₁ y₂ :=
  ⟨h.bot_lt, h.lt_top, h.lt_q, h.q_lt⟩

theorem y₁_lt_y₂ (h : Trap R S q sL sR y₁ y₂) : y₁ < y₂ := h.bot_lt.trans h.lt_top

end Trap

end SegObs

end

end Chazelle.Core
