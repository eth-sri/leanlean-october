module

public import Chazelle.Core.FactsChain
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-B, part 2: trapezoids of a box with segment obstacles (towards `FullDegSpec`, chain half)

A generic setting that covers the chain model of `Chazelle.Chain` (box, chain edges, slit) and
depends on nothing else about it:

* an open box `box R` and a finite set `S` of closed **non-horizontal segments** `s = (u, v)`
  (`u.2 < v.2`) in the closed box, including the two vertical sides of the box;
* the domain `dom R S = box R \ ⋃ S`;
* hypotheses (`Good`): two distinct segments meet only at **vertices** (endpoints of segments),
  and two vertices strictly inside the box's height range have distinct heights;
* a finite family `G` of horizontal chords of the domain containing every **vertex chord**
  (`FullAt`: every domain point seen horizontally from a vertex lies on a chord of `G`).

For a point `q` of the domain off the chords, the horizontal segment of `q` ends on two walls
`sL`, `sR` (segments of `S`, hit in their open parts), and the corridor between the lines of the
walls is obstructed above `q` at the first height `y₂` where a wall ends or a vertex lies in the
closed corridor (`y₁` below).  `Trap` records this data (`exists_trap`), and:

* `Trap.walls_lt`: the walls do not cross strictly between the heights;
* `Trap.no_obs`: no obstacle point lies strictly inside the corridor (so the open trapezoid
  `tr` is in the domain, `Trap.tr_subset_dom`);
* `Trap.top_side_vert`, `Trap.top_side_full`: an obstacle point on the open top side is a vertex,
  and every domain point of the open top side lies on a chord of `G` (seen from the top vertex);
  the same at the bottom;
* `Trap.region_subset`: the region of `q` in the map `G` lies in the trapezoid.

The degree bound (`deg_le_four`) is in `Chazelle.Core.Facts2TrapDeg`.
-/

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

theorem mem_seg_iff {s : Point × Point} (hs : s.1.2 < s.2.2) {p : Point} :
    p ∈ seg s ↔ s.1.2 ≤ p.2 ∧ p.2 ≤ s.2.2 ∧ p.1 = xAt s p.2 := by
  have hd  := sub_pos.2 hs
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨by sinl only, by sinl only, ?_⟩
    simp only [xAt]
    field_simp
    ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(p.2 - s.1.2) / (s.2.2 - s.1.2), div_nonneg (by linarith) hd.le,
      (div_le_one hd).2 (by linarith), ?_⟩
    apply point_ext
    · rw [h3]; simp only [xAt]
    · simp only
      field_simp
      ring

theorem xAt_lo (s : Point × Point) : xAt s s.1.2 = s.1.1 := by simp [xAt]

theorem xAt_hi {s : Point × Point} (hs : s.1.2 < s.2.2) : xAt s s.2.2 = s.2.1 := by
  have hd  := (sub_pos.2 hs).ne'
  simp only [xAt]
  rw [div_self hd]
  ring

theorem continuous_xAt (s : Point × Point) : Continuous (xAt s) := by
  unfold xAt
  fun_prop

theorem lo_mem_seg (s : Point × Point) : s.1 ∈ seg s := Geometry.left_mem_segment _ _

theorem hi_mem_seg (s : Point × Point) : s.2 ∈ seg s := Geometry.right_mem_segment _ _

/-- The point of the line of `s` at a height of its range lies on `s`. -/
theorem pt_mem_seg {s : Point × Point} (hs : s.1.2 < s.2.2) {y : ℝ} (h1 : s.1.2 ≤ y)
    (h2 : y ≤ s.2.2) : ((xAt s y, y) : Point) ∈ seg s :=
  (mem_seg_iff hs).2 ⟨h1, h2, rfl⟩

/-- A point of `s` at its lowest height is its lower end. -/
theorem eq_lo {s : Point × Point} (hs : s.1.2 < s.2.2) {p : Point} (hp : p ∈ seg s)
    (h : p.2 = s.1.2) : p = s.1 := by
  obtain ⟨-, -, h3⟩ := (mem_seg_iff hs).1 hp
  exact point_ext (by rw [h3, h, xAt_lo]) h

/-- A point of `s` at its highest height is its upper end. -/
theorem eq_hi {s : Point × Point} (hs : s.1.2 < s.2.2) {p : Point} (hp : p ∈ seg s)
    (h : p.2 = s.2.2) : p = s.2 := by
  obtain ⟨-, -, h3⟩ := (mem_seg_iff hs).1 hp
  exact point_ext (by rw [h3, h, xAt_hi hs]) h

theorem seg_subset_obs {s : Point × Point} (hs : s ∈ S) : seg s ⊆ obs S :=
  fun _ hp => mem_biUnion hs hp

theorem vert_mem_obs {v : Point} (hv : IsVert S v) : v ∈ obs S := by
  obtain ⟨s, hs, rfl | rfl⟩ := hv
  · exact seg_subset_obs hs (lo_mem_seg s)
  · exact seg_subset_obs hs (hi_mem_seg s)

theorem box_of_dom {p : Point} (hp : p ∈ dom R S) : |p.1| < R ∧ |p.2| < R := hp.1

theorem isOpen_dom (hS : Good R S) : IsOpen (dom R S) := by
  refine (Chain.isOpen_box R).sdiff ?_
  refine hS.fin.isClosed_biUnion fun s _ => Geometry.isClosed_segment _ _

theorem finite_verts (hS : Good R S) : {v | IsVert S v}.Finite := by
  refine ((hS.fin.image Prod.fst).union (hS.fin.image Prod.snd)).subset ?_
  rintro v ⟨s, hs, rfl | rfl⟩
  · exact Or.inl ⟨s, hs, rfl⟩
  · exact Or.inr ⟨s, hs, rfl⟩

/-- A point of the line of a segment of `S` in its height range is within the closed box. -/
theorem abs_xAt_le (hS : Good R S) {s : Point × Point} (hs : s ∈ S) {y : ℝ} (h1 : s.1.2 ≤ y)
    (h2 : y ≤ s.2.2) : |xAt s y| ≤ R :=
  (hS.inbox s hs _ (pt_mem_seg (hS.up s hs) h1 h2)).1

/-- An obstacle point that is not a vertex lies in the open part of a segment. -/
theorem wall_of_obs (hS : Good R S) {p : Point} (hp : p ∈ obs S) (hv : ¬ IsVert S p) :
    ∃ s ∈ S, s.1.2 < p.2 ∧ p.2 < s.2.2 ∧ p.1 = xAt s p.2 := by
  obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hp
  have hsu := hS.up s hs
  obtain ⟨h1, h2, h3⟩ := (mem_seg_iff hsu).1 hps
  refine ⟨s, hs, lt_of_le_of_ne h1 fun e => hv ⟨s, hs, Or.inl (eq_lo hsu hps e.symm)⟩,
    lt_of_le_of_ne h2 fun e => hv ⟨s, hs, Or.inr (eq_hi hsu hps e)⟩, h3⟩

/-! ## Horizontal hits -/

/-- The first obstacle to the east of a domain point. -/
theorem exists_hit_east (hS : Good R S) {q : Point} (hq : q ∈ dom R S) :
    ∃ b, q.1 < b ∧ ((b, q.2) : Point) ∉ dom R S ∧
      ∀ x, q.1 ≤ x → x < b → ((x, q.2) : Point) ∈ dom R S := by
  obtain ⟨s, hs, hin, hout⟩ := exists_first_exit (isOpen_dom hS) hq (R := R)
    (fun x hx => (abs_lt.1 (box_of_dom hx).1).2)
  refine ⟨q.1 + s, by linarith, hout, fun x h1 h2 => ?_⟩
  have := hin (x - q.1) ⟨by linarith, by linarith⟩
  simpa using this

/-- The first obstacle to the west of a domain point. -/
theorem exists_hit_west (hS : Good R S) {q : Point} (hq : q ∈ dom R S) :
    ∃ a, a < q.1 ∧ ((a, q.2) : Point) ∉ dom R S ∧
      ∀ x, a < x → x ≤ q.1 → ((x, q.2) : Point) ∈ dom R S := by
  set D' := {p : Point | ((-p.1, p.2) : Point) ∈ dom R S} with hD'
  have hD'o : IsOpen D' := (isOpen_dom hS).preimage (by fun_prop)
  have hq' : ((-q.1, q.2) : Point) ∈ D' := by simpa [hD'] using hq
  obtain ⟨s, hs, hin, hout⟩ := exists_first_exit hD'o hq' (R := R)
    (fun x hx => by
      have := (abs_lt.1 (box_of_dom hx).1).1
      simp only at this
      linarith)
  refine ⟨q.1 - s, by linarith, by simpa [hD', sub_eq_add_neg, add_comm] using hout,
    fun x h1 h2 => ?_⟩
  have := hin (q.1 - x) ⟨by linarith, by linarith⟩
  simp only [hD', mem_ofPred_eq] at this
  simpa using this

/-- A hit point is on the obstacle. -/
theorem hit_mem_obs (hS : Good R S) {q : Point} (hq : q ∈ dom R S) {a : ℝ}
    (hnot : ((a, q.2) : Point) ∉ dom R S)
    (hin : ∀ x, min a q.1 < x → x < max a q.1 → ((x, q.2) : Point) ∈ dom R S) :
    ((a, q.2) : Point) ∈ obs S := by
  obtain ⟨hq1, hq2⟩ := box_of_dom hq
  by_cases hab : |a| < R
  · by_contra hobs
    exact hnot ⟨⟨hab, hq2⟩, hobs⟩
  · push Not at hab
    have hq1' := abs_lt.1 hq1
    have hq2' := abs_lt.1 hq2
    rcases le_abs'.1 hab with ha | ha
    · -- `a ≤ -R`: the hit is on the left side
      have haR : a = -R := by
        by_contra hne
        have hlt  := lt_of_le_of_ne ha hne
        have := box_of_dom (hin (-R) (by
          rwx [min_eq_left (by linarith)]) (by
          rwli [max_eq_right (by linarith)]))
        simp only [abs_neg] at this
        exact lt_irrefl _ (this.1.trans_le (le_abs_self R))
      have hR0 : 0 < R := by linarith
      refine seg_subset_obs hS.sideL ((mem_seg_iff (by sil only)).2
        ⟨by sil only, by sil only, ?_⟩)
      simp [xAt, haR]
    · have haR : a = R := by
        by_contra hne
        have hlt  := lt_of_le_of_ne ha (Ne.symm hne)
        have := box_of_dom (hin R (by
          rwli [min_eq_right (by linarith)]) (by
          rwx [max_eq_left (by linarith)]))
        exact lt_irrefl _ (this.1.trans_le (le_abs_self R))
      have hR0 : 0 < R := by linarith
      refine seg_subset_obs hS.sideR ((mem_seg_iff (by sil only)).2
        ⟨by sil only, by sil only, ?_⟩)
      simp [xAt, haR]

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

/-- **Every domain point off the chords has trapezoid data.** -/
theorem exists_trap (hS : Good R S) {G : Set (Set Point)} (hfull : FullAt R S G) {q : Point}
    (hq : q ∈ dom R S) (hqG : q ∉ ⋃₀ G) : ∃ sL sR y₁ y₂, Trap R S q sL sR y₁ y₂ := by
  obtain ⟨a, ha, hanot, hain⟩ := exists_hit_west hS hq
  obtain ⟨b, hb, hbnot, hbin⟩ := exists_hit_east hS hq
  have hina : ∀ x, min a q.1 < x → x < max a q.1 → ((x, q.2) : Point) ∈ dom R S := by
    intro x h1 h2
    rw [min_eq_left ha.le] at h1; rw [max_eq_right ha.le] at h2
    exact hain x h1 h2.le
  have hinb : ∀ x, min b q.1 < x → x < max b q.1 → ((x, q.2) : Point) ∈ dom R S := by
    intro x h1 h2
    rw [min_eq_right hb.le] at h1; rw [max_eq_left hb.le] at h2
    exact hbin x h1.le h2
  obtain ⟨sL, hsL, hL1, hL2, hLx⟩ := wall_of_obs hS (hit_mem_obs hS hq hanot hina)
    (hit_not_vert hfull hq hqG hina)
  obtain ⟨sR, hsR, hR1, hR2, hRx⟩ := wall_of_obs hS (hit_mem_obs hS hq hbnot hinb)
    (hit_not_vert hfull hq hqG hinb)
  simp only at hL1 hL2 hLx hR1 hR2 hRx
  have hseg : ∀ x, a < x → x < b → ((x, q.2) : Point) ∈ dom R S := by
    intro x h1 h2
    rcases le_total x q.1 with h | h
    · exact hain x h1 h
    · exact hbin x h h2
  -- the vertices at the height of `q` in the closed segment
  have hnoq : ∀ v, IsVert S v → v.2 = q.2 → a ≤ v.1 → v.1 ≤ b → False := by
    intro v hv hvq h1 h2
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · have := hseg v.1 h1 h2
        rw [show ((v.1, q.2) : Point) = v from point_ext rfl hvq.symm] at this
        exact this.2 (vert_mem_obs hv)
      · exact hit_not_vert hfull hq hqG hinb
          (by rwx [show ((b, q.2) : Point) = v from point_ext h2.symm hvq.symm])
    · exact hit_not_vert hfull hq hqG hina
        (by rwx [show ((a, q.2) : Point) = v from point_ext h1 hvq.symm])
  have hV := finite_verts hS
  have hup := hS.up sL hsL
  have hupR := hS.up sR hsR
  -- the top height
  set C₂ : Set ℝ := {y | ∃ v, IsVert S v ∧ v.2 = y ∧ q.2 < y ∧ xAt sL y ≤ v.1 ∧ v.1 ≤ xAt sR y} ∪
    {sL.2.2, sR.2.2} with hC₂
  have hC₂f : C₂.Finite := by
    refine Set.Finite.union ?_ ((finite_singleton _).insert _)
    refine (hV.image fun v => v.2).subset ?_
    rintro y ⟨v, hv, rfl, -⟩
    exact ⟨v, hv, rfl⟩
  obtain ⟨y₂, hy₂C, hmin⟩ := Set.exists_min_image C₂ id hC₂f ⟨sL.2.2, Or.inr (Or.inl rfl)⟩
  have hall₂ : ∀ y ∈ C₂, q.2 < y := by
    rintro y (⟨v, -, rfl, h, -⟩ | h)
    · exact h
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact hL2
      · exact hR2
  -- the bottom height
  set C₁ : Set ℝ := {y | ∃ v, IsVert S v ∧ v.2 = y ∧ y < q.2 ∧ xAt sL y ≤ v.1 ∧ v.1 ≤ xAt sR y} ∪
    {sL.1.2, sR.1.2} with hC₁
  have hC₁f : C₁.Finite := by
    refine Set.Finite.union ?_ ((finite_singleton _).insert _)
    refine (hV.image fun v => v.2).subset ?_
    rintro y ⟨v, hv, rfl, -⟩
    exact ⟨v, hv, rfl⟩
  obtain ⟨y₁, hy₁C, hmax⟩ := Set.exists_max_image C₁ id hC₁f ⟨sL.1.2, Or.inr (Or.inl rfl)⟩
  have hall₁ : ∀ y ∈ C₁, y < q.2 := by
    rintro y (⟨v, -, rfl, h, -⟩ | h)
    · exact h
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact hL1
      · exact hR1
  refine ⟨sL, sR, y₁, y₂, ⟨hsL, hsR, by rwx [← hLx], by rwx [← hRx],
    by rwx [← hLx, ← hRx], hall₁ _ hy₁C, hall₂ _ hy₂C,
    hmax _ (Or.inr (Or.inl rfl)), hmax _ (Or.inr (Or.inr rfl)),
    hmin _ (Or.inr (Or.inl rfl)), hmin _ (Or.inr (Or.inr rfl)), ?_, ?_, ?_⟩⟩
  · intro v hv h1 h2 h3 h4
    rcases lt_trichotomy v.2 q.2 with hlt | heq | hgt
    · have := hmax _ (Or.inl ⟨v, hv, rfl, hlt, h3, h4⟩)
      simp only [id] at this
      linarith
    · rw [heq, ← hLx] at h3
      rw [heq, ← hRx] at h4
      exact hnoq v hv heq h3 h4
    · have := hmin _ (Or.inl ⟨v, hv, rfl, hgt, h3, h4⟩)
      simp only [id] at this
      linarith
  · rcases hy₂C with ⟨v, hv, hvy, -, h3, h4⟩ | h
    · exact ⟨v, hv, hvy, fun _ => ⟨hvy ▸ h3, hvy ▸ h4⟩⟩
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact ⟨sL.2, ⟨sL, hsL, Or.inr rfl⟩, rfl, fun hle => ⟨by rw [xAt_hi hup],
          by rwx [← xAt_hi hup]⟩⟩
      · exact ⟨sR.2, ⟨sR, hsR, Or.inr rfl⟩, rfl, fun hle => ⟨by rwx [← xAt_hi hupR],
          by rw [xAt_hi hupR]⟩⟩
  · rcases hy₁C with ⟨v, hv, hvy, -, h3, h4⟩ | h
    · exact ⟨v, hv, hvy, fun _ => ⟨hvy ▸ h3, hvy ▸ h4⟩⟩
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact ⟨sL.1, ⟨sL, hsL, Or.inl rfl⟩, rfl, fun hle => ⟨by rw [xAt_lo],
          by rwx [← xAt_lo sL]⟩⟩
      · exact ⟨sR.1, ⟨sR, hsR, Or.inl rfl⟩, rfl, fun hle => ⟨by rwx [← xAt_lo sR],
          by rw [xAt_lo]⟩⟩

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
  have h3 : IsOpen {p : Point | xAt sL p.2 < p.1} :=
    isOpen_lt ((continuous_xAt sL).comp continuous_snd) continuous_fst
  have h4 : IsOpen {p : Point | p.1 < xAt sR p.2} :=
    isOpen_lt continuous_fst ((continuous_xAt sR).comp continuous_snd)
  have : tr sL sR y₁ y₂ = {p : Point | y₁ < p.2} ∩ ({p : Point | p.2 < y₂} ∩
      ({p : Point | xAt sL p.2 < p.1} ∩ {p : Point | p.1 < xAt sR p.2})) := by
    ext p; simp [tr]
  rw [this]
  exact h1.inter (h2.inter (h3.inter h4))

theorem isClosed_ctr (sL sR : Point × Point) (y₁ y₂ : ℝ) : IsClosed (ctr sL sR y₁ y₂) := by
  have h1 : IsClosed {p : Point | y₁ ≤ p.2} := isClosed_le continuous_const continuous_snd
  have h2 : IsClosed {p : Point | p.2 ≤ y₂} := isClosed_le continuous_snd continuous_const
  have h3 : IsClosed {p : Point | xAt sL p.2 ≤ p.1} :=
    isClosed_le ((continuous_xAt sL).comp continuous_snd) continuous_fst
  have h4 : IsClosed {p : Point | p.1 ≤ xAt sR p.2} :=
    isClosed_le continuous_fst ((continuous_xAt sR).comp continuous_snd)
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
    intro z; ufring xAt
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
    refine ⟨c, hfc, by rw [min_eq_left hab]; exact hc.1, by rw [max_eq_right hab]; exact hc.2,
      fun e => ?_⟩
    rwli [e] at hfc
  · obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hf.continuousOn ⟨hb, ha.le⟩
    refine ⟨c, hfc, by rw [min_eq_right hab]; exact hc.1, by rw [max_eq_left hab]; exact hc.2,
      fun e => ?_⟩
    rwli [e] at hfc

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

/-- A point on the left wall line at a height of the trapezoid is an obstacle point. -/
theorem memL (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2)
    (h2 : p.2 ≤ y₂) (hx : p.1 = xAt sL p.2) : p ∈ obs S :=
  seg_subset_obs h.hL ((mem_seg_iff (hS.up sL h.hL)).2 ⟨h.botL.trans h1, h2.trans h.topL, hx⟩)

/-- A point on the right wall line at a height of the trapezoid is an obstacle point. -/
theorem memR (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2)
    (h2 : p.2 ≤ y₂) (hx : p.1 = xAt sR p.2) : p ∈ obs S :=
  seg_subset_obs h.hR ((mem_seg_iff (hS.up sR h.hR)).2 ⟨h.botR.trans h1, h2.trans h.topR, hx⟩)

/-- **The walls do not cross** strictly between the heights. -/
theorem walls_lt (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {y : ℝ} (h1 : y₁ < y)
    (h2 : y < y₂) : xAt sL y < xAt sR y := by
  by_contra hle
  push Not at hle
  have hne : sL ≠ sR := by
    intro e; rw [e] at h; exact lt_irrefl _ (h.lt_q.trans h.q_lt)
  obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between (f := fun y => xAt sR y - xAt sL y)
    ((continuous_xAt sR).sub (continuous_xAt sL)) (a := q.2) (b := y)
    (show (0 : ℝ) < xAt sR q.2 - xAt sL q.2 by have := h.lt_q; have := h.q_lt; linarith)
    (show xAt sR y - xAt sL y ≤ 0 by linarith)
  have hc'  := hc
  have hc1'  := lt_of_lt_of_le (lt_min h.bot_lt h1) hc1
  have hc2'  := lt_of_le_of_lt hc2 (max_lt h.lt_top h2)
  have hmL  := pt_mem_seg (hS.up sL h.hL) (h.botL.trans hc1'.le) (hc2'.le.trans h.topL)
  have hmR : ((xAt sL c, c) : Point) ∈ seg sR := by
    rw [show xAt sL c = xAt sR c by linarith]
    exact pt_mem_seg (hS.up sR h.hR) (h.botR.trans hc1'.le) (hc2'.le.trans h.topR)
  exact h.no_vertex _ (hS.cross sL h.hL sR h.hR hne _ hmL hmR) hc1' hc2' le_rfl
    (show xAt sL c ≤ xAt sR c by linarith)

/-- **No obstacle point strictly inside the corridor.** -/
theorem no_obs (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {p : Point} (hp : p ∈ obs S)
    (h1 : y₁ < p.2) (h2 : p.2 < y₂) (h3 : xAt sL p.2 < p.1) (h4 : p.1 < xAt sR p.2) : False := by
  obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hp
  have hsu := hS.up s hs
  obtain ⟨hp1, hp2, hpx⟩ := (mem_seg_iff hsu).1 hps
  obtain ⟨y', hy'1, hy'2, hb1, hb2, hcases⟩ := exists_clamp (q := q.2) hp1 hp2
  have hy'in1  := lt_of_lt_of_le (lt_min h1 h.bot_lt) hb1
  have hy'in2  := lt_of_le_of_lt hb2 (max_lt h2 h.lt_top)
  have hp'  := pt_mem_seg hsu hy'1 hy'2
  by_cases hin : xAt sL y' < xAt s y' ∧ xAt s y' < xAt sR y'
  · rcases hcases with he | he | he
    · have := h.hseg (xAt s y') (he ▸ hin.1) (he ▸ hin.2)
      rw [← he] at this
      exact this.2 (seg_subset_obs hs hp')
    · exact h.no_vertex _ ⟨s, hs, Or.inl (eq_lo hsu hp' he)⟩ hy'in1 hy'in2 hin.1.le hin.2.le
    · exact h.no_vertex _ ⟨s, hs, Or.inr (eq_hi hsu hp' he)⟩ hy'in1 hy'in2 hin.1.le hin.2.le
  · rw [not_and_or, not_lt, not_lt] at hin
    rcases hin with hle | hge
    · have hne : s ≠ sL := by
        intro e; subst e; linarith
      obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between (f := fun y => xAt s y - xAt sL y)
        ((continuous_xAt s).sub (continuous_xAt sL)) (a := p.2) (b := y')
        (show (0 : ℝ) < xAt s p.2 - xAt sL p.2 by linarith)
        (show xAt s y' - xAt sL y' ≤ 0 by linarith)
      have hc'  := hc
      have hc1'  := lt_of_lt_of_le (lt_min h1 hy'in1) hc1
      have hc2'  := lt_of_le_of_lt hc2 (max_lt h2 hy'in2)
      have hcs1  := le_trans (le_min hp1 hy'1) hc1
      have hcs2  := le_trans hc2 (max_le hp2 hy'2)
      have hmS : ((xAt sL c, c) : Point) ∈ seg s := by
        rw [show xAt sL c = xAt s c by linarith]
        exact pt_mem_seg hsu hcs1 hcs2
      have hmL  := pt_mem_seg (hS.up sL h.hL) (h.botL.trans hc1'.le) (hc2'.le.trans h.topL)
      exact h.no_vertex _ (hS.cross s hs sL h.hL hne _ hmS hmL) hc1' hc2' le_rfl
        (h.walls_lt hS hc1' hc2').le
    · have hne : s ≠ sR := by
        intro e; subst e; linarith
      obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between (f := fun y => xAt sR y - xAt s y)
        ((continuous_xAt sR).sub (continuous_xAt s)) (a := p.2) (b := y')
        (show (0 : ℝ) < xAt sR p.2 - xAt s p.2 by linarith)
        (show xAt sR y' - xAt s y' ≤ 0 by linarith)
      have hc'  := hc
      have hc1'  := lt_of_lt_of_le (lt_min h1 hy'in1) hc1
      have hc2'  := lt_of_le_of_lt hc2 (max_lt h2 hy'in2)
      have hcs1  := le_trans (le_min hp1 hy'1) hc1
      have hcs2  := le_trans hc2 (max_le hp2 hy'2)
      have hmS : ((xAt sR c, c) : Point) ∈ seg s := by
        rw [show xAt sR c = xAt s c by linarith]
        exact pt_mem_seg hsu hcs1 hcs2
      have hmR  := pt_mem_seg (hS.up sR h.hR) (h.botR.trans hc1'.le) (hc2'.le.trans h.topR)
      exact h.no_vertex _ (hS.cross s hs sR h.hR hne _ hmS hmR) hc1' hc2'
        (h.walls_lt hS hc1' hc2').le le_rfl

/-- The trapezoid lies in the domain. -/
theorem tr_subset_dom (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) :
    tr sL sR y₁ y₂ ⊆ dom R S := by
  rintro p ⟨h1, h2, h3, h4⟩
  have hlo := (abs_le.1 (hS.inbox sL h.hL _ (lo_mem_seg sL)).2).1
  have hhi := (abs_le.1 (hS.inbox sL h.hL _ (hi_mem_seg sL)).2).2
  have hL := (abs_le.1 (abs_xAt_le hS h.hL (h.botL.trans h1.le) (h2.le.trans h.topL))).1
  have hR := (abs_le.1 (abs_xAt_le hS h.hR (h.botR.trans h1.le) (h2.le.trans h.topR))).2
  have hbL := h.botL
  have htL := h.topL
  refine ⟨⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩,
    fun hp => h.no_obs hS hp h1 h2 h3 h4⟩

/-- **An obstacle point on the open top side is a vertex.** -/
theorem top_side_vert (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {w : Point}
    (hw : w ∈ obs S) (hwy : w.2 = y₂) (h3 : xAt sL y₂ < w.1) (h4 : w.1 < xAt sR y₂) :
    IsVert S w := by
  by_contra hv
  obtain ⟨s, hs, hs1, hs2, hsx⟩ := wall_of_obs hS hw hv
  rw [hwy] at hs1 hs2 hsx
  have hev : ∀ᶠ y in 𝓝 y₂, xAt sL y < xAt s y ∧ xAt s y < xAt sR y :=
    ((continuous_xAt sL).continuousAt.eventually_lt (continuous_xAt s).continuousAt
      (by rwx [← hsx])).and
    ((continuous_xAt s).continuousAt.eventually_lt (continuous_xAt sR).continuousAt
      (by rwx [← hsx]))
  have hlt : max y₁ s.1.2 < y₂ := max_lt h.y₁_lt_y₂ hs1
  have e1 : ∀ᶠ y in 𝓝[<] y₂, y ∈ Ioo (max y₁ s.1.2) y₂ := Ioo_mem_nhdsLT hlt
  obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := (e1.and (nhdsWithin_le_nhds hev)).exists
  exact h.no_obs hS (seg_subset_obs hs (pt_mem_seg (hS.up s hs) (le_of_max_le_right hy1.le)
    (hy2.le.trans hs2.le))) (lt_of_le_of_lt (le_max_left _ _) hy1) hy2 hy3 hy4

/-- **An obstacle point on the open bottom side is a vertex.** -/
theorem bot_side_vert (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {w : Point}
    (hw : w ∈ obs S) (hwy : w.2 = y₁) (h3 : xAt sL y₁ < w.1) (h4 : w.1 < xAt sR y₁) :
    IsVert S w := by
  by_contra hv
  obtain ⟨s, hs, hs1, hs2, hsx⟩ := wall_of_obs hS hw hv
  rw [hwy] at hs1 hs2 hsx
  have hev : ∀ᶠ y in 𝓝 y₁, xAt sL y < xAt s y ∧ xAt s y < xAt sR y :=
    ((continuous_xAt sL).continuousAt.eventually_lt (continuous_xAt s).continuousAt
      (by rwx [← hsx])).and
    ((continuous_xAt s).continuousAt.eventually_lt (continuous_xAt sR).continuousAt
      (by rwx [← hsx]))
  have hlt : y₁ < min y₂ s.2.2 := lt_min h.y₁_lt_y₂ hs2
  have e1 : ∀ᶠ y in 𝓝[>] y₁, y ∈ Ioo y₁ (min y₂ s.2.2) := Ioo_mem_nhdsGT hlt
  obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := (e1.and (nhdsWithin_le_nhds hev)).exists
  exact h.no_obs hS (seg_subset_obs hs (pt_mem_seg (hS.up s hs) (hs1.le.trans hy1.le)
    (le_of_lt (lt_of_lt_of_le hy2 (min_le_right _ _))))) hy1
    (lt_of_lt_of_le hy2 (min_le_left _ _)) hy3 hy4

/-- **A domain point of the open top side lies on a chord of `G`**: it is seen horizontally from
the top vertex. -/
theorem top_side_full (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {G : Set (Set Point)}
    (hfull : FullAt R S G) {p : Point} (hp : p ∈ dom R S) (hpy : p.2 = y₂)
    (h3 : xAt sL y₂ < p.1) (h4 : p.1 < xAt sR y₂) : p ∈ ⋃₀ G := by
  obtain ⟨v, hv, hvy, hvx⟩ := h.top_vertex
  obtain ⟨hv1, hv2⟩ := hvx (by linarith)
  have hy2R  := hpy ▸ (box_of_dom hp).2
  have hin  := h.y₁_lt_y₂.le
  have hLb := (abs_le.1 (abs_xAt_le hS h.hL (h.botL.trans hin) h.topL)).1
  have hRb := (abs_le.1 (abs_xAt_le hS h.hR (h.botR.trans hin) h.topR)).2
  refine hfull v hv (hvy ▸ hy2R) p hp (hpy.trans hvy.symm) fun x hx1 hx2 => ?_
  have hxL  := lt_of_le_of_lt (le_min hv1 h3.le) hx1
  have hxR  := lt_of_lt_of_le hx2 (max_le hv2 h4.le)
  rw [hvy]
  refine ⟨⟨abs_lt.2 ⟨by linarith, by linarith⟩, hy2R⟩, fun hobs => ?_⟩
  have hw := h.top_side_vert hS hobs rfl hxL hxR
  have he := hS.distinct v _ hv hw (hvy ▸ hy2R) hvy
  have hx : v.1 = x := by rw [he]
  rw [hx] at hx1 hx2
  rcases le_total x p.1 with hh | hh
  · rw [min_eq_left hh] at hx1; exact lt_irrefl _ hx1
  · rw [max_eq_left hh] at hx2; exact lt_irrefl _ hx2

/-- **A domain point of the open bottom side lies on a chord of `G`.** -/
theorem bot_side_full (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {G : Set (Set Point)}
    (hfull : FullAt R S G) {p : Point} (hp : p ∈ dom R S) (hpy : p.2 = y₁)
    (h3 : xAt sL y₁ < p.1) (h4 : p.1 < xAt sR y₁) : p ∈ ⋃₀ G := by
  obtain ⟨v, hv, hvy, hvx⟩ := h.bot_vertex
  obtain ⟨hv1, hv2⟩ := hvx (by linarith)
  have hy1R  := hpy ▸ (box_of_dom hp).2
  have hin  := h.y₁_lt_y₂.le
  have hLb := (abs_le.1 (abs_xAt_le hS h.hL h.botL (hin.trans h.topL))).1
  have hRb := (abs_le.1 (abs_xAt_le hS h.hR h.botR (hin.trans h.topR))).2
  refine hfull v hv (hvy ▸ hy1R) p hp (hpy.trans hvy.symm) fun x hx1 hx2 => ?_
  have hxL  := lt_of_le_of_lt (le_min hv1 h3.le) hx1
  have hxR  := lt_of_lt_of_le hx2 (max_le hv2 h4.le)
  rw [hvy]
  refine ⟨⟨abs_lt.2 ⟨by linarith, by linarith⟩, hy1R⟩, fun hobs => ?_⟩
  have hw := h.bot_side_vert hS hobs rfl hxL hxR
  have he := hS.distinct v _ hv hw (hvy ▸ hy1R) hvy
  have hx : v.1 = x := by rw [he]
  rw [hx] at hx1 hx2
  rcases le_total x p.1 with hh | hh
  · rw [min_eq_left hh] at hx1; exact lt_irrefl _ hx1
  · rw [max_eq_left hh] at hx2; exact lt_irrefl _ hx2

/-- **The region of `q` lies in its trapezoid.** -/
theorem region_subset (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {G : Set (Set Point)}
    (hfull : FullAt R S G) (hq : q ∈ freeIn (dom R S) G) :
    connectedComponentIn (freeIn (dom R S) G) q ⊆ tr sL sR y₁ y₂ := by
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset (isOpen_tr _ _ _ _)
    ⟨q, mem_connectedComponentIn hq, h.q_mem⟩ ?_
  rintro p ⟨hpc, hpU⟩
  have hpf : p ∈ freeIn (dom R S) G := connectedComponentIn_subset _ _ hpU
  obtain ⟨hp1, hp2, hp3, hp4⟩ := closure_tr_subset _ _ _ _ hpc
  have hpD  := hpf.1
  have hpG  := hpf.2
  have hx3 : xAt sL p.2 < p.1 := lt_of_le_of_ne hp3 fun e => hpD.2 (h.memL hS hp1 hp2 e.symm)
  have hx4 : p.1 < xAt sR p.2 := lt_of_le_of_ne hp4 fun e => hpD.2 (h.memR hS hp1 hp2 e)
  refine ⟨lt_of_le_of_ne hp1 fun e => ?_, lt_of_le_of_ne hp2 fun e => ?_, hx3, hx4⟩
  · exact hpG (h.bot_side_full hS hfull hpD e.symm (e ▸ hx3) (e ▸ hx4))
  · exact hpG (h.top_side_full hS hfull hpD e (e ▸ hx3) (e ▸ hx4))

end Trap

end SegObs

end

end Chazelle.Core
