module

public import Chazelle.MacT
public import Chazelle.Core.SpecNF

section
set_option hygiene false
local macro "zqbew" : tactic => `(tactic| (have hc1' : ztsnj := lt_of_lt_of_le ztodb hc1
                                           have hc2' : ztsdu := lt_of_le_of_lt hc2 ztodh
                                           have hcs1 : ztsma := le_trans ztocs hc1
                                           have hcs2 : ztsdy := le_trans hc2 ztodg))
local macro "zqbex" : tactic => `(tactic| (refine Set.Finite.union ?_ ztifb
                                           refine (hV.image fun v => v.2).subset ?_
                                           rintro y ⟨v, hv, rfl, -⟩
                                           grind))
local macro "zqbey" : tactic => `(tactic| (simp only [mem_insert_iff, mem_singleton_iff] at h
                                           rcases h with rfl | rfl))
local macro "zqbez" : tactic => `(tactic| (by_contra hv
                                           obtain ⟨s, hs, hs1, hs2, hsx⟩ := wall_of_obs hS hw hv
                                           rw [hwy] at hs1 hs2 hsx))
local macro "zqbfa" : tactic => `(tactic| obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := (e1.and ztqtw).exists)
local macro "zqbfb" : tactic => `(tactic| refine hfull v hv by_simp_all p hp (hpy.trans hvy.symm) fun x hx1 hx2 => ?_)
local macro "zqbfc" : tactic => `(tactic| rintro y (⟨v, -, rfl, h, -⟩ | h))
set_option hygiene true

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
noncomputable def xAt (s : Point × Point) (y : ℝ) : ℝ :=
  s.1.1 + (y - s.1.2) / ztken * ztkem

/-- The closed segment of `s`. -/
def seg (s : Point × Point) : Set Point := Chazelle.segment s.1 s.2

/-- The obstacle: the union of the segments. -/
def obs (S : Set ztdga) : Set Point := ⋃ s ∈ S, seg s

/-- The domain: the open box minus the obstacle. -/
def dom (R : ℝ) (S : Set ztdga) : Set Point := box R \ obs S

/-- A vertex: an endpoint of a segment. -/
def IsVert (S : Set ztdga) (v : Point) : Prop := ∃ s ∈ S, v = s.1 ∨ v = s.2

/-- **The hypotheses on the obstacle segments.** -/
structure Good (R : ℝ) (S : Set ztdga) : Prop where
  fin : S.Finite
  up : ∀ s ∈ S, s.1.2 < s.2.2
  inbox : ∀ s ∈ S, ∀ p ∈ seg s, |p.1| ≤ R ∧ |p.2| ≤ R
  sideL : zthpy ∈ S
  sideR : ztipe ∈ S
  cross : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ∀ p ∈ seg s, p ∈ seg s' → IsVert S p
  distinct : ∀ v w, IsVert S v → IsVert S w → |v.2| < R → v.2 = w.2 → v = w

/-- **The chord family contains the vertex chords**: a domain point seen horizontally from a
vertex (through the domain) lies on a chord of `G`. -/
def FullAt (R : ℝ) (S : Set ztdga) (G : Set ztf) : Prop :=
  ∀ v, IsVert S v → |v.2| < R → ∀ z ∈ dom R S, z.2 = v.2 →
    (∀ x, min v.1 z.1 < x → x < max v.1 z.1 → (ztudy : Point) ∈ dom R S) → z ∈ ⋃₀ G
variable {R : ℝ} {S : Set (Point × Point)}

/-! ## Segments -/
variable {s : Point × Point}
theorem mem_seg_iff (hs : s.1.2 < s.2.2) {p : Point} :
    p ∈ seg s ↔ s.1.2 ≤ p.2 ∧ p.2 ≤ s.2.2 ∧ p.1 = xAt s p.2 := by
  have hd := sub_pos.2 hs
  constructor
  · zuly
    refine ⟨by_simp_all, by simp only; nlinarith, ?_⟩
    zulsk
    grind
  · zuei
    refine ⟨(p.2 - s.1.2) / ztken, div_nonneg by_linarith hd.le,
      (div_le_one hd).2 by_linarith, ?_⟩
    zubjw
    · tauto
    grind
theorem xAt_lo (s : Point × Point) : xAt s s.1.2 = s.1.1 := by zuoew
theorem xAt_hi (hs : s.1.2 < s.2.2) : xAt s s.2.2 = s.2.1 := by
  have hd : s.2.2 - s.1.2 ≠ 0 := by_grind
  zulsk
  simp_all
theorem continuous_xAt (s : Point × Point) : Continuous (xAt s) := by
  zulve
  fun_prop
theorem lo_mem_seg (s : Point × Point) : s.1 ∈ seg s := Geometry.left_mem_segment _ _
theorem hi_mem_seg (s : Point × Point) : s.2 ∈ seg s := Geometry.right_mem_segment _ _

/-- The point of the line of `s` at a height of its range lies on `s`. -/
theorem pt_mem_seg (hs : s.1.2 < s.2.2) {y : ℝ} (h1 : s.1.2 ≤ y)
    (h2 : y ≤ s.2.2) : ((xAt s y, y) : Point) ∈ seg s :=
  (mem_seg_iff hs).2 by_simp_all

/-- A point of `s` at its lowest height is its lower end. -/
theorem eq_lo (hs : s.1.2 < s.2.2) {p : Point} (hp : p ∈ seg s)
    (h : p.2 = s.1.2) : p = s.1 := by
  zueae
  exact point_ext (by rw [h3, h, xAt_lo]) h

/-- A point of `s` at its highest height is its upper end. -/
theorem eq_hi (hs : s.1.2 < s.2.2) {p : Point} (hp : p ∈ seg s)
    (h : p.2 = s.2.2) : p = s.2 := by
  zueae
  exact point_ext (by rw [h3, h, xAt_hi hs]) h
theorem seg_subset_obs (hs : s ∈ S) : seg s ⊆ obs S :=
  fun _ hp => mem_biUnion hs hp
theorem vert_mem_obs {v : Point} (hv : IsVert S v) : v ∈ obs S := by
  obtain ⟨s, hs, rfl | rfl⟩ := hv
  · exact seg_subset_obs hs (lo_mem_seg s)
  · exact seg_subset_obs hs (hi_mem_seg s)
theorem box_of_dom {p : Point} (hp : p ∈ dom R S) : |p.1| < R ∧ |p.2| < R := hp.1
theorem isOpen_dom (hS : Good R S) : IsOpen ztbgx := by
  zudsp
theorem finite_verts (hS : Good R S) : {v | IsVert S v}.Finite := by
  zucit

  · grind
  grind

/-- A point of the line of a segment of `S` in its height range is within the closed box. -/
theorem abs_xAt_le (hS : Good R S) {s : Point × Point} (hs : s ∈ S) {y : ℝ} (h1 : s.1.2 ≤ y)
    (h2 : y ≤ s.2.2) : |xAt s y| ≤ R :=
  (hS.inbox s hs _ (pt_mem_seg (hS.up s hs) h1 h2)).1

/-- An obstacle point that is not a vertex lies in the open part of a segment. -/
theorem wall_of_obs (hS : Good R S) {p : Point} (hp : p ∈ obs S) (hv : ¬ IsVert S p) :
    ∃ s ∈ S, s.1.2 < p.2 ∧ p.2 < s.2.2 ∧ p.1 = xAt s p.2 := by
  zubhl
  zufwj
  obtain ⟨h1, h2, h3⟩ := (mem_seg_iff hsu).1 hps
  refine ⟨s, hs, lt_of_le_of_ne h1 fun e => hv ⟨s, hs, Or.inl (eq_lo hsu hps e.symm)⟩,
    lt_of_le_of_ne h2 fun e => hv ⟨s, hs, Or.inr (eq_hi hsu hps e)⟩, h3⟩

/-! ## Horizontal hits -/

/-- The first obstacle to the east of a domain point. -/
theorem exists_hit_east (hS : Good R S) {q : Point} (hq : q ∈ dom R S) :
    ∃ b, q.1 < b ∧ (zttfo : Point) ∉ dom R S ∧
      ∀ x, q.1 ≤ x → x < b → (ztbqo : Point) ∈ dom R S := by
  obtain ⟨s, hs, hin, hout⟩ := exists_first_exit (isOpen_dom hS) hq (R := R)
    ztikm
  refine zticp
  have := hin ztuds by_grind
  simp_all

/-- The first obstacle to the west of a domain point. -/
theorem exists_hit_west (hS : Good R S) {q : Point} (hq : q ∈ dom R S) :
    ∃ a, a < q.1 ∧ (ztdgk : Point) ∉ dom R S ∧
      ∀ x, a < x → x ≤ q.1 → (ztbqo : Point) ∈ dom R S := by
  zucue
  have hD'o : IsOpen D' := (isOpen_dom hS).preimage ztepq
  zukfa
  obtain ⟨s, hs, hin, hout⟩ := exists_first_exit hD'o hq' (R := R)
    (fun x hx => by
      have := (abs_lt.1 (box_of_dom hx).1).1
      simp_all)
  refine ⟨q.1 - s, by_linarith, by simpa [hD', sub_eq_add_neg, add_comm] using hout,
    fun x h1 h2 => ?_⟩
  have := hin zttxb by_grind
  simp_all

/-- A hit point is on the obstacle. -/
theorem hit_mem_obs (hS : Good R S) {q : Point} (hq : q ∈ dom R S) {a : ℝ}
    (hnot : (ztdgk : Point) ∉ dom R S)
    (hin : ∀ x, min a q.1 < x → x < max a q.1 → (ztbqo : Point) ∈ dom R S) :
    (ztdgk : Point) ∈ obs S := by
  zudiu

  · zuldr

  · zucoo

    · -- `a ≤ -R`: the hit is on the left side
      have haR : ztumr := by
        zuct
        have hlt : ztumq := by_grind
        have := box_of_dom (hin (-R) (by
          simp_all) (by
          simp_all))
        grind
      zudnx
      refine seg_subset_obs hS.sideL ((mem_seg_iff by_simp_all).2
        ⟨by_grind, by_grind, ?_⟩)
      zudvy
    · have haR : a = R := by
        zuct
        have hlt : R < a := by_grind
        have := box_of_dom (hin R (by
          simp_all) (by
          simp_all))
        grind
      zudnx
      refine seg_subset_obs hS.sideR ((mem_seg_iff by_simp_all).2
        ⟨by_grind, by_grind, ?_⟩)
      zudvy

/-- A hit point seen from a point off the chords is not a vertex. -/
theorem hit_not_vert {G : Set ztf} (hfull : FullAt R S G) {q : Point}
    (hq : q ∈ dom R S) (hqG : q ∉ ⋃₀ G) {a : ℝ}
    (hin : ∀ x, min a q.1 < x → x < max a q.1 → (ztbqo : Point) ∈ dom R S) :
    ¬ IsVert S (ztdgk : Point) :=
  fun hv => hqG (hfull _ hv (box_of_dom hq).2 q hq rfl hin)

/-! ## The trapezoid data -/

/-- The trapezoid data of a point `q`: its walls `sL`, `sR` and the heights of the bottom and top
sides. -/
structure Trap (R : ℝ) (S : Set ztdga) (q : Point) (sL sR : Point × Point)
    (y₁ y₂ : ℝ) : Prop where
  hL : sL ∈ S
  hR : sR ∈ S
  lt_q : xAt sL q.2 < q.1
  q_lt : q.1 < xAt sR q.2
  hseg : ∀ x, xAt sL q.2 < x → x < xAt sR q.2 → (ztbqo : Point) ∈ dom R S
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
theorem exists_trap (hS : Good R S) {G : Set ztf} (hfull : FullAt R S G) {q : Point}
    (hq : q ∈ dom R S) (hqG : q ∉ ⋃₀ G) : ∃ sL sR y₁ y₂, Trap R S q sL sR y₁ y₂ := by
  obtain ⟨a, ha, hanot, hain⟩ := exists_hit_west hS hq
  obtain ⟨b, hb, hbnot, hbin⟩ := exists_hit_east hS hq
  have hina : ztxax := by
    grind
  have hinb : ztxay := by
    grind
  obtain ⟨sL, hsL, hL1, hL2, hLx⟩ := wall_of_obs hS (hit_mem_obs hS hq hanot hina)
    ztqqe
  obtain ⟨sR, hsR, hR1, hR2, hRx⟩ := wall_of_obs hS (hit_mem_obs hS hq hbnot hinb)
    ztqqf
  simp only at hL1 hL2 hLx hR1 hR2 hRx
  have hseg : ztxeq := by
    grind
  -- the vertices at the height of `q` in the closed segment
  have hnoq : ztfxn := by
    zukjw
    zuff
    · zudt
      · have := hseg v.1 h1 h2
        zuctx

      · exact hit_not_vert hfull hq hqG hinb
          by_grind
    · exact hit_not_vert hfull hq hqG hina
        by_grind
  have hV := finite_verts hS
  have hup := hS.up sL hsL
  have hupR := hS.up sR hsR
  -- the top height
  set C₂ : Set ℝ := {y | ∃ v, IsVert S v ∧ v.2 = y ∧ q.2 < y ∧ xAt sL y ≤ v.1 ∧ v.1 ≤ xAt sR y} ∪
    {sL.2.2, sR.2.2} with hC₂
  have hC₂f : C₂.Finite := by
    zqbex
  zuejo
  have hall₂ : ztoru := by
    zqbfc
    · zubh
    · zugzm

  -- the bottom height
  set C₁ : Set ℝ := {y | ∃ v, IsVert S v ∧ v.2 = y ∧ y < q.2 ∧ xAt sL y ≤ v.1 ∧ v.1 ≤ xAt sR y} ∪
    {sL.1.2, sR.1.2} with hC₁
  have hC₁f : C₁.Finite := by
    zqbex
  zuejn
  have hall₁ : ztort := by
    zqbfc
    · zubh
    · zqbey
      · omega
      omega
  refine ⟨sL, sR, y₁, y₂, ⟨hsL, hsR, by_grind, by_grind,
    by grind, by_grind, by_grind,
    hmax _ by_grind, hmax _ by_grind,
    hmin _ by_grind, hmin _ by_grind, ?_, ?_, ?_⟩⟩
  · zudij

    · have := hmax _ zthru
      grind
    · grind
    · have := hmin _ zthrt
      grind
  · zudfe
    · grind
    · zqbey
      · exact ⟨sL.2, ztpfy, rfl, fun hle => ⟨by zuore,
          by zuoil; omega⟩⟩
      · exact ⟨sR.2, ztpga, rfl, fun hle => ⟨by zuoim; omega,
          by zuorf⟩⟩
  · zudfd
    · grind
    · zqbey
      · exact ⟨sL.1, ztpfx, rfl, fun hle => ⟨by zunrq,
          by zuoin; omega⟩⟩
      · exact ⟨sR.1, ztpfz, rfl, fun hle => ⟨by zuoio; omega,
          by zunrq⟩⟩

/-! ## The trapezoid -/

/-- The open trapezoid between the lines of `sL` and `sR` and the heights `y₁ < y₂`. -/
def tr (sL sR : Point × Point) (y₁ y₂ : ℝ) : Set Point :=
  {p | y₁ < p.2 ∧ p.2 < y₂ ∧ xAt sL p.2 < p.1 ∧ p.1 < xAt sR p.2}

/-- The closed trapezoid. -/
def ctr (sL sR : Point × Point) (y₁ y₂ : ℝ) : Set Point :=
  {p | y₁ ≤ p.2 ∧ p.2 ≤ y₂ ∧ xAt sL p.2 ≤ p.1 ∧ p.1 ≤ xAt sR p.2}
theorem isOpen_tr (sL sR : Point × Point) (y₁ y₂ : ℝ) : IsOpen ztkgc := by
  have h1 : ztlxg := isOpen_lt continuous_const continuous_snd
  have h2 : ztlxf := isOpen_lt continuous_snd continuous_const
  have h3 :=
    isOpen_lt ztosn continuous_fst
  have h4 :=
    isOpen_lt continuous_fst ztoso
  have : tr sL sR y₁ y₂ = {p : Point | y₁ < p.2} ∩ ({p : Point | p.2 < y₂} ∩
      ({p : Point | xAt sL p.2 < p.1} ∩ {p : Point | p.1 < xAt sR p.2})) := by
    rfl
  zubk
  zuith
theorem isClosed_ctr (sL sR : Point × Point) (y₁ y₂ : ℝ) : IsClosed (ctr sL sR y₁ y₂) := by
  zudnf

  have h3 :=
    isClosed_le ztosn continuous_fst
  have h4 :=
    isClosed_le continuous_fst ztoso
  have : ctr sL sR y₁ y₂ = {p : Point | y₁ ≤ p.2} ∩ ({p : Point | p.2 ≤ y₂} ∩
      ({p : Point | xAt sL p.2 ≤ p.1} ∩ {p : Point | p.1 ≤ xAt sR p.2})) := by
    rfl
  zubk
  zuith
theorem closure_tr_subset (sL sR : Point × Point) (y₁ y₂ : ℝ) :
    closure ztkgc ⊆ ctr sL sR y₁ y₂ :=
  closure_minimal (fun _ hp => ztoom)
    (isClosed_ctr sL sR y₁ y₂)

/-- The abscissa of the line of a segment is affine in the height. -/
theorem xAt_combo (s : Point × Point) {a b : ℝ} (hab : a + b = 1) (y y' : ℝ) :
    xAt s (a * y + b * y') = a * xAt s y + b * xAt s y' := by
  have e : ∀ z, xAt s z = s.1.1 + (z - s.1.2) * ztejg := by
    intro z; unfold xAt; ring
  grind

/-- Strict inequalities are preserved by convex combinations. -/
theorem combo_lt_combo {a b a' b' s s' : ℝ} (h1 : a < a') (h2 : b < b') (hs : 0 ≤ s)
    (hs' : 0 ≤ s') (h : s + s' = 1) : s * a + s' * b < s * a' + s' * b' := by
  zuevh
  · simp_all
  · zugor

/-- The open trapezoid is convex. -/
theorem convex_tr (sL sR : Point × Point) (y₁ y₂ : ℝ) : Convex ℝ ztkgc := by
  zubaw

  · show y₁ < (a • x + b • y).2
    zutw
    exact Jordan.combo_lt hx1 hy1 ha hb hab
  · show (a • x + b • y).2 < y₂
    zutw
    exact Jordan.combo_gt hx2 hy2 ha hb hab
  · show xAt sL (a • x + b • y).2 < (a • x + b • y).1
    zubip
    rw [xAt_combo sL hab]
    zuita
  · show (a • x + b • y).1 < xAt sR (a • x + b • y).2
    zubip
    rw [xAt_combo sR hab]
    zuitb

/-- A zero of a continuous function between a point where it is positive and one where it is
not. -/
theorem exists_zero_between {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (ha : 0 < f a)
    (hb : f b ≤ 0) : ∃ c, f c = 0 ∧ min a b ≤ c ∧ c ≤ max a b ∧ c ≠ a := by
  rcases le_total a b with hab | hab
  · obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hab hf.continuousOn ztuhb
    grind
  · obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hf.continuousOn ztuhb
    grind

/-- Clamping a height into the range of a segment containing another height. -/
theorem exists_clamp {lo hi p q : ℝ} (hp1 : lo ≤ p) (hp2 : p ≤ hi) :
    ∃ y, lo ≤ y ∧ y ≤ hi ∧ min p q ≤ y ∧ y ≤ max p q ∧ (y = q ∨ y = lo ∨ y = hi) := by
  grind
namespace Trap
variable {q : Point} {sL sR : Point × Point} {y₁ y₂ : ℝ}
theorem q_mem (h : Trap R S q sL sR y₁ y₂) : q ∈ tr sL sR y₁ y₂ :=
  ⟨h.bot_lt, h.lt_top, h.lt_q, h.q_lt⟩
theorem y₁_lt_y₂ (h : Trap R S q sL sR y₁ y₂) : y₁ < y₂ := h.bot_lt.trans h.lt_top

/-- A point on the left wall line at a height of the trapezoid is an obstacle point. -/
theorem memL (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2)
    (h2 : p.2 ≤ y₂) (hx : p.1 = xAt sL p.2) : p ∈ obs S :=
  seg_subset_obs h.hL ((mem_seg_iff ztjxm).2 ztonp)

/-- A point on the right wall line at a height of the trapezoid is an obstacle point. -/
theorem memR (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2)
    (h2 : p.2 ≤ y₂) (hx : p.1 = xAt sR p.2) : p ∈ obs S :=
  seg_subset_obs h.hR ((mem_seg_iff ztjxn).2 ztonq)

/-- **The walls do not cross** strictly between the heights. -/
theorem walls_lt (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {y : ℝ} (h1 : y₁ < y)
    (h2 : y < y₂) : xAt sL y < xAt sR y := by
  zuks

  have hne : ztsmc := by
    zudie
  obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between (f := fun y => xAt sR y - xAt sL y)
    ztlco (a := q.2) (b := y)
    (show (0 : ℝ) < xAt sR q.2 - xAt sL q.2 by have := h.lt_q; have := h.q_lt; linarith)
    ztitq
  zudok

  have hmL :=
    pt_mem_seg ztjxm ztmkj ztmlc
  have hmR : ztytv := by
    zuezk
    exact pt_mem_seg ztjxn ztmkk ztmld
  exact h.no_vertex _ ztlpo hc1' hc2' le_rfl
    by_grind

/-- **No obstacle point strictly inside the corridor.** -/
theorem no_obs (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {p : Point} (hp : p ∈ obs S)
    (h1 : y₁ < p.2) (h2 : p.2 < y₂) (h3 : xAt sL p.2 < p.1) (h4 : p.1 < xAt sR p.2) : False := by
  zubhl
  zufwj
  zuebb
  obtain ⟨y', hy'1, hy'2, hb1, hb2, hcases⟩ := exists_clamp (q := q.2) hp1 hp2
  zuyw

  · zuieb
    · have := h.hseg ztuei zttnk zttnl
      zugxs

    · zuhub
    · zuhuc
  · zuduz

    · have hne : ztsly := by
        grind
      obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between
        ztlcm
        ztgru
        ztitp
      zukbi
      zqbew
      have hmS : ztytu := by
        zudga

      have hmL :=
        pt_mem_seg ztjxm ztmkj ztmlc
      exact h.no_vertex _ ztfsj hc1' hc2' le_rfl
        (h.walls_lt hS hc1' hc2').le
    · have hne : s ≠ sR := by
        grind
      obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between
        ztlcn
        ztgrv
        ztitr
      zukbj
      zqbew
      have hmS : ztioq := by
        zudgb

      have hmR :=
        pt_mem_seg ztjxn ztmkk ztmld
      exact h.no_vertex _ ztlpn hc1' hc2'
        (h.walls_lt hS hc1' hc2').le le_rfl

/-- The trapezoid lies in the domain. -/
theorem tr_subset_dom (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) :
    tr sL sR y₁ y₂ ⊆ dom R S := by
  zuvp

  have hL := (abs_le.1 (abs_xAt_le hS h.hL ztqou ztqpa)).1
  have hR := (abs_le.1 (abs_xAt_le hS h.hR ztvrr ztvsk)).2
  zuhyb

  refine ⟨ztsr,
    fun hp => h.no_obs hS hp h1 h2 h3 h4⟩

/-- **An obstacle point on the open top side is a vertex.** -/
theorem top_side_vert (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {w : Point}
    (hw : w ∈ obs S) (hwy : w.2 = y₂) (h3 : xAt sL y₂ < w.1) (h4 : w.1 < xAt sR y₂) :
    IsVert S w := by
  zqbez
  have hev : ∀ᶠ y in 𝓝 y₂, xAt sL y < xAt s y ∧ xAt s y < xAt sR y :=
    ((continuous_xAt sL).continuousAt.eventually_lt (continuous_xAt s).continuousAt
      (by simp_all)).and
    ((continuous_xAt s).continuousAt.eventually_lt (continuous_xAt sR).continuousAt
      (by simp_all))
  have hlt := max_lt h.y₁_lt_y₂ hs1
  have e1 : ∀ᶠ y in 𝓝[<] y₂, y ∈ Ioo _ y₂ := Ioo_mem_nhdsLT hlt
  zqbfa
  exact h.no_obs hS (seg_subset_obs hs (pt_mem_seg by_grind ztvya
    (hy2.le.trans hs2.le))) by_simp_all hy2 hy3 hy4

/-- **An obstacle point on the open bottom side is a vertex.** -/
theorem bot_side_vert (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {w : Point}
    (hw : w ∈ obs S) (hwy : w.2 = y₁) (h3 : xAt sL y₁ < w.1) (h4 : w.1 < xAt sR y₁) :
    IsVert S w := by
  zqbez
  have hev : ∀ᶠ y in 𝓝 y₁, xAt sL y < xAt s y ∧ xAt s y < xAt sR y :=
    ((continuous_xAt sL).continuousAt.eventually_lt (continuous_xAt s).continuousAt
      (by simp_all)).and
    ((continuous_xAt s).continuousAt.eventually_lt (continuous_xAt sR).continuousAt
      (by simp_all))
  have hlt := lt_min h.y₁_lt_y₂ hs2
  have e1 : ∀ᶠ y in 𝓝[>] y₁, y ∈ Ioo y₁ _ := Ioo_mem_nhdsGT hlt
  zqbfa
  exact h.no_obs hS (seg_subset_obs hs (pt_mem_seg by_grind (hs1.le.trans hy1.le)
    by_grind)) hy1
    by_simp_all hy3 hy4

/-- **A domain point of the open top side lies on a chord of `G`**: it is seen horizontally from
the top vertex. -/
theorem top_side_full (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {G : Set ztf}
    (hfull : FullAt R S G) {p : Point} (hp : p ∈ dom R S) (hpy : p.2 = y₂)
    (h3 : xAt sL y₂ < p.1) (h4 : p.1 < xAt sR y₂) : p ∈ ⋃₀ G := by
  zufkz
  zubxs
  have hy2R := hpy ▸ (box_of_dom hp).2
  zumdo
  have hLb := (abs_le.1 (abs_xAt_le hS h.hL (h.botL.trans hin) h.topL)).1
  have hRb := (abs_le.1 (abs_xAt_le hS h.hR (h.botR.trans hin) h.topR)).2
  zqbfb
  have hxL : xAt sL y₂ < x := by_grind
  have hxR : x < xAt sR y₂ := by_grind
  zujjx
  refine ⟨⟨by_grind, hy2R⟩, fun hobs => ?_⟩
  have hw := h.top_side_vert hS hobs rfl hxL hxR
  zufuo

/-- **A domain point of the open bottom side lies on a chord of `G`.** -/
theorem bot_side_full (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {G : Set ztf}
    (hfull : FullAt R S G) {p : Point} (hp : p ∈ dom R S) (hpy : p.2 = y₁)
    (h3 : xAt sL y₁ < p.1) (h4 : p.1 < xAt sR y₁) : p ∈ ⋃₀ G := by
  zufky
  zubxs
  have hy1R := hpy ▸ (box_of_dom hp).2
  zumdo
  have hLb := (abs_le.1 (abs_xAt_le hS h.hL h.botL (hin.trans h.topL))).1
  have hRb := (abs_le.1 (abs_xAt_le hS h.hR h.botR (hin.trans h.topR))).2
  zqbfb
  have hxL : xAt sL y₁ < x := by_grind
  have hxR : x < xAt sR y₁ := by_grind
  zujjx
  refine ⟨⟨by_grind, hy1R⟩, fun hobs => ?_⟩
  have hw := h.bot_side_vert hS hobs rfl hxL hxR
  zufuo

/-- **The region of `q` lies in its trapezoid.** -/
theorem region_subset (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {G : Set ztf}
    (hfull : FullAt R S G) (hq : q ∈ freeIn ztbgx G) :
    connectedComponentIn ztzvr q ⊆ tr sL sR y₁ y₂ := by
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset ztqrw
    ⟨q, mem_connectedComponentIn hq, h.q_mem⟩ ?_
  zuvq

  have hx3 := lt_of_le_of_ne hp3 fun e => hpD.2 (h.memL hS hp1 hp2 e.symm)
  have hx4 := lt_of_le_of_ne hp4 fun e => hpD.2 (h.memR hS hp1 hp2 e)
  refine ztgpc
  · exact hpG (h.bot_side_full hS hfull hpD e.symm by_simp_all by_simp_all)
  · exact hpG (h.top_side_full hS hfull hpD e by_simp_all by_simp_all)
end Trap
end SegObs
end
end Chazelle.Core
end
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (point_ext)
namespace SegObs
section Chords
variable {D : Set Point}

/-- A horizontal chord of the domain `D`. -/
def HCD (D : Set Point) (c : Set Point) : Prop :=
  ∃ y a b : ℝ, IsHChordIn D y a b ∧ c = hseg y a b
variable {y a b : ℝ}
/-- A point of a chord in the domain is strictly inside it. -/
theorem open_of_mem (h : IsHChordIn D y a b) {z : Point} (hz : z ∈ hseg y a b)
    (hzD : z ∈ D) : a < z.1 ∧ z.1 < b := by
  zubpe
  refine zthnj
  · grind
  grind

/-- Two chords sharing a point of the domain are equal. -/
theorem eq_of_common {c c' : Set Point} (hc : HCD D c) (hc' : HCD D c') {z : Point} (hz : z ∈ c)
    (hz' : z ∈ c') (hzD : z ∈ D) : c = c' := by
  zuhs
  zubaz

  · rfl
  · zulxk
  · zulxl

/-- A chord contains every point of its line joined to it inside the domain. -/
theorem mem_of_joined (h : IsHChordIn D y a b) {z : Point} (hz : z ∈ hseg y a b)
    (hzD : z ∈ D) {w : Point} (hw : w.2 = y)
    (hj : ∀ s : ℝ, min z.1 w.1 ≤ s → s ≤ max z.1 w.1 → (ztkel : Point) ∈ D) :
    w ∈ hseg y a b := by
  zueuh

  · zuhby

  · zuhbz

/-- The points of a chord between two of its domain points are in the domain. -/
theorem between_mem (h : IsHChordIn D y a b) {z z' : Point}
    (hz : z ∈ hseg y a b) (hzD : z ∈ D) (hz' : z' ∈ hseg y a b) (hz'D : z' ∈ D) {s : ℝ}
    (h1 : z.1 ≤ s) (h2 : s ≤ z'.1) : (ztkel : Point) ∈ D :=
  h.open_mem s ztjpt ztjpu

/-- The side of a chord point relative to a point off the domain, read off from the chord. -/
theorem side_iff {c : Set Point} (hc : HCD D c) {y₀ : ℝ} {w₀ : Point} (hw₀ : w₀ ∉ D)
    (hw₀y : w₀.2 = y₀) {z : Point} (hz : z ∈ c) (hzD : z ∈ D) (hzy : z.2 = y₀) :
    (∃ z' ∈ c, z' ∈ D ∧ z'.2 = y₀ ∧ z'.1 < w₀.1) ↔ z.1 < w₀.1 := by
  zuhs
  zubwr
  constructor
  · zubur

    have := between_mem h hz' hz'D hz hzD hlt.le by_omega
    grind
  grind
end Chords

/-! ## Chords on a horizontal side of the trapezoid -/
variable {R : ℝ} {S : Set (Point × Point)}
namespace Trap
variable {q : Point} {sL sR : Point × Point} {y₁ y₂ : ℝ}

/-- **Two chords touching the closed trapezoid at a side height `Y`** (whose obstacle points on
the open side are vertices), on the same side of the vertex `v` at that height, are equal. -/
theorem side_chords_eq (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {Y : ℝ} (hY1 : y₁ ≤ Y)
    (hY2 : Y ≤ y₂)
    (hvert : ∀ w ∈ obs S, w.2 = Y → xAt sL Y < w.1 → w.1 < xAt sR Y → IsVert S w)
    {v : Point} (hv : IsVert S v) (hvY : v.2 = Y)
    {c c' : Set Point} (hc : HCD ztbgx c) (hc' : HCD ztbgx c') {z z' : Point}
    (hz : z ∈ c) (hz' : z' ∈ c') (hzD : z ∈ dom R S) (hz'D : z' ∈ dom R S)
    (hzy : z.2 = Y) (hz'y : z'.2 = Y) (hzx : xAt sL Y ≤ z.1 ∧ z.1 ≤ xAt sR Y)
    (hz'x : xAt sL Y ≤ z'.1 ∧ z'.1 ≤ xAt sR Y) (hside : z.1 < v.1 ↔ z'.1 < v.1) : c = c' := by
  zucwq
  have hYR := hzy ▸ (box_of_dom hzD).2
  have hLb := (abs_le.1 (abs_xAt_le hS h.hL (h.botL.trans hY1) (hY2.trans h.topL))).1
  have hRb := (abs_le.1 (abs_xAt_le hS h.hR (h.botR.trans hY1) (hY2.trans h.topR))).2
  -- strictness at a domain point
  have hstrict : ∀ w : Point, w ∈ dom R S → w.2 = Y → xAt sL Y ≤ w.1 → w.1 ≤ xAt sR Y →
      xAt sL Y < w.1 ∧ w.1 < xAt sR Y := by
    zukjx
    refine ⟨lt_of_le_of_ne h1 fun e => hw.2 (h.memL hS by_simp_all by_simp_all ?_),
      lt_of_le_of_ne h2 fun e => hw.2 (h.memR hS by_simp_all by_simp_all ?_)⟩
    · simp_all
    simp_all
  have key : ∀ {c c' : Set Point} {z z' : Point}, HCD ztbgx c → HCD ztbgx c' → z ∈ c →
      z' ∈ c' → z ∈ dom R S → z' ∈ dom R S → z.2 = Y → z'.2 = Y →
      xAt sL Y ≤ z.1 ∧ z.1 ≤ xAt sR Y → xAt sL Y ≤ z'.1 ∧ z'.1 ≤ xAt sR Y → z.1 ≤ z'.1 →
      (z.1 < v.1 ↔ z'.1 < v.1) → c = c' := by
    intro c c' z z' hc hc' hz hz' hzD hz'D hzy hz'y hzx hz'x hle hside
    obtain ⟨y, a, b, hh, rfl⟩ := hc
    have hy : y = Y := by rw [← hzy, hz.1]
    have hs1 := hstrict z hzD hzy hzx.1 hzx.2
    have hs2 := hstrict z' hz'D hz'y hz'x.1 hz'x.2
    have hall : ∀ s : ℝ, z.1 ≤ s → s ≤ z'.1 → (zttzm : Point) ∈ dom R S := by
      intro s h1 h2
      refine ⟨⟨abs_lt.2 by_grind, hYR⟩, fun hobs => ?_⟩
      have hw := hvert _ hobs rfl by_linarith by_linarith
      have he := hS.distinct v _ hv hw by_grind hvY
      grind
    have hz'c : z' ∈ Visibility.hseg y a b := mem_of_joined hh hz hzD by_grind (fun s h1 h2 => by
      grind)
    exact eq_of_common ⟨y, a, b, hh, rfl⟩ hc' hz'c hz' hz'D
  grind

/-- **At most two chords touch the closure of a set inside the closed trapezoid at a side
height `Y`** that carries a vertex `v` in the closed corridor. -/
theorem ncard_side_le_two (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {Y : ℝ} (hY1 : y₁ ≤ Y)
    (hY2 : Y ≤ y₂)
    (hvert : ∀ w ∈ obs S, w.2 = Y → xAt sL Y < w.1 → w.1 < xAt sR Y → IsVert S w)
    {v : Point} (hv : IsVert S v) (hvY : v.2 = Y) {E : Set ztf}
    (hE : ∀ c ∈ E, HCD ztbgx c ∧ ∃ z ∈ c, z ∈ dom R S ∧ z.2 = Y ∧
      xAt sL Y ≤ z.1 ∧ z.1 ≤ xAt sR Y) : E.ncard ≤ 2 := by
  classical
  zucwq
  let f : Set Point → Bool := fun c => decide (∃ z ∈ c, z ∈ dom R S ∧ z.2 = Y ∧ z.1 < v.1)
  have hinj : InjOn f E := by
    zufxj
    obtain ⟨hcH, z, hz, hzD, hzy, hzx⟩ := hE c hc
    obtain ⟨hc'H, z', hz', hz'D, hz'y, hz'x⟩ := hE c' hc'
    have h1 := side_iff hcH hvD hvY hz hzD hzy
    have h2 := side_iff hc'H hvD hvY hz' hz'D hz'y
    have hside : z.1 < v.1 ↔ z'.1 < v.1 := by
      grind
    exact h.side_chords_eq hS hY1 hY2 hvert hv hvY hcH hc'H hz hz' hzD hz'D hzy hz'y hzx hz'x hside
  have hBool : ztmrb := by
    simp
  calc E.ncard ≤ (Set.univ : Set Bool).ncard :=
        ncard_le_ncard_of_injOn f by_simp_all hinj
    _ = 2 := hBool
end Trap

/-! ## The degree bound -/

/-- **Degree `≤ 4`**: every region of a finite family of horizontal chords of the domain that
contains the vertex chords is touched by at most four of them. -/
theorem deg_le_four (hS : Good R S) {G : Set ztf} (hG : ∀ c ∈ G, HCD ztbgx c)
    (hGfin : G.Finite) (hfull : FullAt R S G) {U : Set Point}
    (hU : U ∈ regionsIn ztbgx G) :
    {c | c ∈ G ∧ TouchesIn ztbgx c U}.ncard ≤ 4 := by
  zucvb

  obtain ⟨sL, sR, y₁, y₂, h⟩ := exists_trap hS hfull hqf.1 hqf.2
  zugyk
  zuioa
  have hUT : ztscv := h.region_subset hS hfull hqf
  have hTD : ztscq := h.tr_subset_dom hS
  zubko

  have hcl : ztoqq :=
    (closure_mono hUT).trans ztqju
  zucdd

  -- a domain point of the closed trapezoid at a middle height is inside
  have hmid : ztezl := by
    zubbr

    exact ⟨hz1, hz2, lt_of_le_of_ne h3 fun e => hzD.2 (h.memL hS h1 h2 e.symm),
      lt_of_le_of_ne h4 fun e => hzD.2 (h.memR hS h1 h2 e)⟩
  -- a chord meeting `T` contains its whole slice
  have hslice : ztbvg := by
    zuor

    zumfc
    zubyd
    have hseg :=
      Geometry.segment_subset_of_convex ztqjz hzT hwT
    zudwt

  -- `U` is on one side of a chord crossing `T`
  have hno : ztcgd := fun c hc z hz hzT p hp he =>
    (hfreeU hp).2 ztdbh
  zudhj
  have hbelow : ztbve := by
    zubgr
    have := hUc.subset_left_of_subset_union (u := {p : Point | p.2 < z.2}) ztdvc
      ztetr
      ztmcj
      ztwzy
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    tauto
  have habove : ztbvf := by
    zubgr
    have := hUc.subset_left_of_subset_union (u := {p : Point | z.2 < p.2}) ztetr
      ztdvc
      ztmcj
      ztwzz
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    tauto
  have hclle : ztbxe := fun y hy =>
    fun p hp => closure_minimal ztbrj
      ztjyx hp
  have hclge : ztbxf := fun y hy =>
    fun p hp => closure_minimal ztbrj
      ztobt hp
  -- the two classes of exit chords
  set E₁ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ ztdwo}
    with hE₁
  set E₂ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ ztdwn}
    with hE₂
  have hsub : ztdjx := by
    zulx

    zudt
    · zuff
      · zubgk

        · exact Or.inl ztcyb
        · exact Or.inr ztcyb
      · zuleo
    · zulek
  -- at most two chords above
  have hE₁ : E₁.ncard ≤ 2 := by
    zuke
    · zuex

      have hsub1 : ztmsz := by
        zugm
        zudzu
        have hmz : ztjac := by
          grind
        zumj

        zufo

      calc E₁.ncard ≤ ({c₀} : Set _).ncard := ncard_le_ncard hsub1 ztgir
        _ ≤ 2 := by_simp
    · zubhq
      have htop : ztcgb := by
        zucd

        · zujvm
        · zudmm
      obtain ⟨v, hv, hvy, -⟩ := h.top_vertex
      refine h.ncard_side_le_two hS h.y₁_lt_y₂.le le_rfl
        (fun w hw hwy h3 h4 => h.top_side_vert hS hw hwy h3 h4) hv hvy fun c hc => ?_
      zubho
      zuih

  -- at most two chords below
  have hE₂ : E₂.ncard ≤ 2 := by
    zukf
    · zuew

      have hsub1 : ztmta := by
        zugm
        zudzt
        have hmz : ztjav := by
          grind
        zumi

        zufo

      calc E₂.ncard ≤ ({c₀} : Set _).ncard := ncard_le_ncard hsub1 ztgir
        _ ≤ 2 := by_simp
    · zubhq
      have hbot : ztcgc := by
        zucd

        · zujvm
        · zudmm
      obtain ⟨v, hv, hvy, -⟩ := h.bot_vertex
      refine h.ncard_side_le_two hS le_rfl h.y₁_lt_y₂.le
        (fun w hw hwy h3 h4 => h.bot_side_vert hS hw hwy h3 h4) hv hvy fun c hc => ?_
      zubhn
      zuih

  have hfin12 : ztkys :=
    (hGfin.subset fun c hc => hc.1).union ztikv
  calc {c | c ∈ G ∧ TouchesIn D c U}.ncard ≤ (E₁ ∪ E₂).ncard := ncard_le_ncard hsub hfin12
    _ ≤ E₁.ncard + E₂.ncard := ncard_union_le _ _
    _ ≤ 4 := by_omega
end SegObs
namespace HSegObs
open SegObs

/-- **The hypotheses on the obstacle segments**, allowing horizontal segments and up to `t`
vertices per height. -/
structure GoodH (R : ℝ) (S : Set ztdga) (t : ℕ) : Prop where
  fin : S.Finite
  le : ∀ s ∈ S, s.1.2 ≤ s.2.2
  inbox : ∀ s ∈ S, ∀ p ∈ seg s, |p.1| ≤ R ∧ |p.2| ≤ R
  sideL : zthpy ∈ S
  sideR : ztipe ∈ S
  cross : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ∀ p ∈ seg s, p ∈ seg s' → IsVert S p
  tmany : ∀ y : ℝ, |y| < R → {v | IsVert S v ∧ v.2 = y}.ncard ≤ t
variable {R : ℝ} {S : Set (Point × Point)} {t : ℕ}

/-! ## Horizontal segments -/
theorem mem_seg_flat {s : Point × Point} (hf : s.1.2 = s.2.2) {p : Point} :
    p ∈ seg s ↔ p.2 = s.1.2 ∧ min s.1.1 s.2.1 ≤ p.1 ∧ p.1 ≤ max s.1.1 s.2.1 := by
  constructor
  · zuczj
    zujft
    · zubi
      zuiem
      · zujkv
      · zujkx
    · zubi
      zuiem
      · zujkm
      · zujkj
  · zuei
    by_cases he : s.1.1 = s.2.1
    · refine ⟨0, le_rfl, zero_le_one, point_ext ?_ ?_⟩
      · grind
      simp_all
    · have hd : s.2.1 - s.1.1 ≠ 0 := sub_ne_zero.2 ztvbb
      refine ⟨(p.1 - s.1.1) / ztkem, ?_, ?_, point_ext ?_ ?_⟩
      · zujeg
        · rw [min_eq_left h.le] at h2
          positivity
        · rw [max_eq_left h.le] at h3
          zuitg
      · zujeg
        · rw [max_eq_right h.le] at h3
          exact (div_le_one by_linarith).2 by_linarith
        · rw [min_eq_right h.le] at h2
          exact (div_le_one_of_neg by_linarith).2 by_linarith
      · simp_all
      simp_all
theorem isOpen_domH (hS : GoodH R S t) : IsOpen ztbgx := by
  zudsp
theorem finite_vertsH (hS : GoodH R S t) : {v | IsVert S v}.Finite := by
  zucit

  · grind
  grind
theorem abs_xAt_leH (hS : GoodH R S t) {s : Point × Point} (hs : s ∈ S) (hu : s.1.2 < s.2.2)
    {y : ℝ} (h1 : s.1.2 ≤ y) (h2 : y ≤ s.2.2) : |xAt s y| ≤ R :=
  (hS.inbox s hs _ (pt_mem_seg hu h1 h2)).1

/-! ## Horizontal hits -/
theorem exists_hit_eastH (hS : GoodH R S t) {q : Point} (hq : q ∈ dom R S) :
    ∃ b, q.1 < b ∧ (zttfo : Point) ∉ dom R S ∧
      ∀ x, q.1 ≤ x → x < b → (ztbqo : Point) ∈ dom R S := by
  obtain ⟨s, hs, hin, hout⟩ := exists_first_exit (isOpen_domH hS) hq (R := R)
    ztikm
  refine zticp
  have := hin ztuds ztbcx
  simp_all
theorem exists_hit_westH (hS : GoodH R S t) {q : Point} (hq : q ∈ dom R S) :
    ∃ a, a < q.1 ∧ (ztdgk : Point) ∉ dom R S ∧
      ∀ x, a < x → x ≤ q.1 → (ztbqo : Point) ∈ dom R S := by
  zucue
  have hD'o : IsOpen D' := (isOpen_domH hS).preimage ztepq
  zukfa
  obtain ⟨s, hs, hin, hout⟩ := exists_first_exit hD'o hq' (R := R)
    (fun x hx => by
      have := (abs_lt.1 (box_of_dom hx).1).1
      simp_all)
  refine ⟨q.1 - s, by_linarith, by simpa [hD', sub_eq_add_neg, add_comm] using hout,
    fun x h1 h2 => ?_⟩
  have := hin zttxb ztbcx
  simp_all
theorem hit_mem_obsH (hS : GoodH R S t) {q : Point} (hq : q ∈ dom R S) {a : ℝ}
    (hnot : (ztdgk : Point) ∉ dom R S)
    (hin : ∀ x, min a q.1 < x → x < max a q.1 → (ztbqo : Point) ∈ dom R S) :
    (ztdgk : Point) ∈ obs S := by
  zudiu

  · zuldr

  · zucoo

    · have haR : ztumr := by
        zuct
        have hlt : ztumq := lt_of_le_of_ne ha hne
        have := box_of_dom (hin (-R) (by
          simp_all) (by
          simp_all))
        grind
      zudnx
      refine seg_subset_obs hS.sideL ((mem_seg_iff by_simp_all).2
        ⟨by_grind, by_grind, ?_⟩)
      zudvy
    · have haR : a = R := by
        zuct
        have hlt : R < a := lt_of_le_of_ne ha ztnr
        have := box_of_dom (hin R (by
          simp_all) (by
          simp_all))
        grind
      zudnx
      refine seg_subset_obs hS.sideR ((mem_seg_iff by_simp_all).2
        ⟨by_grind, by_grind, ?_⟩)
      zudvy

/-- **A horizontal hit that is not a vertex lies in the open part of a non-horizontal
segment** (a horizontal segment on the line would be entered at a vertex first). -/
theorem hit_wall (hS : GoodH R S t) {q : Point} {a : ℝ} (hobs : (ztdgk : Point) ∈ obs S)
    (hv : ¬ IsVert S (ztdgk : Point)) (haq : a ≠ q.1)
    (hin : ∀ x, min a q.1 < x → x < max a q.1 → (ztbqo : Point) ∈ dom R S) :
    ∃ s ∈ S, s.1.2 < q.2 ∧ q.2 < s.2.2 ∧ a = xAt s q.2 := by
  obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hobs
  rcases (hS.le s hs).lt_or_eq with hu | hf
  · obtain ⟨h1, h2, h3⟩ := (mem_seg_iff hu).1 hps
    zulam
    refine ⟨s, hs, lt_of_le_of_ne h1 fun e => hv ⟨s, hs, Or.inl (eq_lo hu hps e.symm)⟩,
      lt_of_le_of_ne h2 fun e => hv ⟨s, hs, Or.inr (eq_hi hu hps e)⟩, h3⟩
  · exfalso
    zuebd
    simp only at hy hmin hmax
    have hne1 : a ≠ s.1.1 := fun e => hv ⟨s, hs, Or.inl (point_ext e hy)⟩
    have hne2 : a ≠ s.2.1 := fun e => hv ⟨s, hs, Or.inr (point_ext e (hy.trans hf))⟩
    have hmin' : min s.1.1 s.2.1 < a := lt_of_le_of_ne hmin fun e => by
      grind
    have hmax' : a < max s.1.1 s.2.1 := lt_of_le_of_ne hmax fun e => by
      grind
    rcases lt_or_gt_of_ne haq with hlt | hgt
    · set x := min (max s.1.1 s.2.1) ztmyj with hx
      have hx1 : a < x := lt_min hmax' by_linarith
      have hx2 : x < q.1 := lt_of_le_of_lt ztgh by_linarith
      zuizs
      exact hxD.2 (seg_subset_obs hs ((mem_seg_flat hf).2 ⟨hy, by_linarith, min_le_left _ _⟩))
    · set x := max (min s.1.1 s.2.1) ztmyj with hx
      have hx1 : x < a := max_lt hmin' by_linarith
      have hx2 : q.1 < x := lt_of_lt_of_le by_linarith (le_max_right _ _)
      zuizs
      exact hxD.2 (seg_subset_obs hs ((mem_seg_flat hf).2 ⟨hy, le_max_left _ _, by_linarith⟩))
theorem exists_trapH (hS : GoodH R S t) {G : Set ztf} (hfull : FullAt R S G) {q : Point}
    (hq : q ∈ dom R S) (hqG : q ∉ ⋃₀ G) : ∃ sL sR y₁ y₂, Trap R S q sL sR y₁ y₂ := by
  obtain ⟨a, ha, hanot, hain⟩ := exists_hit_westH hS hq
  obtain ⟨b, hb, hbnot, hbin⟩ := exists_hit_eastH hS hq
  have hina : ztxax := by
    grind
  have hinb : ztxay := by
    grind
  obtain ⟨sL, hsL, hL1, hL2, hLx⟩ := hit_wall hS (hit_mem_obsH hS hq hanot hina)
    ztqqe ha.ne hina
  obtain ⟨sR, hsR, hR1, hR2, hRx⟩ := hit_wall hS (hit_mem_obsH hS hq hbnot hinb)
    ztqqf hb.ne' hinb
  have hseg : ztxeq := by
    grind
  have hnoq : ztfxn := by
    zukjw
    zuff
    · zudt
      · have := hseg v.1 h1 h2
        zuctx

      · exact hit_not_vert hfull hq hqG hinb
          by_grind
    · exact hit_not_vert hfull hq hqG hina
        by_grind
  have hV := finite_vertsH hS
  have hup := hL1.trans hL2
  have hupR := hR1.trans hR2
  set C₂ : Set ℝ := {y | ∃ v, IsVert S v ∧ v.2 = y ∧ q.2 < y ∧ xAt sL y ≤ v.1 ∧ v.1 ≤ xAt sR y} ∪
    {sL.2.2, sR.2.2} with hC₂
  have hC₂f : C₂.Finite := by
    zubul

  zuejo
  have hall₂ : ztoru := by
    zudjq
    · zubh
    · zugzm

  set C₁ : Set ℝ := {y | ∃ v, IsVert S v ∧ v.2 = y ∧ y < q.2 ∧ xAt sL y ≤ v.1 ∧ v.1 ≤ xAt sR y} ∪
    {sL.1.2, sR.1.2} with hC₁
  have hC₁f : C₁.Finite := by
    zubul

  zuejn
  have hall₁ : ztort := by
    zudjq
    · zubh
    · zugp

      · omega
      omega
  refine ⟨sL, sR, y₁, y₂, ⟨hsL, hsR, by_grind, by_grind,
    by grind, by_grind, by_grind,
    hmax _ by_grind, hmax _ by_grind,
    hmin _ by_grind, hmin _ by_grind, ?_, ?_, ?_⟩⟩
  · zudij

    · have := hmax _ zthru
      grind
    · grind
    · have := hmin _ zthrt
      grind
  · zudfe
    · grind
    · zugp

      · exact ⟨sL.2, ztpfy, rfl, fun hle => ⟨by zuore,
          by zuoil; omega⟩⟩
      · exact ⟨sR.2, ztpga, rfl, fun hle => ⟨by zuoim; omega,
          by zuorf⟩⟩
  · zudfd
    · grind
    · zugp

      · exact ⟨sL.1, ztpfx, rfl, fun hle => ⟨by zunrq,
          by zuoin; omega⟩⟩
      · exact ⟨sR.1, ztpfz, rfl, fun hle => ⟨by zuoio; omega,
          by zunrq⟩⟩
end HSegObs
namespace SegObs
namespace Trap
open HSegObs
variable {R : ℝ} {S : Set (Point × Point)} {t : ℕ}
variable {q : Point} {sL sR : Point × Point} {y₁ y₂ : ℝ}
theorem upL (h : Trap R S q sL sR y₁ y₂) : sL.1.2 < sL.2.2 :=
  lt_of_le_of_lt h.botL (h.y₁_lt_y₂.trans_le h.topL)
theorem upR (h : Trap R S q sL sR y₁ y₂) : sR.1.2 < sR.2.2 :=
  lt_of_le_of_lt h.botR (h.y₁_lt_y₂.trans_le h.topR)
theorem memLH (h : Trap R S q sL sR y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2)
    (h2 : p.2 ≤ y₂) (hx : p.1 = xAt sL p.2) : p ∈ obs S :=
  seg_subset_obs h.hL ((mem_seg_iff h.upL).2 ztonp)
theorem memRH (h : Trap R S q sL sR y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2)
    (h2 : p.2 ≤ y₂) (hx : p.1 = xAt sR p.2) : p ∈ obs S :=
  seg_subset_obs h.hR ((mem_seg_iff h.upR).2 ztonq)

/-- **The walls do not cross** strictly between the heights. -/
theorem walls_ltH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {y : ℝ} (h1 : y₁ < y)
    (h2 : y < y₂) : xAt sL y < xAt sR y := by
  zuks

  have hne : ztsmc := by
    zudie
  obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between (f := fun y => xAt sR y - xAt sL y)
    ztlco (a := q.2) (b := y)
    (show (0 : ℝ) < xAt sR q.2 - xAt sL q.2 by have := h.lt_q; have := h.q_lt; linarith)
    ztitq
  zudok

  have hmL :=
    pt_mem_seg h.upL ztmkj ztmlc
  have hmR : ztytv := by
    zuezk
    exact pt_mem_seg h.upR ztmkk ztmld
  exact h.no_vertex _ ztlpo hc1' hc2' le_rfl
    by_grind

/-- **No obstacle point strictly inside the corridor.** -/
theorem no_obsH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {p : Point} (hp : p ∈ obs S)
    (h1 : y₁ < p.2) (h2 : p.2 < y₂) (h3 : xAt sL p.2 < p.1) (h4 : p.1 < xAt sR p.2) : False := by
  zubhl
  rcases (hS.le s hs).lt_or_eq with hsu | hf
  · zuebb
    obtain ⟨y', hy'1, hy'2, hb1, hb2, hcases⟩ := exists_clamp hp1 hp2
    zuyw

    · zuieb
      · have := h.hseg ztuei zttnk zttnl
        zugxs

      · zuhub
      · zuhuc
    · zuduz

      · have hne : ztsly := by
          grind
        obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between
          ztlcm
          ztgru
          ztitp
        zukbi
        zubey

        have hmS : ztytu := by
          zudga

        have hmL :=
          pt_mem_seg h.upL ztmkj ztmlc
        exact h.no_vertex _ ztfsj hc1' hc2' le_rfl
          (h.walls_ltH hS hc1' hc2').le
      · have hne : s ≠ sR := by
          grind
        obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between
          ztlcn
          ztgrv
          ztitr
        zukbj
        zubey

        have hmS : ztioq := by
          zudgb

        have hmR :=
          pt_mem_seg h.upR ztmkk ztmld
        exact h.no_vertex _ ztlpn hc1' hc2'
          (h.walls_ltH hS hc1' hc2').le le_rfl
  · -- a horizontal segment at the height of `p`
    zuebd
    have hwl := h.walls_ltH hS h1 h2
    have e1 : IsVert S ((s.1.1, p.2) : Point) := ⟨s, hs, by_grind⟩
    have e2 : IsVert S ((s.2.1, p.2) : Point) :=
      ⟨s, hs, by_simp_all⟩
    have out : ∀ x, x = s.1.1 ∨ x = s.2.1 → x < xAt sL p.2 ∨ xAt sR p.2 < x := by
      rintro x hx
      zux

      zudsl
      · exact h.no_vertex _ e1 h1 h2 hc.1 hc.2
      · exact h.no_vertex _ e2 h1 h2 hc.1 hc.2
    have hlo : min s.1.1 s.2.1 < xAt sL p.2 := by
      grind
    have hhi : xAt sR p.2 < max s.1.1 s.2.1 := by
      grind
    have hne : ztsly := by
      intro e; zvmwe at hf; exact absurd hf h.upL.ne
    have hmS : ((xAt sL p.2, p.2) : Point) ∈ seg s :=
      (mem_seg_flat hf).2 by_grind
    have hmL :=
      pt_mem_seg h.upL ztqou ztqpa
    exact h.no_vertex _ ztfsj h1 h2 le_rfl hwl.le

/-- The trapezoid lies in the domain. -/
theorem tr_subset_domH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) :
    tr sL sR y₁ y₂ ⊆ dom R S := by
  zuvp

  have hL := (abs_le.1 (abs_xAt_leH hS h.hL h.upL ztqou ztqpa)).1
  have hR := (abs_le.1 (abs_xAt_leH hS h.hR h.upR ztvrr ztvsk)).2
  zuhyb

  refine ⟨ztsr,
    fun hp => h.no_obsH hS hp h1 h2 h3 h4⟩

/-- **An obstacle point of the open top side is a vertex or lies on a horizontal segment.** -/
theorem top_sideH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {w : Point}
    (hw : w ∈ obs S) (hwy : w.2 = y₂) (h3 : xAt sL y₂ < w.1) (h4 : w.1 < xAt sR y₂) :
    IsVert S w ∨ ∃ s ∈ S, s.1.2 = s.2.2 ∧ w ∈ seg s := by
  zucif

  · zujua
    · simp_all
    zusj

    have hev : ∀ᶠ y in 𝓝 y₂, xAt sL y < xAt s y ∧ xAt s y < xAt sR y :=
      ((continuous_xAt sL).continuousAt.eventually_lt (continuous_xAt s).continuousAt
        (by simp_all)).and
      ((continuous_xAt s).continuousAt.eventually_lt (continuous_xAt sR).continuousAt
        (by simp_all))
    have hlt := max_lt h.y₁_lt_y₂ hs1'
    have e1 : ∀ᶠ y in 𝓝[<] y₂, y ∈ Ioo _ y₂ := Ioo_mem_nhdsLT hlt
    obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := (e1.and (nhdsWithin_le_nhds hev)).exists
    exact h.no_obsH hS (seg_subset_obs hs (pt_mem_seg hsu ztvya
      (hy2.le.trans hs2'.le))) by_simp_all hy2 hy3 hy4
  grind

/-- **An obstacle point of the open bottom side is a vertex or lies on a horizontal segment.** -/
theorem bot_sideH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {w : Point}
    (hw : w ∈ obs S) (hwy : w.2 = y₁) (h3 : xAt sL y₁ < w.1) (h4 : w.1 < xAt sR y₁) :
    IsVert S w ∨ ∃ s ∈ S, s.1.2 = s.2.2 ∧ w ∈ seg s := by
  zucif

  · zujua
    · simp_all
    zusj

    have hev : ∀ᶠ y in 𝓝 y₁, xAt sL y < xAt s y ∧ xAt s y < xAt sR y :=
      ((continuous_xAt sL).continuousAt.eventually_lt (continuous_xAt s).continuousAt
        (by simp_all)).and
      ((continuous_xAt s).continuousAt.eventually_lt (continuous_xAt sR).continuousAt
        (by simp_all))
    have hlt := lt_min h.y₁_lt_y₂ hs2'
    have e1 : ∀ᶠ y in 𝓝[>] y₁, y ∈ Ioo y₁ _ := Ioo_mem_nhdsGT hlt
    obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := (e1.and (nhdsWithin_le_nhds hev)).exists
    exact h.no_obsH hS (seg_subset_obs hs (pt_mem_seg hsu (hs1'.le.trans hy1.le)
      by_grind)) hy1
      by_simp_all hy3 hy4
  grind
def SideOK (S : Set ztdga) (sL sR : Point × Point) (Y : ℝ) : Prop :=
  ∀ w ∈ obs S, w.2 = Y → xAt sL Y < w.1 → w.1 < xAt sR Y →
    IsVert S w ∨ ∃ s ∈ S, s.1.2 = s.2.2 ∧ w ∈ seg s
theorem sideOK_top (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) : SideOK S sL sR y₂ :=
  fun _ hw hwy h3 h4 => h.top_sideH hS hw hwy h3 h4
theorem sideOK_bot (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) : SideOK S sL sR y₁ :=
  fun _ hw hwy h3 h4 => h.bot_sideH hS hw hwy h3 h4
variable {s : Point × Point}
/-- The lower end of a horizontal segment containing a point of the line of a domain point, on
the side away from it, is a vertex between them. -/
theorem flat_vertex (hs : s ∈ S) (hf : s.1.2 = s.2.2) {w z : Point}
    (hws : w ∈ seg s) (hz : z ∉ obs S) (hzy : z.2 = w.2) (hzw : z.1 < w.1) :
    ∃ v, IsVert S v ∧ v.2 = w.2 ∧ z.1 < v.1 ∧ v.1 ≤ w.1 := by
  zuebe
  have hzmin : z.1 < min s.1.1 s.2.1 := by
    zux

    exact hz ztkwx
  rcases min_choice s.1.1 s.2.1 with e | e <;> zvmwe at hzmin hmin
  · exact ⟨s.1, ztpfv, hy.symm, hzmin, hmin⟩
  · exact ⟨s.2, ztpfw, by_simp_all, hzmin, hmin⟩

/-- The mirror image of `flat_vertex`. -/
theorem flat_vertex' (hs : s ∈ S) (hf : s.1.2 = s.2.2) {w z : Point}
    (hws : w ∈ seg s) (hz : z ∉ obs S) (hzy : z.2 = w.2) (hzw : w.1 < z.1) :
    ∃ v, IsVert S v ∧ v.2 = w.2 ∧ w.1 ≤ v.1 ∧ v.1 < z.1 := by
  zuebe
  have hzmax : max s.1.1 s.2.1 < z.1 := by
    zux

    exact hz ztkwx
  rcases max_choice s.1.1 s.2.1 with e | e <;> zvmwe at hzmax hmax
  · exact ⟨s.1, ztpfv, hy.symm, hmax, hzmax⟩
  · exact ⟨s.2, ztpfw, by_simp_all, hmax, hzmax⟩

/-- **A vertex between two domain points of the open side** separated by an obstacle point. -/
theorem vert_between (_hS : GoodH R S t) {Y : ℝ} (hside : SideOK S sL sR Y) {z z' : Point}
    (hz : z ∈ dom R S) (hz' : z' ∈ dom R S) (hzy : z.2 = Y) (_hz'y : z'.2 = Y)
    (hzL : xAt sL Y < z.1) (hz'R : z'.1 < xAt sR Y) {s₀ : ℝ} (hs : z.1 < s₀) (hs' : s₀ < z'.1)
    (hnot : (ztubo : Point) ∉ dom R S) :
    ∃ v, IsVert S v ∧ v.2 = Y ∧ z.1 < v.1 ∧ v.1 < z'.1 := by
  have hb1 := abs_lt.1 (box_of_dom hz).1
  have hb2 := abs_lt.1 (box_of_dom hz').1
  have hYR := hzy ▸ (box_of_dom hz).2
  have hw : (ztubo : Point) ∈ obs S := by
    zukr
    exact hnot ⟨⟨by_grind, hYR⟩, hc⟩
  rcases hside _ hw rfl by_grind by_grind with hv | ⟨s, hs1, hf, hws⟩
  · grind
  · obtain ⟨v, hv, hvy, h1, h2⟩ := flat_vertex hs1 hf hws hz.2 hzy hs
    grind

/-- **A domain point of the open side lies on a chord**, given a vertex of the closed side. -/
theorem side_full (hS : GoodH R S t) (_h : Trap R S q sL sR y₁ y₂) {G : Set ztf}
    (hfull : FullAt R S G) {Y : ℝ} (_hY1 : y₁ ≤ Y) (_hY2 : Y ≤ y₂) (hside : SideOK S sL sR Y)
    {v : Point} (hv : IsVert S v) (hvY : v.2 = Y) (hvL : xAt sL Y ≤ v.1) (hvR : v.1 ≤ xAt sR Y)
    {p : Point} (hp : p ∈ dom R S) (hpy : p.2 = Y) (h3 : xAt sL Y < p.1)
    (h4 : p.1 < xAt sR Y) : p ∈ ⋃₀ G := by
  zucwq
  have hpv : p.1 ≠ v.1 := by_grind
  have hYR := hpy ▸ (box_of_dom hp).2
  rcases lt_or_gt_of_ne hpv with hlt | hgt
  · obtain ⟨b, hb, hbnot, hbin⟩ := exists_hit_eastH hS hp
    have hinb : ∀ x, min b p.1 < x → x < max b p.1 → (ztkhc : Point) ∈ dom R S := by
      grind
    have hbv : b ≤ v.1 := by
      grind
    have hw := hit_mem_obsH hS hp hbnot hinb
    have hwv : IsVert S ((b, p.2) : Point) := by
      rcases lt_or_eq_of_le (show b ≤ xAt sR Y from hbv.trans hvR) with hbR | hbR
      · rcases hside _ hw hpy by_grind hbR with hv' | ⟨s, hs1, hf, hws⟩
        · omega
        · obtain ⟨u, hu, huy, hu1, hu2⟩ := flat_vertex hs1 hf hws hp.2 rfl hb
          rcases hu2.lt_or_eq with hu2 | hu2
          · exfalso
            have := hbin u.1 hu1.le hu2
            zuctw

          grind
      grind
    zuhcu
  · obtain ⟨a, ha, hanot, hain⟩ := exists_hit_westH hS hp
    have hina : ∀ x, min a p.1 < x → x < max a p.1 → (ztkhc : Point) ∈ dom R S := by
      grind
    have hav : v.1 ≤ a := by
      grind
    have hw := hit_mem_obsH hS hp hanot hina
    have hwv : IsVert S (zttet : Point) := by
      rcases lt_or_eq_of_le (show xAt sL Y ≤ a from hvL.trans hav) with haL | haL
      · rcases hside _ hw hpy haL by_grind with hv' | ⟨s, hs1, hf, hws⟩
        · omega
        · obtain ⟨u, hu, huy, hu1, hu2⟩ := flat_vertex' hs1 hf hws hp.2 rfl ha
          rcases hu1.lt_or_eq with hu1 | hu1
          · exfalso
            have := hain u.1 hu1 hu2.le
            zuctw

          grind
      grind
    zuhcu

/-- **The region of `q` lies in its trapezoid.** -/
theorem region_subsetH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {G : Set ztf}
    (hfull : FullAt R S G) (hq : q ∈ freeIn ztbgx G) :
    connectedComponentIn ztzvr q ⊆ tr sL sR y₁ y₂ := by
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset ztqrw
    ⟨q, mem_connectedComponentIn hq, h.q_mem⟩ ?_
  zuvq

  have hx3 := lt_of_le_of_ne hp3 fun e => hpD.2 (h.memLH hp1 hp2 e.symm)
  have hx4 := lt_of_le_of_ne hp4 fun e => hpD.2 (h.memRH hp1 hp2 e)
  refine ztgpc
  · zufky
    zvmyr at hx3 hx4
    zubxs
    exact hpG (h.side_full hS hfull le_rfl h.y₁_lt_y₂.le ztuai hv hvy hv1 hv2 hpD
      e.symm hx3 hx4)
  · zufkz
    zvmwe at hx3 hx4
    zubxs
    exact hpG (h.side_full hS hfull h.y₁_lt_y₂.le le_rfl ztuaj hv hvy hv1 hv2 hpD
      e hx3 hx4)

/-- **At most `t + 1` chords touch the closed side at height `Y`.** -/
theorem ncard_sideH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {Y : ℝ} (hY1 : y₁ ≤ Y)
    (hY2 : Y ≤ y₂) (hside : SideOK S sL sR Y) {E : Set ztf}
    (hE : ∀ c ∈ E, HCD ztbgx c ∧ ∃ z ∈ c, z ∈ dom R S ∧ z.2 = Y ∧
      xAt sL Y ≤ z.1 ∧ z.1 ≤ xAt sR Y) : E.ncard ≤ t + 1 := by
  classical
  by_cases hne : E.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, ncard_empty]; omega
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨-, z₀, -, hz₀D, hz₀y, -⟩ := hE c₀ hc₀
  have hYR : |Y| < R := hz₀y ▸ (box_of_dom hz₀D).2
  have hstrict : ∀ w : Point, w ∈ dom R S → w.2 = Y → xAt sL Y ≤ w.1 → w.1 ≤ xAt sR Y →
      xAt sL Y < w.1 ∧ w.1 < xAt sR Y := by
    zukjx
    refine ⟨lt_of_le_of_ne h1 fun e => hw.2 (h.memLH by_simp_all by_simp_all ?_),
      lt_of_le_of_ne h2 fun e => hw.2 (h.memRH by_simp_all by_simp_all ?_)⟩
    · simp_all
    simp_all
  -- the chosen point of each chord
  let zc : Set Point → Point := fun c =>
    if hc : c ∈ E then Classical.choose (hE c hc).2 else (0, 0)
  have hzc : ∀ c ∈ E, zc c ∈ c ∧ zc c ∈ dom R S ∧ (zc c).2 = Y ∧
      xAt sL Y ≤ (zc c).1 ∧ (zc c).1 ≤ xAt sR Y := by_grind
  set V := {v | IsVert S v ∧ v.2 = Y} with hV
  have hVf : V.Finite := (finite_vertsH hS).subset by_simp_all
  let g : Set Point → ℕ := fun c => {v | v ∈ V ∧ v.1 < (zc c).1}.ncard
  have hgle : ∀ c, g c ≤ t := fun c =>
    (ncard_le_ncard by_simp_all hVf).trans (hS.tmany Y hYR)
  -- the key: chords with points in order are separated by a vertex
  have hlt : ∀ c ∈ E, ∀ c' ∈ E, c ≠ c' → (zc c).1 < (zc c').1 → g c < g c' := by
    intro c hc c' hc' hcc' hlt
    obtain ⟨hz, hzD, hzy, hzx⟩ := hzc c hc
    obtain ⟨hz', hz'D, hz'y, hz'x⟩ := hzc c' hc'
    obtain ⟨y, a, b, hh, hceq⟩ := (hE c hc).1
    have hzc1 : zc c ∈ Visibility.hseg y a b := by_simp_all
    have hy : y = Y := by rw [← hzy, hzc1.1]
    have hs1 := hstrict _ hzD hzy hzx.1 hzx.2
    have hs2 := hstrict _ hz'D hz'y hz'x.1 hz'x.2
    by_cases hall : ∀ s : ℝ, (zc c).1 ≤ s → s ≤ (zc c').1 → (zttzm : Point) ∈ dom R S
    · exfalso
      have hz'c := mem_of_joined hh hzc1 hzD by_linarith
        (fun s h1 h2 => by
          rw [min_eq_left hlt.le] at h1; rw [max_eq_right hlt.le] at h2
          rw [hy]; tauto)
      exact hcc' (eq_of_common (hE c hc).1 (hE c' hc').1 (hceq ▸ hz'c) hz' hz'D)
    · zugrg
      obtain ⟨s₀, h1, h2, hnot⟩ := hall
      have h1' : (zc c).1 < s₀ := by_grind
      have h2' : s₀ < (zc c').1 := by_grind
      obtain ⟨v, hv, hvy, hv1, hv2⟩ := vert_between hS hside hzD hz'D hzy hz'y hs1.1 hs2.2 h1' h2'
        hnot
      have hsub : {v | v ∈ V ∧ v.1 < (zc c).1} ⊆ {v | v ∈ V ∧ v.1 < (zc c').1} :=
        fun w hw => ⟨hw.1, hw.2.trans hlt⟩
      have hvin : v ∈ {v | v ∈ V ∧ v.1 < (zc c').1} := ⟨⟨hv, hvy⟩, hv2⟩
      have hvout : v ∉ {v | v ∈ V ∧ v.1 < (zc c).1} := fun hh => by
        have := hh.2; linarith
      exact ncard_lt_ncard (ssubset_of_subset_of_ne hsub fun e => hvout (e ▸ hvin))
        (hVf.subset fun w hw => hw.1)
  have hinj : InjOn g E := by
    intro c hc c' hc' hgg
    by_contra hcc'
    obtain ⟨hz, hzD, -, -⟩ := hzc c hc
    obtain ⟨hz', hz'D, -, -⟩ := hzc c' hc'
    have hne : (zc c).1 ≠ (zc c').1 := by
      zuchf
      have hzz := point_ext e (by rw [(hzc c hc).2.2.1, (hzc c' hc').2.2.1])
      exact hcc' (eq_of_common (hE c hc).1 (hE c' hc').1 hz (hzz ▸ hz') hzD)
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := hlt c hc c' hc' hcc' h1; omega
    · have := hlt c' hc' c hc (Ne.symm hcc') h1; omega
  calc E.ncard ≤ (Set.Iic t).ncard :=
        ncard_le_ncard_of_injOn g (fun c _ => hgle c) hinj (Set.finite_Iic t)
    _ = t + 1 := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_Iic]; simp
end Trap
end SegObs
namespace HSegObs
open SegObs SegObs.Trap
variable {R : ℝ} {S : Set (Point × Point)} {t : ℕ}

/-- **Degree `≤ 2 (t + 1)`**: every region of a finite family of horizontal chords of the domain
that contains the vertex chords is touched by at most `2 (t + 1)` of them. -/
theorem deg_leH (hS : GoodH R S t) {G : Set ztf} (hG : ∀ c ∈ G, HCD ztbgx c)
    (hGfin : G.Finite) (hfull : FullAt R S G) {U : Set Point}
    (hU : U ∈ regionsIn ztbgx G) :
    {c | c ∈ G ∧ TouchesIn ztbgx c U}.ncard ≤ 2 * ztbx := by
  zucvb

  obtain ⟨sL, sR, y₁, y₂, h⟩ := exists_trapH hS hfull hqf.1 hqf.2
  zugyk
  set U := connectedComponentIn zttkd q with hUdef
  have hUT : ztscv := h.region_subsetH hS hfull hqf
  have hTD : ztscq := h.tr_subset_domH hS
  zubko

  have hcl : ztoqq :=
    (closure_mono hUT).trans ztqju
  zucdd

  -- a domain point of the closed trapezoid at a middle height is inside
  have hmid : ztezl := by
    zubbr

    exact ⟨hz1, hz2, lt_of_le_of_ne h3 fun e => hzD.2 (h.memLH h1 h2 e.symm),
      lt_of_le_of_ne h4 fun e => hzD.2 (h.memRH h1 h2 e)⟩
  -- a chord meeting `T` contains its whole slice
  have hslice : ztbvg := by
    zuor

    have hzy : ztlbm := hz.1
    zubyd
    have hseg : Chazelle.segment z w ⊆ T :=
      Geometry.segment_subset_of_convex ztqjz hzT hwT
    zudwt

  -- `U` is on one side of a chord crossing `T`
  have hno : ztcgd := fun c hc z hz hzT p hp he =>
    (hfreeU hp).2 ztdbh
  zudhj
  have hbelow : ztbve := by
    zubgr
    have := hUc.subset_left_of_subset_union (u := {p : Point | p.2 < z.2})
      (v := {p : Point | z.2 < p.2}) ztdvc
      ztetr
      ztfbe
      ztwzy
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    tauto
  have habove : ztbvf := by
    zubgr
    have := hUc.subset_left_of_subset_union (u := {p : Point | z.2 < p.2})
      (v := {p : Point | p.2 < z.2}) ztetr
      ztdvc
      ztfbe
      ztwzz
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    tauto
  have hclle : ztbxe := fun y hy =>
    fun p hp => closure_minimal ztbrj
      ztjyx hp
  have hclge : ztbxf := fun y hy =>
    fun p hp => closure_minimal ztbrj
      ztobt hp
  -- the two classes of exit chords
  set E₁ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ ztdwo}
    with hE₁
  set E₂ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ ztdwn}
    with hE₂
  have hsub : ztdjx := by
    zulx

    zudt
    · zuff
      · zubgk

        · exact Or.inl ⟨hc, z, hz, hzD, hzU, Or.inr ⟨h3, h2⟩⟩
        · exact Or.inr ⟨hc, z, hz, hzD, hzU, Or.inr ztons⟩
      · zuleo
    · zulek
  -- at most two chords above
  have hE₁ : E₁.ncard ≤ t + 1 := by
    zuke
    · zuex

      have hsub1 : ztmsz := by
        zugm
        zudzu
        have hmz : ztjac := by
          grind
        zumj

        have heq : ztlbn := le_antisymm hz0' hz0
        zucws

      calc E₁.ncard ≤ ({c₀} : Set ztf).ncard := ncard_le_ncard hsub1 ztgir
        _ ≤ t + 1 := by_simp
    · zubhq
      have htop : ztcgb := by
        zucd

        · zujvm
        · zudmm
      refine h.ncard_sideH hS h.y₁_lt_y₂.le le_rfl ztuaj fun c hc => ?_
      zubho
      zuih

  -- at most two chords below
  have hE₂ : E₂.ncard ≤ t + 1 := by
    zukf
    · zuew

      have hsub1 : ztmta := by
        zugm
        zudzt
        have hmz : ztjav := by
          grind
        zumi

        have heq : ztlbn := le_antisymm hz0 hz0'
        zucws

      calc E₂.ncard ≤ ({c₀} : Set ztf).ncard := ncard_le_ncard hsub1 ztgir
        _ ≤ t + 1 := by_simp
    · zubhq
      have hbot : ztcgc := by
        zucd

        · zujvm
        · zudmm
      refine h.ncard_sideH hS le_rfl h.y₁_lt_y₂.le ztuai fun c hc => ?_
      zubhn
      zuih

  have hfin12 : ztkys :=
    (hGfin.subset fun c hc => hc.1).union ztikv
  calc {c | c ∈ G ∧ TouchesIn D c U}.ncard ≤ (E₁ ∪ E₂).ncard := ncard_le_ncard hsub hfin12
    _ ≤ E₁.ncard + E₂.ncard := ncard_union_le _ _
    _ ≤ 2 * ztbx := by_omega
end HSegObs
end
end Chazelle.Core
namespace Chazelle.Core.Dec
@[expose] public section
open Relation Finset

/-- The facts a breadth-first search from region `0` establishes on the region–chord tree with
`R` regions and `K` chords (chord `i` joins `up i` and `dn i`). -/
structure Rooted (R K : ℕ) (up dn ord pos prg pch : ℕ → ℕ) : Prop where
  hR : R = K + 1
  ord_lt : ∀ i, i < R → ord i < R
  pos_lt : ∀ r, r < R → pos r < R
  ord_pos : ∀ r, r < R → ord (pos r) = r
  pos_ord : ∀ i, i < R → pos ztbnh = i
  root : ord 0 = 0
  prg_lt : ∀ s, s < R → s ≠ 0 → prg s < R
  pos_prg : ∀ s, s < R → s ≠ 0 → pos ztqut < pos s
  pch_lt : ∀ s, s < R → s ≠ 0 → pch s < K
  ends : ∀ s, s < R → s ≠ 0 →
    (up zteuo = prg s ∧ dn zteuo = s) ∨ (up zteuo = s ∧ dn zteuo = prg s)
  pch_surj : ∀ i, i < K → ∃ s, s < R ∧ s ≠ 0 ∧ pch s = i
  ends_lt : ∀ i, i < K → up i < R ∧ dn i < R

/-- `y` is a child of `x` (not through a removed chord). -/
def ChX (R : ℕ) (prg pch rem : ℕ → ℕ) (x y : ℕ) : Prop :=
  y < R ∧ y ≠ 0 ∧ prg y = x ∧ rem (pch y) ≠ 1

/-- `a` is an ancestor of `u` in its component (not through a removed chord). -/
def AncX (R : ℕ) (prg pch rem : ℕ → ℕ) : ℕ → ℕ → Prop := ReflTransGen (ChX R prg pch rem)

/-- A top: the root, or a region whose parent chord is removed. -/
def IsTop (pch rem : ℕ → ℕ) (t : ℕ) : Prop := t = 0 ∨ rem ztwbr = 1
instance (pch rem : ℕ → ℕ) (t : ℕ) : Decidable (IsTop pch rem t) :=
  inferInstanceAs (Decidable (t = 0 ∨ rem ztwbr = 1))

/-- No chord removed. -/
def rem0 : ℕ → ℕ := fun _ => 0
section rooted
variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h
theorem Rooted.pos_inj {r s : ℕ} (hr : r < R) (hs : s < R) (he : pos r = pos s) : r = s := by
  rw [← h.ord_pos r hr, ← h.ord_pos s hs, he]
theorem Rooted.R_pos : 0 < R := by rw [h.hR]; omega
variable {rem : ℕ → ℕ}
variable {a b : ℕ} {u : ℕ} {rem' : ℕ → ℕ}
/-- An ancestor precedes its descendants in the search order. -/
theorem AncX.pos_le (hab : AncX R prg pch rem a b) (hb : b < R) :
    a < R ∧ pos a ≤ pos b ∧ (a ≠ b → pos a < pos b) := by
  induction hab with
  | refl => exact by_omega
  | tail hax hxc ih =>
    zuhje
    obtain ⟨hc, hc0, hpc, -⟩ := hxc
    have hxR : x < R := hpc ▸ h.prg_lt c hc hc0
    have hlt : pos x < pos c := hpc ▸ h.pos_prg c hc hc0
    obtain ⟨ha, hle, -⟩ := ih hxR
    zulyc
theorem AncX.antisymm (hab : AncX R prg pch rem a b) (hba : AncX R prg pch rem b a)
    (hb : b < R) : a = b := by
  zuct
  have h1 := (hab.pos_le h hb).2.2 hne
  have ha := (hab.pos_le h hb).1
  have h2 := (hba.pos_le h ha).2.1
  omega
omit h in
/-- The last step of an ancestor path. -/
theorem AncX.back_iff (_h : Rooted R K up dn ord pos prg pch) {a s : ℕ} :
    AncX R prg pch rem a s ↔ a = s ∨ (s < R ∧ s ≠ 0 ∧ rem zteuo ≠ 1 ∧ AncX R prg pch rem a ztqut) := by
  constructor
  · zumgt
    rcases hs.cases_tail with e | ⟨x, hax, hx⟩
    · omega
    · obtain ⟨hsR, hs0, hp, hr⟩ := hx
      exact Or.inr ⟨hsR, hs0, hr, hp ▸ hax⟩
  · rintro (rfl | ⟨hsR, hs0, hr, hax⟩)
    · tauto
    · exact hax.tail ⟨hsR, hs0, rfl, hr⟩

/-- Ancestors of a region form a chain. -/
theorem AncX.chain {a b u : ℕ} (hau : AncX R prg pch rem a u) (hbu : AncX R prg pch rem b u) :
    AncX R prg pch rem a b ∨ AncX R prg pch rem b a := by
  induction hau generalizing b with
  | refl => exact Or.inr hbu
  | tail hax hxc ih =>
    zuhje
    rcases (AncX.back_iff h).1 hbu with rfl | ⟨-, -, -, hbx⟩
    · exact Or.inl (hax.tail hxc)
    · obtain ⟨-, -, hpc, -⟩ := hxc
      simp_all
omit h in
/-- A proper descendant is not a top. -/
theorem AncX.not_top (hab : AncX R prg pch rem a b) (hne : a ≠ b) : ¬ IsTop pch rem b := by
  rcases hab.cases_tail with e | ⟨x, -, hx⟩
  · omega
  · obtain ⟨-, hb0, -, hr⟩ := hx
    zugax
    · omega
    omega

/-- The top of a region is unique. -/
theorem top_unique {t t' u : ℕ} (ht : IsTop pch rem t) (ht' : IsTop pch rem t')
    (hu : AncX R prg pch rem t u) (hu' : AncX R prg pch rem t' u) : t = t' := by
  rcases AncX.chain h hu hu' with h1 | h1
  · zuct
    exact h1.not_top hne ht'
  · zuct
    exact h1.not_top ztnr ht

/-- Every region has a top. -/
theorem exists_top (hu : u < R) : ∃ t, IsTop pch rem t ∧ AncX R prg pch rem t u := by
  induction hp : pos u using Nat.strong_induction_on generalizing u with
  | _ n ih =>
    by_cases ht : IsTop pch rem u
    · exact ⟨u, ht, ReflTransGen.refl⟩
    · simp only [IsTop, not_or] at ht
      have hpR := h.prg_lt u hu ht.1
      obtain ⟨t, htt, hta⟩ := ih (pos (prg u)) (hp ▸ h.pos_prg u hu ht.1) hpR rfl
      exact ⟨t, htt, hta.tail ⟨hu, ht.1, rfl, ht.2⟩⟩

/-- Every region descends from the root (no chord removed). -/
theorem anc_root (hu : u < R) : AncX R prg pch rem0 0 u := by
  obtain ⟨t, ht, hta⟩ := exists_top h (rem := rem0) hu
  rcases ht with rfl | h1
  · omega
  tauto
omit h in
/-- Removing more chords shrinks the ancestor relation. -/
theorem AncX.mono (hrem : ∀ e, rem e = 1 → rem' e = 1) {a b : ℕ}
    (hab : AncX R prg pch rem' a b) : AncX R prg pch rem a b := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hxc ih =>
    obtain ⟨h1, h2, h3, h4⟩ := hxc
    exact ih.tail ⟨h1, h2, h3, by_grind⟩
omit h in
theorem AncX.to0 (hab : AncX R prg pch rem a b) : AncX R prg pch rem0 a b :=
  AncX.mono (rem := rem0) (fun e he => by_tauto) hab

/-- A path whose chords are all kept by `rem'` survives. -/
theorem AncX.of_keep {a b : ℕ} (hab : AncX R prg pch rem a b)
    (hkeep : ∀ w, AncX R prg pch rem a w → AncX R prg pch rem w b → w ≠ a → rem' ztkci ≠ 1) :
    AncX R prg pch rem' a b := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail hax hxc ih =>
    zuhje
    have hc : AncX R prg pch rem a c := hax.tail hxc
    refine (ih fun w hw1 hw2 hw3 => hkeep w hw1 (hw2.tail hxc) hw3).tail ?_
    obtain ⟨h1, h2, h3, _⟩ := hxc
    refine ⟨h1, h2, h3, hkeep c hc ReflTransGen.refl ?_⟩
    intro hca
    have hxR : x < R := h3 ▸ h.prg_lt c h1 h2
    have h5 := (AncX.pos_le h hax hxR).2.1
    have h6 := h.pos_prg c h1 h2
    rw [h3, hca] at h6
    omega

/-- The part of a component below one of its regions. -/
theorem AncX.of_anc0 {a b v : ℕ} (hav : AncX R prg pch rem a v) (hbv : AncX R prg pch rem0 b v)
    (hab : AncX R prg pch rem0 a b) (hv : v < R) : AncX R prg pch rem b v := by
  induction hav generalizing b with
  | refl =>
    have hb := (hbv.pos_le h hv).1
    have := AncX.antisymm h hab hbv hb
    zumo
    exact ReflTransGen.refl
  | tail hax hxc ih =>
    zuhje
    rcases (AncX.back_iff h).1 hbv with rfl | ⟨-, -, -, hbx⟩
    · tauto
    · zumem
      rw [hpc] at hbx
      exact (ih hbx hab ztpcf).tail hxc

/-- The upper part of a component path. -/
theorem AncX.upper {a v w : ℕ} (hav : AncX R prg pch rem a v) (hwv : AncX R prg pch rem0 w v)
    (haw : AncX R prg pch rem0 a w) (hv : v < R) : AncX R prg pch rem a w := by
  induction hav generalizing w with
  | refl =>
    have := AncX.antisymm h hwv haw hv
    zubk
    exact ReflTransGen.refl
  | tail hax hxc ih =>
    zuhje
    rcases (AncX.back_iff h).1 hwv with rfl | ⟨-, -, -, hwx⟩
    · exact hax.tail hxc
    · zumem
      rw [hpc] at hwx
      exact ih hwx haw ztpcf

/-- The parent chords of distinct regions are distinct. -/
theorem Rooted.pch_inj {s s' : ℕ} (hs : s < R) (hs' : s' < R) (h0 : s ≠ 0) (h0' : s' ≠ 0)
    (he : pch s = pch s') : s = s' := by
  zuct
  have p1 := h.pos_prg s hs h0
  have p2 := h.pos_prg s' hs' h0'
  rcases h.ends s hs h0 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases h.ends s' hs' h0' with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> zvmxm at a1 a2
  · omega
  · -- `s = prg s'` and `s' = prg s`
    grind
  · grind
  omega

/-- With no chord removed below `K`, every region is in the component of the root. -/
theorem anc_root_of (hu : u < R) (hrem : ∀ e, e < K → rem e ≠ 1) :
    AncX R prg pch rem 0 u :=
  (anc_root h hu).of_keep h fun w _ hw hw0 =>
    hrem _ (h.pch_lt w (AncX.pos_le h hw hu).1 hw0)

/-- The part of a component below a member `c`. -/
theorem anc_member {t c v : ℕ} (htc : AncX R prg pch rem t c) (hv : v < R) :
    AncX R prg pch rem c v ↔ AncX R prg pch rem t v ∧ AncX R prg pch rem0 c v :=
  ⟨fun hcv => ⟨htc.trans hcv, hcv.to0⟩, fun ⟨htv, hcv⟩ => htv.of_anc0 h hcv htc.to0 hv⟩
end rooted

/-! ## Sizes -/
section sizes
variable (R : ℕ) (prg pch : ℕ → ℕ)
open Classical in
/-- The `AncX`-descendants of `u` (below `R`). -/
noncomputable def sub (rem : ℕ → ℕ) (u : ℕ) : Finset ℕ :=
  (range R).filter (AncX R prg pch rem u)

/-- The number of `AncX`-descendants of `u`: the size of the part of its component below it. -/
noncomputable def sz (rem : ℕ → ℕ) (u : ℕ) : ℕ := (sub R prg pch rem u).card
open Classical in
/-- The children of `u` in its component. -/
noncomputable def kids (rem : ℕ → ℕ) (u : ℕ) : Finset ℕ :=
  (range R).filter (ChX R prg pch rem u)
end sizes
section sizes2
variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h
variable {rem : ℕ → ℕ}
omit h in
theorem mem_sub {u v : ℕ} : v ∈ sub R prg pch rem u ↔ v < R ∧ AncX R prg pch rem u v := by
  classical
  simp [sub]
omit h in
theorem mem_kids {u c : ℕ} : c ∈ kids R prg pch rem u ↔ ChX R prg pch rem u c := by
  classical
  simp only [kids, mem_filter, mem_range, and_iff_right_iff_imp]
  exact fun hc => hc.1
omit h in
theorem self_mem_sub {u : ℕ} (hu : u < R) : u ∈ sub R prg pch rem u :=
  mem_sub.2 ⟨hu, ReflTransGen.refl⟩
omit h in
theorem sz_pos (_h : Rooted R K up dn ord pos prg pch) {u : ℕ}
    (hu : u < R) : 1 ≤ sz R prg pch rem u :=
  Finset.card_pos.2 ⟨u, self_mem_sub hu⟩

/-- **The size recurrence**: `sz u = 1 + Σ sz c` over the children `c` of `u` in its component. -/
theorem sz_rec {u : ℕ} (hu : u < R) :
    sz R prg pch rem u = 1 + ∑ c ∈ kids R prg pch rem u, sz R prg pch rem c := by
  classical
  have hdisj : (↑(kids R prg pch rem u) : Set ℕ).PairwiseDisjoint ztkfq := by
    zukjc
    rw [Finset.mem_coe, mem_kids] at hc hc'
    zukpg
    zugon
    rw [mem_sub] at hv hv'
    rcases AncX.chain h hv.2 hv'.2 with h1 | h1
    · zucyi
      · omega
      · rw [hc'.2.2.1] at h2
        zuhdz
        zubqq

    · zucyi
      · omega
      · rw [hc.2.2.1] at h2
        zuhdz
        have h4 := h.pos_prg c' hc'.1 hc'.2.1
        rw [hc'.2.2.1] at h4
        omega
  have hnot : u ∉ (kids R prg pch rem u).biUnion ztkfq := by
    rw [Finset.mem_biUnion]
    rintro ⟨c, hc, hu'⟩
    zubbi
    rw [mem_sub] at hu'
    have h3 := (hu'.2.pos_le h hu).2.1
    zubqq

  have heq : sub R prg pch rem u = insert u ((kids R prg pch rem u).biUnion ztkfq) := by
    zuepb
    rw [Finset.mem_insert, Finset.mem_biUnion, mem_sub]
    constructor
    · zubuq
      rcases hav.cases_head with e | ⟨c, huc, hcv⟩
      · omega
      · exact Or.inr ⟨c, mem_kids.2 huc, mem_sub.2 ⟨hv, hcv⟩⟩
    · rintro (rfl | ⟨c, hc, hv⟩)
      · tauto
      · zubbi
        rw [mem_sub] at hv
        exact ⟨hv.1, ReflTransGen.head hc hv.2⟩
  unfold sz
  rw [heq, Finset.card_insert_of_notMem hnot, Finset.card_biUnion hdisj]
  omega

/-- A proper descendant has a strictly smaller subtree. -/
theorem sz_lt {a c : ℕ} (hac : AncX R prg pch rem a c) (hne : a ≠ c) (hc : c < R) :
    sz R prg pch rem c + 1 ≤ sz R prg pch rem a := by
  classical
  have ha := (hac.pos_le h hc).1
  have hsub : insert a (sub R prg pch rem c) ⊆ sub R prg pch rem a := by
    zuml
    rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact self_mem_sub ha
    · rw [mem_sub] at hv ⊢
      exact ⟨hv.1, hac.trans hv.2⟩
  have hna : a ∉ sub R prg pch rem c := by
    rw [mem_sub]
    rintro ⟨-, hca⟩
    exact hne (AncX.antisymm h hac hca hc)
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hna] at this
  zufep
end sizes2

/-! ## The edge separator -/

/-- A sum of `card s ≤ D` terms (plus an optional extra term, present iff `e`) equal to `m ≥ 1`
has a term `x` with `m ≤ D x`. -/
theorem pigeon {s : Finset ℕ} (f : ℕ → ℕ) (u m D : ℕ) (e : Prop) [Decidable e]
    (hsum : ∑ c ∈ s, f c + u = m) (hcard : s.card + (if e then 1 else 0) ≤ D)
    (hu : ¬ e → u = 0) (hm : 1 ≤ m) :
    (∃ c ∈ s, m ≤ D * f c) ∨ (e ∧ m ≤ D * u) := by
  classical
  zulwf
  simp only [not_or, not_exists, not_and, not_le] at hno
  obtain ⟨h1, h2⟩ := hno
  have hs : ∑ c ∈ s, D * f c ≤ ∑ c ∈ s, m := Finset.sum_le_sum by_grind
  rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hs
  by_cases he : e
  · have h2' := h2 he
    rw [ite_eq_left he] at hcard
    have : D * m = D * (∑ c ∈ s, f c) + D * u := by_grind
    have h3 : D * m < zttzo * m := by_nlinarith
    have h4 : zttzo * m ≤ D * m := Nat.mul_le_mul_right _ hcard
    omega
  · have hu0 := hu he
    rw [ite_eq_right he, add_zero] at hcard
    rw [hu0, add_zero] at hsum
    have hne : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with h0 | h0
      · grind
      omega
    have hs' := Finset.sum_lt_sum_of_nonempty hne h1
    rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul, hsum] at hs'
    have h4 : s.card * m ≤ D * m := Nat.mul_le_mul_right _ hcard
    omega
section sep
variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h
variable {rem : ℕ → ℕ} {D : ℕ}

/-- **The edge separator.**  In the component of a top `t` with `n = sz t ≥ 2` regions, if every
region has at most `D` tree neighbours, there is a non-top region `c` of the component with
`n - 1 ≤ D · min (sz c) (n - sz c)`. -/
theorem exists_good
    (hdeg : ∀ v, v < R → (kids R prg pch rem0 v).card + ztbst ≤ D)
    {t : ℕ} (ht : t < R) (_htop : IsTop pch rem t) (hn : 2 ≤ sz R prg pch rem t) :
    ∃ c, c < R ∧ AncX R prg pch rem t c ∧ c ≠ t ∧
      sz R prg pch rem t - 1 ≤ D * min ztpej ztimh := by
  classical
  set n := sz R prg pch rem t with hn_def
  set V := (range R).filter (fun v => AncX R prg pch rem t v ∧ n < 2 * sz R prg pch rem v) with hV
  have htV : t ∈ V := by
    zuiji
    exact ⟨ht, ReflTransGen.refl, by_omega⟩
  obtain ⟨v, hvV, hvmax⟩ := Finset.exists_max_image V pos by_grind
  rw [hV, Finset.mem_filter, Finset.mem_range] at hvV
  obtain ⟨hvR, htv, hvbig⟩ := hvV
  -- the children of `v` are small
  have hsmall : ∀ c ∈ kids R prg pch rem v, 2 * sz R prg pch rem c ≤ n := by
    zung
    zubbi
    by_contra hbig
    have hcV : c ∈ V := by
      zuiji
      exact ⟨hc.1, htv.tail hc, by_omega⟩
    have := hvmax c hcV
    zubqq

  -- the kids in the component are tree kids
  have hkids : (kids R prg pch rem v).card ≤ (kids R prg pch rem0 v).card := by
    zulcz
    zung
    rw [mem_kids] at hc ⊢
    exact ⟨hc.1, hc.2.1, hc.2.2.1, by_positivity⟩
  have hrec := sz_rec h (rem := rem) hvR
  have hvt : v ≠ t → v ≠ 0 := by
    intro hne h0
    exact AncX.not_top htv ztnr zthrq
  have hsv : sz R prg pch rem v ≤ n := by
    by_cases e : t = v
    · grind
    · have := sz_lt h htv e hvR; omega
  have hcard : (kids R prg pch rem v).card + (if v ≠ t then 1 else 0) ≤ D := by
    grind
  have hsum : ∑ c ∈ kids R prg pch rem v, sz R prg pch rem c +
      (if v ≠ t then n - sz R prg pch rem v else 0) = n - 1 := by
    grind
  rcases pigeon ztgmn _ _ D _ hsum hcard
    by_grind by_omega with
    ⟨c, hc, hc'⟩ | ⟨hne, hu⟩
  · have hc2 := hsmall c hc
    zubbi
    refine ⟨c, hc.1, htv.tail hc, ?_, ?_⟩
    · grind
    grind
  · grind
end sep
def p1 (R : ℕ) (ord prg pch rem : ℕ → ℕ) (s : ℕ → ℕ) (j : ℕ) : ℕ → ℕ :=
  if ord ztjz ≠ 0 ∧ rem (pch ztxxu) ≠ 1 then
    Function.update s ztbaso (s ztbaso + s ztxxu)
  else s

/-- The all-ones array. -/
def ones : ℕ → ℕ := fun _ => 1
section p1
variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h
variable {rem : ℕ → ℕ}
open Classical in
/-- Splitting the children sum at one position of the search order. -/
theorem sum_kids_split {v p r : ℕ} (hr : r < R) (hpr : pos r = p) :
    ∑ c ∈ (kids R prg pch rem v).filter (fun c => p ≤ pos c), sz R prg pch rem c =
      (if ChX R prg pch rem v r then sz R prg pch rem r else 0) +
        ∑ c ∈ (kids R prg pch rem v).filter (fun c => p + 1 ≤ pos c), sz R prg pch rem c := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  have hpt : ∀ c ∈ kids R prg pch rem v,
      (if p ≤ pos c then sz R prg pch rem c else 0) =
        (if c = r then sz R prg pch rem c else 0) +
          (if p + 1 ≤ pos c then sz R prg pch rem c else 0) := by
    zung
    zubbi
    by_cases hcr : c = r
    · simp_all
    · have hne : pos c ≠ p := fun e => hcr (h.pos_inj hc.1 hr ztvps)
      grind
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq']
  zucr
  by_cases hk : ChX R prg pch rem v r
  · rw [ite_eq_left ((mem_kids).2 hk), ite_eq_left hk]
  · rw [ite_eq_right (fun hh => hk ((mem_kids).1 hh)), ite_eq_right hk]

/-- **The size pass**, partial: after `j` steps, entry `u` is `1` plus the sizes of its children
at search positions `≥ R - j`. -/
theorem p1_fold {j : ℕ} (hj : j ≤ R) {u : ℕ} (hu : u < R) :
    ((List.range j).foldl ztilr ones) u =
      1 + ∑ c ∈ (kids R prg pch rem u).filter ztfrm, sz R prg pch rem c := by
  classical
  induction j generalizing u with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, ones, Nat.sub_zero]
    have : (kids R prg pch rem u).filter (fun c => R ≤ pos c) = ∅ := by
      zubcj
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_le]
      zuchg
      exact h.pos_lt c ((mem_kids).1 hc).1
    rw [this, Finset.sum_empty]
    rfl
  | succ j ih =>
    zugtu
    have hjR : j < R := by_omega
    zukek
    have hr : ord _ < R := h.ord_lt _ hp
    have hpr : pos ztxxu = R - ztl := by rw [h.pos_ord _ hp]; omega
    have ih' : ∀ v, v < R → ztmyb v =
        1 + ∑ c ∈ (kids R prg pch rem v).filter ztfrm, sz R prg pch rem c :=
      fun v hv => ih by_omega hv
    generalize (List.range j).foldl _ ones = s at ih' ⊢
    unfold p1
    generalize ord _ = r at hr hpr ⊢
    have hsplit := fun v => sum_kids_split h (rem := rem) (v := v) hr hpr
    have hth : R - ztl + 1 = R - j := by_omega
    -- the size of `r` is final
    have hsr : s r = sz R prg pch rem r := by
      rw [ih' r hr, sz_rec h hr]
      zucr
      apply Finset.sum_congr _ by_omega
      zubcj
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      zuchg
      zubbi
      have := h.pos_prg c hc.1 hc.2.1
      rw [hc.2.2.1, hpr] at this
      omega
    by_cases hc : r ≠ 0 ∧ rem ztkch ≠ 1
    · zulpw
      have hk : ChX R prg pch rem _ r := ⟨hr, hc.1, rfl, hc.2⟩
      by_cases hu' : u = prg r
      · subst hu'
        rw [Function.update_self, hsr, ih' _ hu, hsplit, ite_eq_left hk, hth]
        ring
      · rw [Function.update_of_ne hu', ih' u hu, hsplit,
          ite_eq_right (fun hh : ChX R prg pch rem u r => hu' hh.2.2.1.symm), hth, zero_add]
    · rw [ite_eq_right hc, ih' u hu, hsplit,
        ite_eq_right (fun hh : ChX R prg pch rem u r => hc ⟨hh.2.1, hh.2.2.2⟩), hth, zero_add]

/-- **The size pass**: after all `R` steps, entry `u` is `sz rem u`. -/
theorem p1_full {u : ℕ} (hu : u < R) :
    ((List.range R).foldl ztilr ones) u = sz R prg pch rem u := by
  rw [p1_fold h le_rfl hu, sz_rec h hu, Nat.sub_self]
  simp
end p1

/-! ## Pass 2: tops and cut candidates -/

/-- The state of the top pass: tops, best candidates and their values. -/
structure T3 where
  /-- The top of each region. -/
  top : ℕ → ℕ
  /-- The best cut candidate of each top (the top itself if none). -/
  best : ℕ → ℕ
  /-- The value of the best candidate. -/
  bestv : ℕ → ℕ

/-- Step `i` of the top pass (region `r = ord i`, sizes `S`). -/
def p2 (ord prg pch rem S : ℕ → ℕ) (st : T3) (i : ℕ) : T3 :=
  if ord i = 0 ∨ rem (pch ztbnh) = 1 then
    ⟨Function.update st.top ztbnh ztbnh, Function.update st.best ztbnh ztbnh,
      Function.update st.bestv ztbnh 0⟩
  else if st.bestv ztwsf <
      min ztbafk ztbapd then
    ⟨Function.update st.top ztbnh ztwsf,
      Function.update st.best ztwsf ztbnh,
      Function.update st.bestv ztwsf
        (min ztbafk ztbapd)⟩
  else ⟨Function.update st.top ztbnh ztwsf, st.best, st.bestv⟩

/-- The value of a cut candidate `c` of the component of `t`. -/
noncomputable def cval (R : ℕ) (prg pch rem : ℕ → ℕ) (t c : ℕ) : ℕ :=
  min ztpej ztimh

/-- The invariant of the top pass after `i` steps. -/
def P2Inv (R : ℕ) (pos prg pch rem : ℕ → ℕ) (i : ℕ) (st : T3) : Prop :=
  (∀ u, u < R → pos u < i → st.top u < R ∧ IsTop pch rem ztwfa ∧
      AncX R prg pch rem ztwfa u) ∧
  (∀ t, t < R → IsTop pch rem t → pos t < i →
    (∀ c, c < R → AncX R prg pch rem t c → c ≠ t → pos c < i →
        cval R prg pch rem t c ≤ st.bestv t) ∧
    ((st.best t = t ∧ st.bestv t = 0 ∧ ∀ c, c < R → AncX R prg pch rem t c → c ≠ t → i ≤ pos c) ∨
      (st.best t < R ∧ AncX R prg pch rem t ztqwv ∧ st.best t ≠ t ∧ pos ztqwv < i ∧
        st.bestv t = cval R prg pch rem t ztqwv)))
section p2
variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h
variable {rem S : ℕ → ℕ}

/-- A proper member of a component has a positive value. -/
theorem cval_pos {t c : ℕ} (hc : c < R) (htc : AncX R prg pch rem t c) (hne : c ≠ t) :
    1 ≤ cval R prg pch rem t c := by
  unfold cval
  have h1 := sz_pos h (rem := rem) hc
  have h2 := sz_lt h htc ztnr hc
  omega
variable {i : ℕ}
theorem p2_step (hi : i < R) (hS : ∀ u, u < R → S u = sz R prg pch rem u) {st : T3}
    (hI : P2Inv R pos prg pch rem i st) : P2Inv R pos prg pch rem ztg (p2 ord prg pch rem S st i) := by
  obtain ⟨hA, hB⟩ := hI
  have hr := h.ord_lt i hi
  have hpr : pos _ = i := h.pos_ord i hi
  unfold p2
  generalize ord i = r at hr hpr ⊢
  -- positions `< i + 1` are positions `< i` or `r`
  have hlt : ∀ u, u < R → pos u < i + 1 → pos u < i ∨ u = r := by
    zumhn
    by_cases e : pos u = i
    · exact Or.inr (h.pos_inj hu hr ztvps)
    omega
  by_cases htop : r = 0 ∨ rem ztkch = 1
  · rw [ite_eq_left htop]
    refine ⟨fun u hu hpu => ?_, fun t ht htt hpt => ?_⟩
    · zuhik
      · zuhzk
        grind
      · zugig
        zubvt
        zuewo
        exact ⟨hr, htop, ReflTransGen.refl⟩
    · rcases hlt t ht hpt with h1 | e
      · have hne : t ≠ r := by_grind
        zubvt
        simp only [Function.update_of_ne hne]
        obtain ⟨hB1, hB2⟩ := hB t ht htt h1
        -- `r` is a top, so it is no proper member of the component of `t`
        have hnm : ∀ c, AncX R prg pch rem t c → c ≠ t → c ≠ r := by
          intro c hc hct e
          zvmwe at hc hct
          exact AncX.not_top hc ztqay htop
        zumkm
        · zubec
          · grind
          grind
        · zuij
          · zuloa
            have := b3 c hc htc hct
            have hcr := hnm c htc hct
            by_contra hh
            exact hcr (h.pos_inj hc hr by_omega)
          grind
      · zugig
        zubvt
        zukph
        refine ⟨fun c hc htc hct hpc => ?_, Or.inl ⟨rfl, rfl, fun c hc htc hct => ?_⟩⟩
        · have := (AncX.pos_le h htc hc).2.2 ztqay
          omega
        · have := (AncX.pos_le h htc hc).2.2 ztqay
          omega
  · rw [ite_eq_right htop]
    have hrnt : ¬ IsTop pch rem r := htop
    simp only [not_or] at htop
    have hr0 := htop.1
    have hprR := h.prg_lt r hr hr0
    have hppr : pos (prg r) < i := by rw [← hpr]; exact h.pos_prg r hr hr0
    obtain ⟨htR, httop, htanc⟩ := hA _ hprR hppr
    generalize st.top _ = t at htR httop htanc ⊢
    have htr : AncX R prg pch rem t r := htanc.tail ⟨hr, hr0, rfl, htop.2⟩
    have htne : t ≠ r := by
      grind
    have hpt : pos t < i := by
      have := (AncX.pos_le h htr hr).2.2 htne
      omega
    have hval : min (S r) (S t - S r) = cval R prg pch rem t r := by
      rw [hS r hr, hS t htR]; rfl
    rw [hval]
    -- the top of `r`
    have hA' : ∀ u, u < R → pos u < i + 1 → Function.update st.top r t u < R ∧
        IsTop pch rem ztpyy ∧
          AncX R prg pch rem ztpyy u := by
      zumhn
      zuhik
      · zuhzk
        rw [Function.update_of_ne hne]
        grind
      · zugig
        zuewo
        grind
    -- members of other components are unaffected
    have hother : ∀ t', t' < R → IsTop pch rem t' → t' ≠ t → ¬ AncX R prg pch rem t' r := by
      intro t' ht' htt' hne hanc
      exact hne (top_unique h htt' httop hanc htr)
    have hvpos := cval_pos h hr htr (Ne.symm htne)
    by_cases hbig : st.bestv t < cval R prg pch rem t r
    · rw [ite_eq_left hbig]
      zugat

      · zudej

        · zugig
          zubvt
          zukph
          refine ⟨fun c hc htc hct hpc => ?_, by_grind⟩
          zubec
          · exact (hB1 c hc htc hct h2).trans hbig.le
          grind
        · zubvt
          simp only [Function.update_of_ne e]
          zumkm
          · zubec
            · zueow
            · zugcx
          · zuij
            · zuloa
              have := b3 c hc htc hct
              zucfp

            grind
      grind
    · rw [ite_eq_right hbig]
      unfold P2Inv
      zubvt
      zugat

      · zudej

        · zugig
          zumkm
          · zubec
            · zueow
            grind
          · zuij
            · omega
            grind
        · zumkm
          · zubec
            · zueow
            · zugcx
          · zuij
            · zuloa
              have := b3 c hc htc hct
              zucfp

            grind
      grind
theorem p2_fold (hi : i ≤ R) (hS : ∀ u, u < R → S u = sz R prg pch rem u) (st : T3) :
    P2Inv R pos prg pch rem i ((List.range i).foldl ztpcy st) := by
  induction i with
  | zero =>
    refine ztgy
  | succ i ih =>
    zugtu
    exact p2_step h by_omega hS by_grind

/-- **The top pass**: after all `R` steps, `top u` is the top of `u`, and for every top `t`,
either its component is `{t}` and `best t = t`, or `best t` is a proper member of the component
of maximal value. -/
theorem p2_full (hS : ∀ u, u < R → S u = sz R prg pch rem u) (st : T3) :
    let st' := (List.range R).foldl ztpcy st
    (∀ u, u < R → st'.top u < R ∧ IsTop pch rem ztwew ∧ AncX R prg pch rem ztwew u) ∧
    (∀ t, t < R → IsTop pch rem t →
      (∀ c, c < R → AncX R prg pch rem t c → c ≠ t → cval R prg pch rem t c ≤ st'.bestv t) ∧
      ((st'.best t = t ∧ ∀ c, c < R → AncX R prg pch rem t c → c = t) ∨
        (st'.best t < R ∧ AncX R prg pch rem t ztwev ∧ st'.best t ≠ t ∧
          st'.bestv t = cval R prg pch rem t ztwev))) := by
  intro st'
  obtain ⟨hA, hB⟩ := p2_fold h le_rfl hS st
  refine ⟨fun u hu => hA u hu (h.pos_lt u hu), fun t ht htt => ?_⟩
  obtain ⟨hB1, hB2⟩ := hB t ht htt (h.pos_lt t ht)
  refine ⟨fun c hc htc hct => hB1 c hc htc hct (h.pos_lt c hc), ?_⟩
  rcases hB2 with ⟨b1, -, b3⟩ | ⟨b1, b2, b3, -, b5⟩
  · refine Or.inl ⟨b1, fun c hc htc => ?_⟩
    by_contra hct
    have := b3 c hc htc hct
    have := h.pos_lt c hc
    omega
  grind
end p2
def hstep (D m : ℕ) : ℕ := ztdsz * m / D
variable (D m : ℕ)
theorem hstep_le : hstep D m ≤ m := by
  zuhqu

  · simp
  · exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ ztjkm)
theorem hstep_lt (hm : 1 ≤ m) : hstep D m < m := by
  zuhqu

  · omega
  · apply Nat.div_lt_of_lt_mul
    have : ztdsz * m < D * m := Nat.mul_lt_mul_of_pos_right by_omega by_omega
    omega
theorem hstep_mono (D : ℕ) {a b : ℕ} (hab : a ≤ b) : hstep D a ≤ hstep D b :=
  Nat.div_le_div_right (Nat.mul_le_mul_left _ hab)
theorem hstep_iter_mono (D n : ℕ) {a b : ℕ} (hab : a ≤ b) : ztyk^[n] a ≤ ztyk^[n] b := by
  induction n generalizing a b with
  | zero => exact hab
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (hstep_mono D hab)
theorem hstep_iter_anti {i j : ℕ} (hij : i ≤ j) : ztyk^[j] m ≤ ztyk^[i] m := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih =>
    zudtl
    exact (hstep_le D _).trans ih

/-- `m' ≤ hstep D m` as soon as `D m' ≤ (D - 1) m`. -/
theorem le_hstep {D m m' : ℕ} (hD : 1 ≤ D) (h : D * m' ≤ ztdsz * m) : m' ≤ hstep D m := by
  unfold hstep
  zuhkf
  grind
theorem hstep_exists (D K : ℕ) : ∃ i, ztyk^[i] K = 0 := by
  refine ⟨K, ?_⟩
  have : ztxbz := by
    zuibw
    induction i with
    | zero => left; simp
    | succ i ih =>
      zudtl
      rcases ih with h1 | h1
      · by_cases h0 : ztyk^[i] K = 0
        · right; zvmzn; exact Nat.le_zero.1 zttoo
        · left; have := hstep_lt D ztyxq by_omega; omega
      · right; zvmwp; exact Nat.le_zero.1 zttoo
  grind

/-- The number of rounds: the least `i` with `hstep D ^[i] K = 0`. -/
noncomputable def rounds (D K : ℕ) : ℕ := Nat.find ztton
theorem iter_rounds (D K : ℕ) : ztyk^[rounds D K] K = 0 := Nat.find_spec ztton

/-- A round index with a nonzero edge bound is below `rounds`. -/
theorem lt_rounds {D K i : ℕ} (h : 1 ≤ ztyk^[i] K) : i < rounds D K := by
  by_contra hle
  rw [not_lt] at hle
  have := hstep_iter_anti D K hle
  rw [iter_rounds] at this
  omega

/-- `D` rounds halve the edge bound. -/
theorem iter_D_half {D : ℕ} (hD : 1 ≤ D) (m : ℕ) : 2 * ztyk^[D] m ≤ m := by
  have key : ∀ i, i ≤ D → 2 * ztyk^[i] m ≤ m ∨ 2 * D * ztyk^[i] m + i * m ≤ 2 * D * m := by
    zug
    induction i with
    | zero => right; simp
    | succ i ih =>
      zudtl
      set x := ztyk^[i] m
      have hx : hstep D x ≤ x := hstep_le D x
      have hDx : D * hstep D x ≤ ztdsz * x := by
        unfold hstep
        have := Nat.div_mul_le_self (ztdsz * x) D
        grind
      rcases ih by_omega with h1 | h1
      · omega
      · by_cases h2 : 2 * x ≤ m
        · omega
        · right
          have e1 : ztdsz * x + x = D * x := by
            rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hD]
          nlinarith
  rcases key D le_rfl with h1 | h1
  · zubvv
  · nlinarith

/-- **The number of rounds**: at most `D ⌈log₂ (K + 1)⌉`. -/
theorem rounds_le {D : ℕ} (hD : 1 ≤ D) (K : ℕ) : rounds D K ≤ D * Nat.clog 2 ztbr := by
  have key : ∀ c m, m + 1 ≤ 2 ^ c → ztyk^[D * c] m = 0 := by
    intro c
    induction c with
    | zero => intro m hm; simp at hm; subst hm; simp
    | succ c ih =>
      zucng
      rw [Nat.mul_succ, Function.iterate_add_apply]
      have h1 := iter_D_half hD m
      have h2 : ztyk^[D] m + 1 ≤ 2 ^ c := by
        omega
      exact Nat.le_zero.1 ((hstep_iter_mono D (D * c) le_rfl).trans (ih _ h2).le)
  exact Nat.find_min' _ (key _ K zttav)
theorem rounds_zero (D : ℕ) : rounds D 0 = 0 :=
  Nat.le_zero.1 (Nat.find_min' _ by_simp)
structure RS where
  /-- Removed chords (`1`). -/
  rem : ℕ → ℕ
  /-- Chords cut in the previous round (`1`). -/
  pend : ℕ → ℕ
  /-- Active components, at their tops (`1`). -/
  act : ℕ → ℕ
  /-- The chord of the pending parent slot of an active component. -/
  cpar : ℕ → ℕ
  /-- The side of the pending slot: `0` low, `1` high, `2` the root. -/
  side : ℕ → ℕ
  /-- Decomposition nodes: parent code. -/
  dpar : ℕ → ℕ
  /-- Decomposition nodes: low child code. -/
  dlo : ℕ → ℕ
  /-- Decomposition nodes: high child code. -/
  dhi : ℕ → ℕ
  /-- Leaf parents. -/
  lpar : ℕ → ℕ
  /-- The root code. -/
  root : ℕ
  /-- The number of finished leaves. -/
  fin : ℕ

/-- The code of the component with top `x` in the current round: its leaf if it is a singleton,
otherwise the node of the chord cut in it. -/
def code (best pch : ℕ → ℕ) (x : ℕ) : ℕ := if best x = x then 2 * x + 1 else 2 * pch ztvex

/-- Chord `e` is cut in this round. -/
abbrev Chosen (σ : RS) (top best chOf : ℕ → ℕ) (e : ℕ) : Prop :=
  σ.rem e ≠ 1 ∧ σ.act ztwoz = 1 ∧ best ztwoz = chOf e

/-- The top of the low child component of a chord cut in the previous round. -/
def loTop (prg isdn chOf top : ℕ → ℕ) (e : ℕ) : ℕ :=
  if isdn ztjk = 1 then chOf e else top ztxom

/-- The top of the high child component of a chord cut in the previous round. -/
def hiTop (prg isdn chOf top : ℕ → ℕ) (e : ℕ) : ℕ :=
  if isdn ztjk = 1 then top ztxom else chOf e

/-- Chord pass: the new `pend`. -/
def nPend (K : ℕ) (chOf top best : ℕ → ℕ) (σ : RS) (e : ℕ) : ℕ :=
  if e < K then (if σ.pend e = 1 then 0 else if Chosen σ top best chOf e then 1 else σ.pend e)
  else σ.pend e

/-- One round of the decomposition. -/
def next (R K : ℕ) (prg pch isdn chOf top best : ℕ → ℕ) (σ : RS) : RS where
  rem e := if e < K then (if σ.pend e = 1 then σ.rem e else
    if Chosen σ top best chOf e then 1 else σ.rem e) else σ.rem e
  pend := nPend K chOf top best σ
  dpar e := if e < K then (if σ.pend e = 1 then σ.dpar e else
    if Chosen σ top best chOf e then
      (if σ.side ztwoz = 2 then 2 * e else 2 * σ.cpar ztwoz)
    else σ.dpar e) else σ.dpar e
  dlo e := if e < K then (if σ.pend e = 1 then code best pch (loTop prg isdn chOf top e)
    else σ.dlo e) else σ.dlo e
  dhi e := if e < K then (if σ.pend e = 1 then code best pch (hiTop prg isdn chOf top e)
    else σ.dhi e) else σ.dhi e
  act r := if r < R then (if top r = r then (if σ.act r = 1 then (if best r = r then 0 else σ.act r)
      else σ.act r)
    else if nPend K chOf top best σ ztkch = 1 then 1 else σ.act r) else σ.act r
  cpar r := if r < R then (if top r = r then (if σ.act r = 1 then
      (if best r = r then σ.cpar r else pch ztvew) else σ.cpar r)
    else if nPend K chOf top best σ ztkch = 1 then pch r else σ.cpar r) else σ.cpar r
  side r := if r < R then (if top r = r then (if σ.act r = 1 then
      (if best r = r then σ.side r else (if isdn ztvew = 1 then 1 else 0)) else σ.side r)
    else if nPend K chOf top best σ ztkch = 1 then (if isdn r = 1 then 0 else 1) else σ.side r)
    else σ.side r
  lpar r := if r < R then (if top r = r then (if σ.act r = 1 then
      (if best r = r then (if σ.side r = 2 then 2 * r + 1 else 2 * σ.cpar r) else σ.lpar r)
      else σ.lpar r) else σ.lpar r) else σ.lpar r
  root := if σ.act 0 = 1 then (if σ.side 0 = 2 then code best pch 0 else σ.root) else σ.root
  fin := σ.fin + ((range R).filter ztcvn).card

/-! ## The invariant -/

/-- Region `v` is on side `s` (`0` low, `1` high) of chord `e`: in the subtree of the child
endpoint `chOf e` iff that endpoint is the low endpoint (`isdn`) exactly when `s = 0`. -/
def OnSide (R : ℕ) (prg pch isdn chOf : ℕ → ℕ) (s e v : ℕ) : Prop :=
  AncX R prg pch rem0 ztjk v ↔ ztwpe
open Classical in
/-- The regions on side `s` of chord `e`. -/
noncomputable def sideSet (R : ℕ) (prg pch isdn chOf : ℕ → ℕ) (s e : ℕ) : Finset ℕ :=
  (range R).filter (OnSide R prg pch isdn chOf s e)

/-- The regions below a code (ghost `gc` for chord nodes). -/
def compOf (gc : ℕ → Finset ℕ) (x : ℕ) : Finset ℕ := if x % 2 = 0 then gc ztbhd else {x / 2}

/-- The parent code of a code. -/
def pcode (σ : RS) (x : ℕ) : ℕ := if x % 2 = 0 then σ.dpar ztbhd else σ.lpar ztbhd

/-- A code already placed: a removed chord, or a finished leaf. -/
def ValidC (R K : ℕ) (pch : ℕ → ℕ) (σ : RS) (x : ℕ) : Prop :=
  (x % 2 = 0 ∧ x / 2 < K ∧ σ.rem ztbhd = 1) ∨
    (x % 2 = 1 ∧ x / 2 < R ∧ IsTop pch σ.rem ztbhd ∧ σ.act ztbhd ≠ 1)

/-- **The round invariant** at the start of round `j`, with ghosts `gc` (the component in which a
removed chord was cut) and `cr` (the round in which it was cut). -/
structure RInv (R K D : ℕ) (prg pch isdn chOf : ℕ → ℕ) (j : ℕ) (σ : RS) (gc : ℕ → Finset ℕ)
    (cr : ℕ → ℕ) : Prop where
  i0 : ∀ e, e < K → σ.pend e = 1 → σ.rem e = 1
  i1 : ∀ e, e < K → σ.rem e = 1 →
    gc e ⊆ range R ∧ chOf e ∈ gc e ∧ prg ztjk ∈ gc e ∧ cr e < j ∧ cr e < rounds D K ∧
    ((σ.dpar e = 2 * e ∧ cr e = 0 ∧ σ.root = 2 * e ∧ gc e = range R) ∨
      (∃ p, p < K ∧ σ.rem p = 1 ∧ σ.dpar e = 2 * p ∧ cr p + 1 = cr e ∧ gc e ⊆ gc p))
  i2 : ∀ e, e < K → σ.rem e = 1 → σ.pend e ≠ 1 → ∀ s, s ≤ 1 →
    ValidC R K pch σ ztdde ∧
    compOf gc ztdde = gc e ∩ sideSet R prg pch isdn chOf s e ∧
    pcode σ ztdde = 2 * e
  i3 : ∀ e, e < K → σ.pend e = 1 → cr e + 1 = j ∧ ∀ s, s ≤ 1 → ∃ t, t < R ∧
    IsTop pch σ.rem t ∧ σ.act t = 1 ∧ σ.cpar t = e ∧ σ.side t = s ∧
    sub R prg pch σ.rem t = gc e ∩ sideSet R prg pch isdn chOf s e
  i4 : ∀ t, t < R → IsTop pch σ.rem t → σ.act t = 1 →
    (σ.side t = 2 ∧ t = 0 ∧ j = 0) ∨
    (σ.side t ≤ 1 ∧ σ.cpar t < K ∧ σ.pend ztqzp = 1 ∧
      sub R prg pch σ.rem t = gc ztqzp ∩ sideSet R prg pch isdn chOf (σ.side t) ztqzp)
  i5 : ∀ t, t < R → IsTop pch σ.rem t → σ.act t ≠ 1 →
    sub R prg pch σ.rem t = {t} ∧
    ((σ.lpar t = 2 * t + 1 ∧ σ.root = 2 * t + 1 ∧ K = 0) ∨
      (∃ p, p < K ∧ σ.rem p = 1 ∧ σ.lpar t = 2 * p ∧ cr p + 1 ≤ rounds D K ∧ t ∈ gc p))
  i6 : ∀ t, t < R → IsTop pch σ.rem t → σ.act t = 1 →
    sz R prg pch σ.rem t ≤ ztyk^[j] K + 1 ∧ (j = 0 ∨ 1 ≤ ztyk^[j - 1] K)
  i7 : j = 0 → (∀ e, e < K → σ.rem e ≠ 1) ∧ σ.act 0 = 1 ∧ σ.side 0 = 2
  i8 : 1 ≤ j → ValidC R K pch σ σ.root ∧ compOf gc σ.root = range R ∧ pcode σ σ.root = σ.root
  i9 : σ.fin = ((range R).filter ztbtz).card
section step
variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ}
variable (h : Rooted R K up dn ord pos prg pch)
variable (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch (chOf e) = e)
variable {σ : RS} {top best bestv : ℕ → ℕ}
variable (hT : ∀ u, u < R → top u < R ∧ IsTop pch σ.rem (top u) ∧ AncX R prg pch σ.rem (top u) u)
variable (hB : ∀ t, t < R → IsTop pch σ.rem t →
      ztpm ∧
      (ztvl ∨
        (best t < R ∧ AncX R prg pch σ.rem t ztmy ∧ best t ≠ t ∧
          bestv t = cval R prg pch σ.rem t ztmy)))
variable {j : ℕ} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
variable (hI : RInv R K D prg pch isdn chOf j σ gc cr)
include h hch hT hB hI
theorem top_of {u t : ℕ} (hu : u < R) (htop : IsTop pch σ.rem t)
    (hanc : AncX R prg pch σ.rem t u) : top u = t := by
  obtain ⟨-, h1, h2⟩ := hT u hu
  exact top_unique h h1 htop h2 hanc
variable {t : ℕ} {u : ℕ} {e : ℕ}
theorem top_self (ht : t < R) (htop : IsTop pch σ.rem t) : top t = t :=
  top_of h hch hT hB hI ht htop ReflTransGen.refl
theorem top_iff (hu : u < R) : top u = u ↔ IsTop pch σ.rem u := by
  constructor
  · grind
  · exact top_self h hch hT hB hI hu
theorem chOf_pch {s : ℕ} (hs : s < R) (h0 : s ≠ 0) : chOf zteuo = s := by
  zucxp

/-- The facts behind a chosen chord. -/
theorem chosen_facts (he : e < K) (hc : Chosen σ top best chOf e) :
    top ztjk < R ∧ IsTop pch σ.rem ztwoz ∧ σ.act ztwoz = 1 ∧
      best ztwoz = chOf e ∧ chOf e ≠ top ztjk ∧ ¬ IsTop pch σ.rem ztjk ∧
      AncX R prg pch σ.rem ztwoz ztjk ∧ chOf e < R ∧ chOf e ≠ 0 ∧
      pch ztjk = e ∧ σ.pend e ≠ 1 := by
  obtain ⟨hr, ha, hb⟩ := hc
  zucdr
  obtain ⟨t1, t2, t3⟩ := hT ztjk c1
  have hnt : ¬ IsTop pch σ.rem ztjk := by
    zugax
    · omega
    simp_all
  refine ⟨t1, t2, ha, hb, fun e' => hnt (e' ▸ t2), hnt, t3, c1, c2, c3, fun hp => hr (hI.i0 e he hp)⟩

/-- The chord cut in an active component that is not a singleton. -/
theorem cut_chosen (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1)
    (hbt : best t ≠ t) :
    best t < R ∧ AncX R prg pch σ.rem t ztmy ∧ best t ≠ 0 ∧ pch ztmy < K ∧
      chOf ztyjw = best t ∧ top ztmy = t ∧ Chosen σ top best chOf ztyjw ∧
      σ.rem ztyjw ≠ 1 := by
  obtain ⟨-, hB2⟩ := hB t ht htop
  rcases hB2 with ⟨e, -⟩ | ⟨b1, b2, b3, -⟩
  · omega
  have hnt : ¬ IsTop pch σ.rem ztmy := AncX.not_top b2 ztvak
  simp only [IsTop, not_or] at hnt
  have hch' := chOf_pch h hch hT hB hI b1 hnt.1
  have htop' := top_of h hch hT hB hI b1 htop b2
  refine ⟨b1, b2, hnt.1, h.pch_lt _ b1 hnt.1, hch', htop', ⟨hnt.2, ?_, ?_⟩, hnt.2⟩
  · simp_all
  simp_all

/-- A chosen chord is the parent chord of the best candidate of its component. -/
theorem chosen_unique {w : ℕ} (hw : w < R) (hw0 : w ≠ 0) (hc : Chosen σ top best chOf ztkci) :
    best ztwgs = w ∧ σ.act ztwgs = 1 := by
  have hch' := chOf_pch h hch hT hB hI hw hw0
  grind
theorem rem_next (he : e < K) :
    (next R K prg pch isdn chOf top best σ).rem e = 1 ↔
      σ.rem e = 1 ∨ Chosen σ top best chOf e := by
  simp only [next, ite_eq_left he]
  zueof
  · zuhmg
    have := hI.i0 e he hp
    omega
  · zuhmq
    by_cases hc : Chosen σ top best chOf e
    · grind
    · rw [ite_eq_right hc]; omega
theorem rem_mono (hr : σ.rem e = 1) : (next R K prg pch isdn chOf top best σ).rem e = 1 := by
  by_cases he : e < K
  · exact (rem_next h hch hT hB hI he).2 ztcgw
  · simp only [next, ite_eq_right he]; exact hr
theorem pend_next (he : e < K) :
    nPend K chOf top best σ e = 1 ↔ Chosen σ top best chOf e := by
  simp only [nPend, ite_eq_left he]
  zueof
  · zuhmg
    have := hI.i0 e he hp
    omega
  simp_all
theorem istop_next (hu : u < R) :
    IsTop pch (next R K prg pch isdn chOf top best σ).rem u ↔
      IsTop pch σ.rem u ∨ (u ≠ 0 ∧ Chosen σ top best chOf (pch u)) := by
  by_cases h0 : u = 0
  · tauto
  · have hpk := h.pch_lt u hu h0
    simp only [IsTop, h0, false_or, rem_next h hch hT hB hI hpk, ne_eq, not_false_eq_true, true_and]

/-- The ancestor relation after the round: the old one, avoiding the chosen chords. -/
theorem ancX_next {a v : ℕ} (hv : v < R) :
    AncX R prg pch (next R K prg pch isdn chOf top best σ).rem a v ↔
      AncX R prg pch σ.rem a v ∧ ∀ w, AncX R prg pch σ.rem a w → AncX R prg pch σ.rem w v →
        w ≠ a → ¬ Chosen σ top best chOf ztkci := by
  constructor
  · intro hav
    refine ⟨hav.mono (fun e he => rem_mono h hch hT hB hI he), fun w haw hwv hwa hc => ?_⟩
    zuboc
    have haw' := hav.upper h hwv.to0 haw.to0 hv
    rcases (AncX.back_iff h).1 haw' with e | ⟨-, hw0, hr, -⟩
    · omega
    · exact hr ((rem_next h hch hT hB hI ztrrh).2 ztdlf)
  · rintro ⟨hav, hkeep⟩
    refine hav.of_keep h fun w haw hwv hwa => ?_
    zuboc
    rcases (AncX.back_iff h).1 haw with e | ⟨-, hw0, hr, -⟩
    · omega
    · zudqd
      rcases (rem_next h hch hT hB hI ztrrh).1 h1 with h2 | h2
      · omega
      grind

/-- Within a component that is not cut, no chord is chosen. -/
theorem no_chosen_in {t w : ℕ} (_ht : t < R) (htop : IsTop pch σ.rem t)
    (hncut : σ.act t = 1 → best t = t) (hw : w < R) (htw : AncX R prg pch σ.rem t w) (hwt : w ≠ t) :
    ¬ Chosen σ top best chOf ztkci := by
  zuchg
  zuehi
  obtain ⟨hb, ha⟩ := chosen_unique h hch hT hB hI hw hw0 hc
  rw [top_of h hch hT hB hI hw htop htw] at hb ha
  omega

/-- In a cut component, the only chosen chord is the parent chord of the best candidate. -/
theorem chosen_in_cut {t w : ℕ} (_ht : t < R) (htop : IsTop pch σ.rem t) (hw : w < R)
    (htw : AncX R prg pch σ.rem t w) (hwt : w ≠ t) (hc : Chosen σ top best chOf ztkci) :
    w = best t := by
  zuehi
  obtain ⟨hb, -⟩ := chosen_unique h hch hT hB hI hw hw0 hc
  rw [top_of h hch hT hB hI hw htop htw] at hb
  omega
theorem sub_uncut (ht : t < R) (htop : IsTop pch σ.rem t)
    (hncut : σ.act t = 1 → best t = t) :
    sub R prg pch (next R K prg pch isdn chOf top best σ).rem t = sub R prg pch σ.rem t := by
  zuepb
  zujku

  · zubuq
    exact ztgta
  · zubuq
    refine ⟨hv, (ancX_next h hch hT hB hI hv).2 ⟨hav, fun w htw hwv hwt => ?_⟩⟩
    exact no_chosen_in h hch hT hB hI ht htop hncut (AncX.pos_le h hwv hv).1 htw hwt
open Classical in
/-- The part of a component below a member `c`. -/
theorem sub_member {t c : ℕ} (htc : AncX R prg pch σ.rem t c) :
    sub R prg pch σ.rem c = (sub R prg pch σ.rem t).filter (fun v => AncX R prg pch rem0 c v) := by
  zuepb
  zuhmz

  · rintro ⟨hv, hcv⟩
    exact ⟨⟨hv, (anc_member h htc hv).1 hcv |>.1⟩, ((anc_member h htc hv).1 hcv).2⟩
  · rintro ⟨⟨hv, htv⟩, hcv⟩
    exact ⟨hv, (anc_member h htc hv).2 ztuil⟩
theorem sub_cut_c (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1)
    (hbt : best t ≠ t) :
    sub R prg pch (next R K prg pch isdn chOf top best σ).rem ztmy = sub R prg pch σ.rem ztmy := by
  zubku
  zuepb
  zujku

  · zubuq
    exact ztgta
  · zubuq
    refine ⟨hv, (ancX_next h hch hT hB hI hv).2 ⟨hav, fun w hcw hwv hwc hc => ?_⟩⟩
    zuboc
    have htw := b2.trans hcw
    have hwt : w ≠ t := by
      zuchf
      zvmwe at hcw
      exact hbt (AncX.antisymm h hcw b2 ht)
    exact hwc (chosen_in_cut h hch hT hB hI ht htop hw htw hwt hc)
open Classical in
theorem sub_cut_t (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1)
    (hbt : best t ≠ t) :
    sub R prg pch (next R K prg pch isdn chOf top best σ).rem t =
      (sub R prg pch σ.rem t).filter (fun v => ¬ AncX R prg pch rem0 ztmy v) := by
  obtain ⟨b1, b2, -, -, -, -, hcho, -⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
  zuepb
  zuhmz

  · zubuq
    obtain ⟨htv, hkeep⟩ := (ancX_next h hch hT hB hI hv).1 hav
    refine ⟨⟨hv, htv⟩, fun hcv => ?_⟩
    have hcv' : AncX R prg pch σ.rem ztmy v := (anc_member h b2 hv).2 ztuil
    simp_all
  · rintro ⟨⟨hv, htv⟩, hncv⟩
    refine ⟨hv, (ancX_next h hch hT hB hI hv).2 ⟨htv, fun w htw hwv hwt hc => ?_⟩⟩
    zuboc
    have := chosen_in_cut h hch hT hB hI ht htop hw htw hwt hc
    zvmwk at hwv
    exact hncv hwv.to0
open Classical in
theorem sz_cut (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1)
    (hbt : best t ≠ t) :
    sz R prg pch (next R K prg pch isdn chOf top best σ).rem ztmy = sz R prg pch σ.rem ztmy ∧
    sz R prg pch (next R K prg pch isdn chOf top best σ).rem t + sz R prg pch σ.rem ztmy =
      sz R prg pch σ.rem t := by
  zubku
  refine ⟨by unfold sz; rw [sub_cut_c h hch hT hB hI ht htop hact hbt], ?_⟩
  unfold sz
  rw [sub_cut_t h hch hT hB hI ht htop hact hbt, sub_member h hch hT hB hI b2]
  zuocq
  exact Finset.card_filter_add_card_filter_not (fun v => AncX R prg pch rem0 ztmy v)
