module

public import Chazelle.Core.Facts2Trap

/-!
# WP-B, part 2: degree `≤ 4` for a box with segment obstacles

`SegObs.deg_le_four`: in the setting of `Chazelle.Core.Facts2Trap` (open box minus finitely many
non-horizontal segments meeting only at vertices, vertices of distinct heights), every region of a
finite family `G` of horizontal chords of the domain that contains the vertex chords (`FullAt`)
has at most four chords of `G` touching it.

The proof follows `FullDegInt.deg_le_four` (the interior of a polygon), with the trapezoid of
`Facts2Trap` in place of the polygon's: a chord touching the region `U ⊆ T` lies at the top height
of `T`, at the bottom height, or crosses `T` (then it contains the whole slice of `T`); at most
one crossing chord lies above `U`, and if there is one no chord at the top height touches `U`; at
the top height at most two chords touch `U`, one on each side of the top vertex (two on the same
side are joined through the open top side, whose obstacle points are vertices, hence the top
vertex, by distinct heights).  Symmetrically below.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (point_ext)

namespace SegObs

/-! ## Horizontal chords of an arbitrary domain -/

section Chords

variable {D : Set Point}

/-- A horizontal chord of the domain `D`. -/
def HCD (D c : Set Point) : Prop :=
  ∃ y a b : ℝ, IsHChordIn D y a b ∧ c = hseg y a b

/-- A point of a chord in the domain is strictly inside it. -/
theorem open_of_mem {y a b : ℝ} (h : IsHChordIn D y a b) {z : Point} (hz : z ∈ hseg y a b)
    (hzD : z ∈ D) : a < z.1 ∧ z.1 < b := by
  obtain ⟨hzy, hza, hzb⟩ := hz
  refine ⟨lt_of_le_of_ne hza fun e => h.left_not ?_, lt_of_le_of_ne hzb fun e => h.right_not ?_⟩
  all_goals grind

/-- Two chords sharing a point of the domain are equal. -/
theorem eq_of_common {c c' : Set Point} (hc : HCD D c) (hc' : HCD D c') {z : Point} (hz : z ∈ c)
    (hz' : z ∈ c') (hzD : z ∈ D) : c = c' := by
  obtain ⟨y, a, b, h, rfl⟩ := hc
  obtain ⟨y', a', b', h', rfl⟩ := hc'
  rcases Chazelle.Chain.hchordIn_inter h h' hz hz' with ⟨rfl, rfl, rfl⟩ | ⟨h1 | h1, -⟩
  · rfl
  · exact absurd (h1 ▸ hzD) h.left_not
  · exact absurd (h1 ▸ hzD) h.right_not

section
variable {y a b : ℝ} (h : IsHChordIn D y a b)
include h
/-- A chord contains every point of its line joined to it inside the domain. -/
theorem mem_of_joined {z : Point} (hz : z ∈ hseg y a b)
    (hzD : z ∈ D) {w : Point} (hw : w.2 = y)
    (hj : ∀ s : ℝ, min z.1 w.1 ≤ s → s ≤ max z.1 w.1 → ((s, y) : Point) ∈ D) :
    w ∈ hseg y a b := by
  obtain ⟨hza, hzb⟩ := open_of_mem h hz hzD
  refine ⟨hw, ?_, ?_⟩
  all_goals (grind [Chazelle.Chain.IsHChordIn])

/-- The points of a chord between two of its domain points are in the domain. -/
theorem between_mem {z z' : Point}
    (hz : z ∈ hseg y a b) (hzD : z ∈ D) (hz' : z' ∈ hseg y a b) (hz'D : z' ∈ D) {s : ℝ}
    (h1 : z.1 ≤ s) (h2 : s ≤ z'.1) : ((s, y) : Point) ∈ D :=
  h.open_mem s (by linarith [(open_of_mem h hz hzD).1]) (by linarith [(open_of_mem h hz' hz'D).2])


end

/-- The side of a chord point relative to a point off the domain, read off from the chord. -/
theorem side_iff {c : Set Point} (hc : HCD D c) {y₀ : ℝ} {w₀ : Point} (hw₀ : w₀ ∉ D)
    (hw₀y : w₀.2 = y₀) {z : Point} (hz : z ∈ c) (hzD : z ∈ D) (hzy : z.2 = y₀) :
    (∃ z' ∈ c, z' ∈ D ∧ z'.2 = y₀ ∧ z'.1 < w₀.1) ↔ z.1 < w₀.1 := by
  obtain ⟨y, a, b, h, rfl⟩ := hc
  have hy : y = y₀ := by rw [← hzy, hz.1]
  constructor
  · rintro ⟨z', hz', hz'D, -, hlt⟩
    by_contra hge
    push Not at hge
    have hne : z.1 ≠ w₀.1 := fun e => hw₀ (by
      grind)
    have := between_mem h hz' hz'D hz hzD hlt.le (lt_of_le_of_ne hge (Ne.symm hne)).le
    grind
  grind

end Chords

/-! ## Chords on a horizontal side of the trapezoid -/

variable {R : ℝ} {S : Set (Point × Point)}

namespace Trap

variable {q : Point} {sL sR : Point × Point} {y₁ y₂ : ℝ}

section
variable (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {Y : ℝ} (hY1 : y₁ ≤ Y) (hY2 : Y ≤ y₂) (hvert : ∀ w ∈ obs S, w.2 = Y → xAt sL Y < w.1 → w.1 < xAt sR Y → IsVert S w) {v : Point} (hv : IsVert S v) (hvY : v.2 = Y)
include hS h hY1 hY2 hvert v hv hvY
/-- **Two chords touching the closed trapezoid at a side height `Y`** (whose obstacle points on
the open side are vertices), on the same side of the vertex `v` at that height, are equal. -/
theorem side_chords_eq
    {c c' : Set Point} (hc : HCD (dom R S) c) (hc' : HCD (dom R S) c') {z z' : Point}
    (hz : z ∈ c) (hz' : z' ∈ c') (hzD : z ∈ dom R S) (hz'D : z' ∈ dom R S)
    (hzy : z.2 = Y) (hz'y : z'.2 = Y) (hzx : xAt sL Y ≤ z.1 ∧ z.1 ≤ xAt sR Y)
    (hz'x : xAt sL Y ≤ z'.1 ∧ z'.1 ≤ xAt sR Y) (hside : z.1 < v.1 ↔ z'.1 < v.1) : c = c' := by
  have hvD : v ∉ dom R S := fun hm => hm.2 (vert_mem_obs hv)
  have hYR : |Y| < R := hzy ▸ (box_of_dom hzD).2
  have hLb := (abs_le.1 (abs_xAt_le hS h.hL (h.botL.trans hY1) (hY2.trans h.topL))).1
  have hRb := (abs_le.1 (abs_xAt_le hS h.hR (h.botR.trans hY1) (hY2.trans h.topR))).2
  -- strictness at a domain point
  have hstrict : ∀ w : Point, w ∈ dom R S → w.2 = Y → xAt sL Y ≤ w.1 → w.1 ≤ xAt sR Y →
      xAt sL Y < w.1 ∧ w.1 < xAt sR Y := by
    intro w hw hwy h1 h2
    refine ⟨lt_of_le_of_ne h1 fun e => hw.2 (h.memL hS (hwy ▸ hY1) (hwy ▸ hY2) ?_),
      lt_of_le_of_ne h2 fun e => hw.2 (h.memR hS (hwy ▸ hY1) (hwy ▸ hY2) ?_)⟩
    all_goals grind
  have key : ∀ {c c' : Set Point} {z z' : Point}, HCD (dom R S) c → HCD (dom R S) c' → z ∈ c →
      z' ∈ c' → z ∈ dom R S → z' ∈ dom R S → z.2 = Y → z'.2 = Y →
      xAt sL Y ≤ z.1 ∧ z.1 ≤ xAt sR Y → xAt sL Y ≤ z'.1 ∧ z'.1 ≤ xAt sR Y → z.1 ≤ z'.1 →
      (z.1 < v.1 ↔ z'.1 < v.1) → c = c' := by
    intro c c' z z' hc hc' hz hz' hzD hz'D hzy hz'y hzx hz'x hle hside
    obtain ⟨y, a, b, hh, rfl⟩ := hc
    have hy : y = Y := by rw [← hzy, hz.1]
    have hs1 := hstrict z hzD hzy hzx.1 hzx.2
    have hs2 := hstrict z' hz'D hz'y hz'x.1 hz'x.2
    have hall : ∀ s : ℝ, z.1 ≤ s → s ≤ z'.1 → ((s, Y) : Point) ∈ dom R S := by
      intro s h1 h2
      refine ⟨⟨abs_lt.2 ⟨by linarith, by linarith⟩, hYR⟩, fun hobs => ?_⟩
      have hw := hvert _ hobs rfl (by linarith) (by linarith)
      have he := hS.distinct v _ hv hw (hvY ▸ hYR) hvY
      grind
    have hz'c : z' ∈ Visibility.hseg y a b := mem_of_joined hh hz hzD (by grind) (fun s h1 h2 => by
      grind)
    exact eq_of_common ⟨y, a, b, hh, rfl⟩ hc' hz'c hz' hz'D
  grind

/-- **At most two chords touch the closure of a set inside the closed trapezoid at a side
height `Y`** that carries a vertex `v` in the closed corridor. -/
theorem ncard_side_le_two {E : Set (Set Point)}
    (hE : ∀ c ∈ E, HCD (dom R S) c ∧ ∃ z ∈ c, z ∈ dom R S ∧ z.2 = Y ∧
      xAt sL Y ≤ z.1 ∧ z.1 ≤ xAt sR Y) : E.ncard ≤ 2 := by
  classical
  have hvD : v ∉ dom R S := fun hm => hm.2 (vert_mem_obs hv)
  let f : Set Point → Bool := fun c => decide (∃ z ∈ c, z ∈ dom R S ∧ z.2 = Y ∧ z.1 < v.1)
  have hinj : InjOn f E := by
    intro c hc c' hc' hff
    obtain ⟨hcH, z, hz, hzD, hzy, hzx⟩ := hE c hc
    obtain ⟨hc'H, z', hz', hz'D, hz'y, hz'x⟩ := hE c' hc'
    have h1 := side_iff hcH hvD hvY hz hzD hzy
    have h2 := side_iff hc'H hvD hvY hz' hz'D hz'y
    have hside : z.1 < v.1 ↔ z'.1 < v.1 := by
      grind
    exact h.side_chords_eq hS hY1 hY2 hvert hv hvY hcH hc'H hz hz' hzD hz'D hzy hz'y hzx hz'x hside
  have hBool : (Set.univ : Set Bool).ncard = 2 := by
    rw [ncard_univ, Nat.card_eq_fintype_card]; rfl
  calc E.ncard ≤ (Set.univ : Set Bool).ncard :=
        ncard_le_ncard_of_injOn f (fun _ _ => mem_univ _) hinj
    _ = 2 := hBool


end

end Trap

/-! ## The degree bound -/

/-- **Degree `≤ 4`**: every region of a finite family of horizontal chords of the domain that
contains the vertex chords is touched by at most four of them. -/
theorem deg_le_four (hS : Good R S) {G : Set (Set Point)} (hG : ∀ c ∈ G, HCD (dom R S) c)
    (hGfin : G.Finite) (hfull : FullAt R S G) {U : Set Point}
    (hU : U ∈ regionsIn (dom R S) G) :
    {c | c ∈ G ∧ TouchesIn (dom R S) c U}.ncard ≤ 4 := by
  classical
  set D := dom R S with hD
  obtain ⟨q, hqf, rfl⟩ := hU
  obtain ⟨sL, sR, y₁, y₂, h⟩ := exists_trap hS hfull hqf.1 hqf.2
  set T := tr sL sR y₁ y₂ with hTdef
  set U := connectedComponentIn (freeIn D G) q with hUdef
  have hUT : U ⊆ T := h.region_subset hS hfull hqf
  have hTD : T ⊆ D := h.tr_subset_dom hS
  have hqT : q ∈ T := hUT (mem_connectedComponentIn hqf)
  have hfreeU : U ⊆ freeIn D G := connectedComponentIn_subset _ _
  have hcl : closure U ⊆ ctr sL sR y₁ y₂ :=
    (closure_mono hUT).trans (closure_tr_subset _ _ _ _)
  have hqy₁ : y₁ < q.2 := hqT.1
  have hqy₂ : q.2 < y₂ := hqT.2.1
  -- a domain point of the closed trapezoid at a middle height is inside
  have hmid : ∀ z ∈ D, z ∈ ctr sL sR y₁ y₂ → y₁ < z.2 → z.2 < y₂ → z ∈ T := by
    intro z hzD hzC hz1 hz2
    obtain ⟨h1, h2, h3, h4⟩ := hzC
    exact ⟨hz1, hz2, lt_of_le_of_ne h3 fun e => hzD.2 (h.memL hS h1 h2 e.symm),
      lt_of_le_of_ne h4 fun e => hzD.2 (h.memR hS h1 h2 e)⟩
  -- a chord meeting `T` contains its whole slice
  have hslice : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → ∀ w ∈ T, w.2 = z.2 → w ∈ c := by
    intro c hc z hz hzT w hwT hwz
    obtain ⟨y, a, b, hh, rfl⟩ := hG c hc
    have hzy : z.2 = y := hz.1
    refine mem_of_joined hh hz (hTD hzT) (hwz.trans hzy) fun s h1 h2 => hTD ?_
    have hseg : Chazelle.segment z w ⊆ T :=
      Geometry.segment_subset_of_convex (convex_tr _ _ _ _) hzT hwT
    apply hseg
    rw [Visibility.segment_horizontal_eq_hseg hwz.symm]
    exact ⟨hzy.symm, h1, h2⟩
  -- `U` is on one side of a chord crossing `T`
  have hno : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → ∀ p ∈ U, p.2 ≠ z.2 := fun c hc z hz hzT p hp he =>
    (hfreeU hp).2 ⟨c, hc, hslice c hc z hz hzT p (hUT hp) he⟩
  have hUc := (isPreconnected_connectedComponentIn : IsPreconnected U)
  have hbelow : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → q.2 < z.2 → ∀ p ∈ U, p.2 < z.2 := by
    intro c hc z hz hzT hqz
    have := hUc.subset_left_of_subset_union (u := {p : Point | p.2 < z.2})
      (v := {p : Point | z.2 < p.2}) (isOpen_lt continuous_snd continuous_const)
      (isOpen_lt continuous_const continuous_snd)
      (Set.disjoint_left.2 fun p (h1 : _ < _) (h2 : _ < _) => lt_asymm h1 h2)
      (fun p hp => (lt_or_gt_of_ne (hno c hc z hz hzT p hp)).elim Or.inl Or.inr)
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    exact fun p hp => this hp
  have habove : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → z.2 < q.2 → ∀ p ∈ U, z.2 < p.2 := by
    intro c hc z hz hzT hqz
    have := hUc.subset_left_of_subset_union (u := {p : Point | z.2 < p.2})
      (v := {p : Point | p.2 < z.2}) (isOpen_lt continuous_const continuous_snd)
      (isOpen_lt continuous_snd continuous_const)
      (Set.disjoint_left.2 fun p (h1 : _ < _) (h2 : _ < _) => lt_asymm h1 h2)
      (fun p hp => (lt_or_gt_of_ne (hno c hc z hz hzT p hp)).elim Or.inr Or.inl)
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    exact fun p hp => this hp
  have hclle : ∀ y : ℝ, (∀ p ∈ U, p.2 < y) → ∀ p ∈ closure U, p.2 ≤ y := fun y hy =>
    fun p hp => closure_minimal (fun x hx => (hy x hx).le)
      (isClosed_le continuous_snd continuous_const) hp
  have hclge : ∀ y : ℝ, (∀ p ∈ U, y < p.2) → ∀ p ∈ closure U, y ≤ p.2 := fun y hy =>
    fun p hp => closure_minimal (fun x hx => (hy x hx).le)
      (isClosed_le continuous_const continuous_snd) hp
  -- the two classes of exit chords
  set E₁ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ (z.2 = y₂ ∨ (q.2 < z.2 ∧ z.2 < y₂))}
    with hE₁
  set E₂ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ (z.2 = y₁ ∨ (y₁ < z.2 ∧ z.2 < q.2))}
    with hE₂
  have hsub : {c | c ∈ G ∧ TouchesIn D c U} ⊆ E₁ ∪ E₂ := by
    rintro c ⟨hc, z, ⟨hz, hzD⟩, hzU⟩
    obtain ⟨h1, h2, -, -⟩ := hcl hzU
    rcases h2.lt_or_eq with h2 | h2
    · rcases h1.lt_or_eq with h1 | h1
      · have hzT := hmid z hzD (hcl hzU) h1 h2
        rcases lt_or_gt_of_ne (hno c hc z hz hzT q (mem_connectedComponentIn hqf)) with h3 | h3
        · exact Or.inl ⟨hc, z, hz, hzD, hzU, Or.inr ⟨h3, h2⟩⟩
        · exact Or.inr ⟨hc, z, hz, hzD, hzU, Or.inr ⟨h1, h3⟩⟩
      · exact Or.inr ⟨hc, z, hz, hzD, hzU, Or.inl h1.symm⟩
    · exact Or.inl ⟨hc, z, hz, hzD, hzU, Or.inl h2⟩
  -- at most two chords above
  have hE₁ : E₁.ncard ≤ 2 := by
    by_cases hA : ∃ c₀ ∈ E₁, ∃ z₀ ∈ c₀, z₀ ∈ D ∧ z₀ ∈ closure U ∧ q.2 < z₀.2 ∧ z₀.2 < y₂
    · obtain ⟨c₀, hc₀, z₀, hz₀, hz₀D, hz₀U, hq0, h0⟩ := hA
      have hz₀T := hmid z₀ hz₀D (hcl hz₀U) (hqy₁.trans hq0) h0
      have hU0 := hbelow c₀ hc₀.1 z₀ hz₀ hz₀T hq0
      have hsub1 : E₁ ⊆ {c₀} := by
        rintro c ⟨hc, z, hz, hzD, hzU, hzc⟩
        have hz0 := hclle _ hU0 z hzU
        have hmz : q.2 < z.2 ∧ z.2 < y₂ := by
          grind
        have hzT := hmid z hzD (hcl hzU) (hqy₁.trans hmz.1) hmz.2
        have hUz := hbelow c hc z hz hzT hmz.1
        have hz0' := hclle _ hUz z₀ hz₀U
        have heq : z₀.2 = z.2 := le_antisymm hz0' hz0
        have hz₀c := hslice c hc z hz hzT z₀ hz₀T heq
        exact eq_of_common (hG c hc) (hG c₀ hc₀.1) hz₀c hz₀ hz₀D
      calc E₁.ncard ≤ ({c₀} : Set (Set Point)).ncard := ncard_le_ncard hsub1 (finite_singleton _)
        _ ≤ 2 := by rw [ncard_singleton]; norm_num
    · push Not at hA
      have htop : ∀ c ∈ E₁, ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ z.2 = y₂ := by
        rintro c hc
        obtain ⟨hcG, z, hz, hzD, hzU, hzc⟩ := hc
        rcases hzc with e | e
        · exact ⟨z, hz, hzD, hzU, e⟩
        · exact absurd e.2 (not_lt.2 (hA c ⟨hcG, z, hz, hzD, hzU, Or.inr e⟩ z hz hzD hzU e.1))
      obtain ⟨v, hv, hvy, -⟩ := h.top_vertex
      refine h.ncard_side_le_two hS h.y₁_lt_y₂.le le_rfl
        (fun w hw hwy h3 h4 => h.top_side_vert hS hw hwy h3 h4) hv hvy fun c hc => ?_
      obtain ⟨z, hz, hzD, hzU, hzy⟩ := htop c hc
      obtain ⟨-, -, h3, h4⟩ := hcl hzU
      rw [hzy] at h3 h4
      exact ⟨hG c hc.1, z, hz, hzD, hzy, h3, h4⟩
  -- at most two chords below
  have hE₂ : E₂.ncard ≤ 2 := by
    by_cases hA : ∃ c₀ ∈ E₂, ∃ z₀ ∈ c₀, z₀ ∈ D ∧ z₀ ∈ closure U ∧ y₁ < z₀.2 ∧ z₀.2 < q.2
    · obtain ⟨c₀, hc₀, z₀, hz₀, hz₀D, hz₀U, h0, hq0⟩ := hA
      have hz₀T := hmid z₀ hz₀D (hcl hz₀U) h0 (hq0.trans hqy₂)
      have hU0 := habove c₀ hc₀.1 z₀ hz₀ hz₀T hq0
      have hsub1 : E₂ ⊆ {c₀} := by
        rintro c ⟨hc, z, hz, hzD, hzU, hzc⟩
        have hz0 := hclge _ hU0 z hzU
        have hmz : y₁ < z.2 ∧ z.2 < q.2 := by
          grind
        have hzT := hmid z hzD (hcl hzU) hmz.1 (hmz.2.trans hqy₂)
        have hUz := habove c hc z hz hzT hmz.2
        have hz0' := hclge _ hUz z₀ hz₀U
        have heq : z₀.2 = z.2 := le_antisymm hz0 hz0'
        have hz₀c := hslice c hc z hz hzT z₀ hz₀T heq
        exact eq_of_common (hG c hc) (hG c₀ hc₀.1) hz₀c hz₀ hz₀D
      calc E₂.ncard ≤ ({c₀} : Set (Set Point)).ncard := ncard_le_ncard hsub1 (finite_singleton _)
        _ ≤ 2 := by rw [ncard_singleton]; norm_num
    · push Not at hA
      have hbot : ∀ c ∈ E₂, ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ z.2 = y₁ := by
        rintro c hc
        obtain ⟨hcG, z, hz, hzD, hzU, hzc⟩ := hc
        rcases hzc with e | e
        · exact ⟨z, hz, hzD, hzU, e⟩
        · exact absurd e.2 (not_lt.2 (hA c ⟨hcG, z, hz, hzD, hzU, Or.inr e⟩ z hz hzD hzU e.1))
      obtain ⟨v, hv, hvy, -⟩ := h.bot_vertex
      refine h.ncard_side_le_two hS le_rfl h.y₁_lt_y₂.le
        (fun w hw hwy h3 h4 => h.bot_side_vert hS hw hwy h3 h4) hv hvy fun c hc => ?_
      obtain ⟨z, hz, hzD, hzU, hzy⟩ := hbot c hc
      obtain ⟨-, -, h3, h4⟩ := hcl hzU
      rw [hzy] at h3 h4
      exact ⟨hG c hc.1, z, hz, hzD, hzy, h3, h4⟩
  have hfin12 : (E₁ ∪ E₂).Finite :=
    (hGfin.subset fun c hc => hc.1).union (hGfin.subset fun c hc => hc.1)
  calc {c | c ∈ G ∧ TouchesIn D c U}.ncard ≤ (E₁ ∪ E₂).ncard := ncard_le_ncard hsub hfin12
    _ ≤ E₁.ncard + E₂.ncard := ncard_union_le _ _
    _ ≤ 4 := by omega

end SegObs

end

end Chazelle.Core
