module

public import Chazelle.Chain.Boundary
public import Chazelle.Jordan.Winding
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# Sides of the double boundary: winding numbers, the corrected walk, and Lemma 2.1

This file applies the integer winding numbers of `Chazelle.Jordan.Winding` to the box model of
the subchain visibility map (`docs/design-subchain-model.md`, `Chazelle.Chain.Boundary`), and
proves the side-aware form of Chazelle's Lemma 2.1 for a corrected boundary walk.

## Winding numbers of the boundary walk

* `sideWindSum_boundaryWalk`: the winding number of `boundaryWalk C` equals that of the box
  polygon at every point (the doubled chain and the doubled slit cancel, now in `ℤ`);
* `sideWindSum_boxPoly`: the box polygon (counterclockwise) has winding number `1` on the
  half-open square `[-R, R) × [-R, R)` and `0` elsewhere;
* `sideWindSum_boundaryWalk_of_mem_dom` / `sideWindSum_boundaryWalk_eq_zero`: **the boundary walk
  has winding number `s₀ = 1` on `dom C` and `0` off `dom C ∪` walk.**

## The split walks of a chord

* `sideWind_chord_split`: for the two closed walks `Γ₁ = a, Q, b` and `Γ₂ = b, P, a` of
  `chord_splits_walk`, `windSum Γ₁ + windSum Γ₂ = windSum (boundaryWalk C)` everywhere, and each
  `windSum Γᵢ` is constant on every preconnected subset of `dom C \ c`.

**Warning (the values of `windSum Γ₁`).**  With `boundaryWalk C` as defined in
`Chazelle.Chain.Boundary`, the values of `windSum Γ₁` on `dom C \ c` are *not* always in
`{0, 1}`.  Example: the chain `v₀ = (1, 0)`, `v₁ = (0, 1)`, `v₂ = (-1, 0)` (top vertex `v₁`)
and the chord `c = [v₂, v₀]`.  The chain part of `boundaryWalk` is `v₁, v₂, v₁, v₀, v₁`, and
the only split at the endpoints of `c` gives `Γ₁ = v₂, v₁, v₀` (clockwise, winding `-1` in the
triangle `v₀ v₁ v₂`) and `Γ₂ = v₀, v₁, slitTop, box, slitTop, v₁, v₂` (winding `2` in the
triangle).  The reason is that at the top vertex `boundaryWalk` goes down the slit and then to
`v_{T+1}` in every case, while the geometric boundary of `dom C` must turn to the neighbour
which is first clockwise from the slit.  For the same reason the side-aware Lemma 2.1 fails for
`boundaryWalk` (the left sectors of its passages through the top vertex overlap).  The
corrected walk `sideWalk` below fixes the order at the top vertex.

## Circular order and left sectors

* `sideCcw B X A`: the direction `X` is strictly inside the counterclockwise arc from `B` to `A`
  (convex, reflex, half-turn and full-turn cases), with the sub-arc, asymmetry, rotation and
  coverage lemmas `sideCcw_sub_left`, `sideCcw_sub_right`, `sideCcw_asymm`, `sideCcw_rotate`,
  `sideCcw_or`;
* `sideLeftOf a v b x`: `x` is in the open left sector of the corner `a → v → b`;
  `sideSector` turns it into a `SectorSide` of `Chazelle.Jordan.Local`.

## Positions on a closed walk; the generic split

A *position* `(p, t)` (`p < W.n`, `0 ≤ t < 1`) of a closed walk `W` is the point
`sidePt W p t` on edge `p`; `sideLeft W p t` is its open left sector.  `SideClean`,
`SideSectorIn` and `SideAttach` (a segment leaving the position into its left sector) are the
local notions.  `sideArc_chain` chains the left sides of all positions of an arc of `W` into one
connected component, and **`sideArc_split`** shows: if a segment `[a, b]` attached at two
positions `A`, `B` separates `D₀`, the positions strictly inside the arc `A → B` face one
component `K₁` of `D₀ \ [a, b]`, those inside `B → A` face another component `K₂ ≠ K₁`.

## The corrected walk

`sideWalk β`: the box block (top of the slit, the four corners counterclockwise, top of the
slit), then the tour of the double boundary of the chain from the top vertex, leaving it towards
`v_{T+1}` (`β = true`) or `v_{T-1}` (`β = false`), and back up the slit.  `SideGood β` is the
order condition at the top vertex; `sideBeta` is the correct choice and `sideGood_sideBeta`
proves the condition for it.  `sideWalk_nd`, `sideWalk_trace`, `sideWalk_clean` and
`sideWalk_disj` are the hypotheses of the generic split for this walk.

## Main results

* **`side_lemma21`** / **`side_lemma21_sideBeta`** (side-aware Lemma 2.1): for chords `c ≠ d`
  attached at `A, B` and `D₁, D₂`, the positions `D₁` and `D₂` lie in the same arc of the walk
  cut at `A` and `B` (keys `p + t`, cyclic betweenness `sideInArc`): *no chord joins the two
  arcs of the double boundary cut by `c`*;
* **`side_attach_exists`**: every chord is attached to `sideWalk β` at two positions with
  distinct points (its endpoints); **`sideAttach_unique`**: at a given point the attaching
  position is unique;
* **`sideWindSum_sideWalk`**: the corrected walk has the winding number of `boundaryWalk` (`1` on
  `dom C`, `0` off `dom C ∪ set ∪ slit ∪ perimeter`).
-/

namespace Chazelle.Chain

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one lerp_mem_segment point_ext
  point_ext_iff det_lerp det_lerp_self)

variable (C : Chain)

/-! ### The winding number of the boundary walk -/

/-! ### The split walks of a chord (Lemma 2.1, winding form) -/

/-! ### Circular order of directions -/

omit C in
/-- The cross product `u.1 v.2 - u.2 v.1`. -/
def sideCross (u v : Point) : ℝ := u.1 * v.2 - u.2 * v.1

omit C in
/-- The dot product. -/
def sideDot (u v : Point) : ℝ := u.1 * v.1 + u.2 * v.2

omit C in
/-- `X` lies strictly inside the counterclockwise arc of directions from `B` to `A`: the convex
case (`A` less than a half-turn from `B`), the reflex case, the half-turn case, and the full-turn
case (`A` in the direction of `B`: every direction except that of `B`). -/
def sideCcw (B X A : Point) : Prop :=
  (0 < sideCross B A ∧ 0 < sideCross B X ∧ 0 < sideCross X A) ∨
  (sideCross B A < 0 ∧ (0 < sideCross B X ∨ 0 < sideCross X A)) ∨
  (sideCross B A = 0 ∧ sideDot B A < 0 ∧ 0 < sideCross B X) ∨
  (sideCross B A = 0 ∧ 0 < sideDot B A ∧ (sideCross B X ≠ 0 ∨ sideDot B X < 0))

omit C in
theorem sideCross_self (u : Point) : sideCross u u = 0 := by ufring sideCross

omit C in
theorem sideCross_swap (u v : Point) : sideCross v u = -sideCross u v := by ufring sideCross

omit C in
theorem sideDot_comm (u v : Point) : sideDot v u = sideDot u v := by ufring sideDot

omit C in
/-- The Plücker relation for four vectors of the plane. -/
theorem side_plucker (B X Y A : Point) :
    sideCross B X * sideCross Y A = sideCross B Y * sideCross X A + sideCross B A * sideCross Y X := by
  ufring sideCross

omit C in
theorem side_dotCross (B X A : Point) :
    sideDot B X * sideCross B A = sideDot B B * sideCross X A + sideCross B X * sideDot B A := by
  ufring sideCross sideDot

omit C in
theorem side_lagrange (B X : Point) :
    sideCross B X ^ 2 + sideDot B X ^ 2 = sideDot B B * sideDot X X := by
  ufring sideCross sideDot

omit C in
theorem sideDot_self_pos {u : Point} (h : u ≠ 0) : 0 < sideDot u u := by
  unfold sideDot
  by_contra h'
  apply h
  have h1 : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
  have h2 : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
  exact Prod.ext h1 h2

omit C in
/-- `B` is not in the direction of `A` (the arc from `B` to `A` is not a full turn). -/
def sideNonSpike (B A : Point) : Prop := ¬ (sideCross B A = 0 ∧ 0 < sideDot B A)

omit C in
/-- A direction on the closed ray of `A` is not strictly inside an arc ending at `A`. -/
theorem sideCcw_not_ray_right {B A Y : Point} (hA : A ≠ 0) (hY : sideCross Y A = 0)
    (hYd : 0 ≤ sideDot Y A) : ¬ sideCcw B Y A := by
  have hAA := sideDot_self_pos hA
  -- `B × Y` is a nonnegative multiple of `B × A`
  have e1 : sideDot A A * sideCross B Y = sideDot Y A * sideCross B A := by
    unfold sideCross sideDot at *; linear_combination (-(A.1 * B.1 + A.2 * B.2)) * hY
  unfold sideCcw
  rintro (⟨h1, h2, h3⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · rw [hY] at h3; exact lt_irrefl _ h3
  · nlinarith [mul_nonneg hYd (le_of_lt (neg_pos.2 h1))]
  · rw [hY] at h2; exact lt_irrefl _ h2
  · rw [h1, mul_zero] at e1
    have : sideCross B Y = 0 := by
      rcases mul_eq_zero.1 e1 with h | h
      · linarith
      · exact h
    rw [this] at h3; exact lt_irrefl _ h3
  · rw [h1, mul_zero] at e1
    have hBY : sideCross B Y = 0 := by
      rcases mul_eq_zero.1 e1 with h | h
      · linarith
      · exact h
    -- `B · Y ≥ 0`
    have e2 : sideDot A A * sideDot B Y = sideDot Y A * sideDot B A := by
      unfold sideCross sideDot at *; linear_combination (B.1 * A.2 - B.2 * A.1) * hY
    rcases h3 with h3 | h3
    · exact h3 hBY
    · nlinarith [mul_nonneg hYd h2.le]

omit C in
theorem side_dotDot (B Y A : Point) :
    sideDot B Y * sideDot B A + sideCross B Y * sideCross B A = sideDot B B * sideDot Y A := by
  ufring sideCross sideDot

omit C in
/-- A direction on the closed ray of `B` is not strictly inside an arc starting at `B`. -/
theorem sideCcw_not_ray_left {B A Y : Point} (hB : B ≠ 0) (hY : sideCross B Y = 0)
    (hYd : 0 ≤ sideDot B Y) : ¬ sideCcw B Y A := by
  have hBB := sideDot_self_pos hB
  have e1 := side_dotCross B Y A
  rw [hY, zero_mul, add_zero] at e1
  unfold sideCcw
  rintro (⟨h1, h2, h3⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · rw [hY] at h2; exact lt_irrefl _ h2
  · rw [hY] at h2; exact lt_irrefl _ h2
  · nlinarith [mul_nonneg hYd (le_of_lt (neg_pos.2 h1))]
  · rw [hY] at h3; exact lt_irrefl _ h3
  · rcases h3 with h3 | h3
    · exact h3 hY
    · linarith

omit C in
/-- **Sub-arc (left part).**  If `X` is inside the arc from `B` to `A`, the arc from `B` to `X`
is contained in it. -/
theorem sideCcw_sub_left {B X Y A : Point} (hB : B ≠ 0) (h1 : sideCcw B X A)
    (h2 : sideCcw B Y X) : sideCcw B Y A := by
  have hBB := sideDot_self_pos hB
  have P1 := side_plucker B X Y A
  have D1 := side_dotCross B X A
  rcases h1 with ⟨hbA, hbX, hxA⟩ | ⟨hbA, hX⟩ | ⟨hbA, hdA, hbX⟩ | ⟨hbA, hdA, hX⟩
  · rcases h2 with ⟨-, hbY, hyX⟩ | ⟨hbX', -⟩ | ⟨hbX', -, -⟩ | ⟨hbX', -, -⟩
    · refine Or.inl ⟨hbA, hbY, ?_⟩
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hbY hxA, mul_pos hbA hyX, mul_nonpos_of_nonneg_of_nonpos hbX.le hc]
    · linarith
    · linarith
    · linarith
  · refine Or.inr (Or.inl ⟨hbA, ?_⟩)
    rcases h2 with ⟨-, hbY, -⟩ | ⟨hbX, h2⟩ | ⟨-, -, hbY⟩ | ⟨hbX, hdX, -⟩
    · exact Or.inl hbY
    · rcases h2 with hbY | hyX
      · exact Or.inl hbY
      · by_cases hbY : 0 < sideCross B Y
        · exact Or.inl hbY
        · push Not at hbY
          right
          have hxA : 0 < sideCross X A := by
            rcases hX with h | h
            · linarith
            · exact h
          by_contra hc
          push Not at hc
          nlinarith [mul_nonpos_of_nonpos_of_nonneg hbY hxA.le, mul_pos (neg_pos.2 hbA) hyX,
            mul_nonneg (neg_pos.2 hbX).le (neg_nonneg.2 hc)]
    · exact Or.inl hbY
    · exfalso
      have hxA : 0 < sideCross X A := by
        rcases hX with h | h
        · rw [hbX] at h; exact absurd h (lt_irrefl _)
        · exact h
      rw [hbX, zero_mul, add_zero] at D1
      nlinarith [mul_pos hdX (neg_pos.2 hbA), mul_pos hBB hxA]
  · rcases h2 with ⟨-, hbY, -⟩ | ⟨hbX', -⟩ | ⟨hbX', -, -⟩ | ⟨hbX', -, -⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hbA, hdA, hbY⟩))
    · linarith
    · linarith
    · linarith
  · refine Or.inr (Or.inr (Or.inr ⟨hbA, hdA, ?_⟩))
    by_contra hc
    push Not at hc
    exact sideCcw_not_ray_left hB hc.1 hc.2 h2

omit C in
/-- **Sub-arc (right part).**  If `X` is inside the arc from `B` to `A`, the arc from `X` to `A`
is contained in it. -/
theorem sideCcw_sub_right {B X Y A : Point} (hB : B ≠ 0) (hX : X ≠ 0) (hA : A ≠ 0)
    (h1 : sideCcw B X A) (h2 : sideCcw X Y A) : sideCcw B Y A := by
  have hBB := sideDot_self_pos hB
  have hXX := sideDot_self_pos hX
  have hAA := sideDot_self_pos hA
  have P1 := side_plucker B X Y A
  rcases h1 with ⟨hbA, hbX, hxA⟩ | ⟨hbA, hX1⟩ | ⟨hbA, hdA, hbX⟩ | ⟨hbA, hdA, hX1⟩
  · rcases h2 with ⟨-, hxY, hyA⟩ | ⟨hxA', -⟩ | ⟨hxA', -, -⟩ | ⟨hxA', -, -⟩
    · refine Or.inl ⟨hbA, ?_, hyA⟩
      have hxY' : sideCross Y X < 0 := by rwli [sideCross_swap]
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hbX hyA, mul_neg_of_pos_of_neg hbA hxY',
        mul_nonpos_of_nonpos_of_nonneg hc hxA.le]
    · linarith
    · linarith
    · linarith
  · refine Or.inr (Or.inl ⟨hbA, ?_⟩)
    rcases h2 with ⟨-, -, hyA⟩ | ⟨hxA, h2⟩ | ⟨hxA, hdXA, hxY⟩ | ⟨hxA, hdXA, -⟩
    · exact Or.inr hyA
    · have hbX : 0 < sideCross B X := by
        rcases hX1 with h | h
        · exact h
        · linarith
      rcases h2 with hxY | hyA
      · by_cases hyA : 0 < sideCross Y A
        · exact Or.inr hyA
        · push Not at hyA
          left
          have hyX : sideCross Y X < 0 := by rwli [sideCross_swap]
          by_contra hc
          push Not at hc
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hbX.le hyA, mul_pos (neg_pos.2 hbA)
            (neg_pos.2 hyX), mul_nonneg (neg_nonneg.2 hc) (neg_pos.2 hxA).le]
      · exact Or.inr hyA
    · right
      have D := side_dotCross X A Y
      rw [hxA, zero_mul, add_zero] at D
      have e : sideCross A Y = -sideCross Y A := sideCross_swap _ _
      rw [e] at D
      nlinarith [mul_neg_of_neg_of_pos hdXA hxY]
    · exfalso
      have hbX : 0 < sideCross B X := by
        rcases hX1 with h | h
        · exact h
        · rw [hxA] at h; exact absurd h (lt_irrefl _)
      have D := side_dotCross A X B
      have e1 : sideCross A X = -sideCross X A := sideCross_swap _ _
      have e2 : sideCross A B = -sideCross B A := sideCross_swap _ _
      have e3 : sideCross X B = -sideCross B X := sideCross_swap _ _
      have e4 : sideDot A X = sideDot X A := sideDot_comm _ _
      rw [e1, e2, e3, e4, hxA] at D
      nlinarith [mul_pos hdXA (neg_pos.2 hbA)]
  · have D := side_dotCross B A X
    rw [hbA, zero_mul, add_zero] at D
    have e : sideCross A X = -sideCross X A := sideCross_swap _ _
    rw [e] at D
    have hxA : 0 < sideCross X A := by nlinarith [mul_neg_of_neg_of_pos hdA hbX]
    rcases h2 with ⟨-, hxY, hyA⟩ | ⟨hxA', -⟩ | ⟨hxA', -, -⟩ | ⟨hxA', -, -⟩
    · refine Or.inr (Or.inr (Or.inl ⟨hbA, hdA, ?_⟩))
      have hxY' : sideCross Y X < 0 := by rwli [sideCross_swap]
      rw [hbA, zero_mul, add_zero] at P1
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hbX hyA, mul_nonpos_of_nonpos_of_nonneg hc hxA.le]
    · linarith
    · linarith
    · linarith
  · refine Or.inr (Or.inr (Or.inr ⟨hbA, hdA, ?_⟩))
    by_contra hc
    push Not at hc
    obtain ⟨hbY, hdY⟩ := hc
    have D := side_dotCross B Y A
    rw [hbA, mul_zero, hbY, zero_mul, add_zero] at D
    have hyA : sideCross Y A = 0 := by
      rcases mul_eq_zero.1 D.symm with h | h
      · linarith
      · exact h
    have DD := side_dotDot B Y A
    rw [hbY, zero_mul, add_zero] at DD
    have hdYA : 0 ≤ sideDot Y A := by nlinarith [mul_nonneg hdY hdA.le]
    exact sideCcw_not_ray_right hA hyA hdYA h2

omit C in
/-- **Complementary arcs are disjoint** (unless the arc is a full turn). -/
theorem sideCcw_asymm {B X A : Point} (hB : B ≠ 0) (hns : sideNonSpike B A)
    (h1 : sideCcw B X A) : ¬ sideCcw A X B := by
  have hBB := sideDot_self_pos hB
  have eBA : sideCross A B = -sideCross B A := sideCross_swap _ _
  have eBX : sideCross X B = -sideCross B X := sideCross_swap _ _
  have eXA : sideCross A X = -sideCross X A := sideCross_swap _ _
  intro h2
  rcases h1 with ⟨hbA, hbX, hxA⟩ | ⟨hbA, hX⟩ | ⟨hbA, hdA, hbX⟩ | ⟨hbA, hdA, hX⟩
  · rcases h2 with ⟨h, -, -⟩ | ⟨-, h | h⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
  · rcases h2 with ⟨-, h, h'⟩ | ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
    · rcases hX with hX | hX <;> linarith
    · linarith
    · linarith
    · linarith
  · have D := side_dotCross B A X
    rw [hbA, zero_mul, add_zero] at D
    rcases h2 with ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
    · linarith
    · linarith
    · nlinarith [mul_neg_of_neg_of_pos hdA hbX]
    · rwli [sideDot_comm] at h
  · exact hns ⟨hbA, hdA⟩

omit C in
/-- **Rotation**: if `X` is inside the arc from `B` to `A`, then `A` is inside the arc from `X`
to `B` (unless the arc is a full turn). -/
theorem sideCcw_rotate {B X A : Point} (hB : B ≠ 0) (hX : X ≠ 0) (hns : sideNonSpike B A)
    (h1 : sideCcw B X A) : sideCcw X A B := by
  have hBB := sideDot_self_pos hB
  have hXX := sideDot_self_pos hX
  have eBA : sideCross A B = -sideCross B A := sideCross_swap _ _
  have eBX : sideCross X B = -sideCross B X := sideCross_swap _ _
  rcases h1 with ⟨hbA, hbX, hxA⟩ | ⟨hbA, hX1⟩ | ⟨hbA, hdA, hbX⟩ | ⟨hbA, hdA, hX1⟩
  · exact Or.inr (Or.inl ⟨by linarith, Or.inl hxA⟩)
  · rcases lt_trichotomy (sideCross B X) 0 with hbX | hbX | hbX
    · have hxA : 0 < sideCross X A := by
        rcases hX1 with h | h
        · linarith
        · exact h
      exact Or.inl ⟨by linarith, hxA, by linarith⟩
    · have hxA : 0 < sideCross X A := by
        rcases hX1 with h | h
        · rw [hbX] at h; exact absurd h (lt_irrefl _)
        · exact h
      have D := side_dotCross B X A
      rw [hbX, zero_mul, add_zero] at D
      have hL := side_lagrange B X
      rw [hbX] at hL
      rcases lt_trichotomy (sideDot X B) 0 with hd | hd | hd
      · exact Or.inr (Or.inr (Or.inl ⟨by rw [eBX, hbX, neg_zero], hd, hxA⟩))
      · exfalso
        rw [sideDot_comm] at hd
        rw [hd] at hL
        nlinarith [mul_pos hBB hXX]
      · exfalso
        rw [sideDot_comm] at hd
        nlinarith [mul_pos hd (neg_pos.2 hbA), mul_pos hBB hxA]
    · exact Or.inr (Or.inl ⟨by linarith, Or.inr (by linarith)⟩)
  · have D := side_dotCross B A X
    rw [hbA, zero_mul, add_zero] at D
    have eXA : sideCross A X = -sideCross X A := sideCross_swap _ _
    rw [eXA] at D
    have hxA : 0 < sideCross X A := by nlinarith [mul_neg_of_neg_of_pos hdA hbX]
    exact Or.inr (Or.inl ⟨by linarith, Or.inl hxA⟩)
  · exact absurd ⟨hbA, hdA⟩ hns

/-! ### Left sectors at a corner -/

omit C in
/-- `x` lies in the open left sector of the corner `a → v → b`: the direction of `x - v` is
strictly inside the counterclockwise arc from the direction of `b - v` to that of `a - v`. -/
def sideLeftOf (a v b x : Point) : Prop := sideCcw (b - v) (x - v) (a - v)

omit C in
theorem sideCross_corner (a v b : Point) : sideCross (b - v) (a - v) = det a v b := by
  unfold sideCross det; sir only [Prod.fst_sub, Prod.snd_sub]

omit C in
theorem sideCross_out (v b x : Point) : sideCross (b - v) (x - v) = det v b x := by
  unfold sideCross det; sir only [Prod.fst_sub, Prod.snd_sub]

omit C in
theorem sideCross_in (a v x : Point) : sideCross (x - v) (a - v) = det a v x := by
  unfold sideCross det; sir only [Prod.fst_sub, Prod.snd_sub]

omit C in
theorem sub_ne_zero_of_ne' {a v : Point} (h : a ≠ v) : a - v ≠ 0 := sub_ne_zero.2 h

omit C in
/-- Left sector of a left turn: the intersection of the two left half-planes. -/
theorem sideLeftOf_iff_pos {a v b x : Point} (h : 0 < det a v b) :
    sideLeftOf a v b x ↔ 0 < 1 * det a v x ∧ 0 < 1 * det v b x := by
  unfold sideLeftOf sideCcw
  rw [sideCross_corner a v b, sideCross_out v b x, sideCross_in a v x, one_mul, one_mul]
  constructor
  · rintro (⟨-, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
    · exact ⟨h3, h2⟩
    · linarith
    · linarith
    · linarith
  · rintro ⟨h1, h2⟩; exact Or.inl ⟨h, h2, h1⟩

omit C in
/-- Left sector of a right turn: the union of the two left half-planes. -/
theorem sideLeftOf_iff_neg {a v b x : Point} (h : det a v b < 0) :
    sideLeftOf a v b x ↔ 0 < (-1) * det b v x ∨ 0 < (-1) * det v a x := by
  unfold sideLeftOf sideCcw
  rw [sideCross_corner a v b, sideCross_out v b x, sideCross_in a v x]
  have e1 : det b v x = -det v b x := Geometry.det_swap12 _ _ _
  have e2 : det v a x = -det a v x := Geometry.det_swap12 _ _ _
  rw [e1, e2]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2 | h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
    · linarith
    · left; linarith
    · right; linarith
    · linarith
    · linarith
  · rintro (h1 | h1)
    · exact Or.inr (Or.inl ⟨h, Or.inl (by linarith)⟩)
    · exact Or.inr (Or.inl ⟨h, Or.inr (by linarith)⟩)

omit C in
/-- Left sector of a straight corner: the left half-plane. -/
theorem sideLeftOf_iff_zero {a v b x : Point} (hbv : b ≠ v) (h : det a v b = 0)
    (hd : sideDot (b - v) (a - v) < 0) : sideLeftOf a v b x ↔ 0 < 1 * det a v x := by
  have hBB := sideDot_self_pos (sub_ne_zero_of_ne' hbv)
  have D := side_dotCross (b - v) (x - v) (a - v)
  rw [sideCross_corner a v b, h, mul_zero, sideCross_out v b x, sideCross_in a v x] at D
  unfold sideLeftOf sideCcw
  rw [sideCross_corner a v b, sideCross_out v b x, sideCross_in a v x, h, one_mul]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, h2, -⟩)
    · exact absurd h1 (lt_irrefl _)
    · exact absurd h1 (lt_irrefl _)
    · nlinarith [mul_pos h3 (neg_pos.2 hd)]
    · linarith
  · intro h1
    refine Or.inr (Or.inr (Or.inl ⟨rfl, hd, ?_⟩))
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hBB h1, mul_nonneg (neg_nonneg.2 hc) (neg_pos.2 hd).le]

omit C in
/-- **Sector lemma.**  At a corner `a → v → b` with `a ≠ v ≠ b`, if no point of `S` near `v`
lies in the open left sector, then the left sector near `v` is a preconnected set avoiding `S`
which contains the left offset points of both edges near `v` (including the full-turn case
`a = b`). -/
theorem sideSector {a v b : Point} (hav : a ≠ v) (hbv : b ≠ v) {S : Set Point} {r : ℝ}
    (hr : 0 < r) (hS : ∀ x ∈ ball v r, x ∈ S → ¬ sideLeftOf a v b x) :
    SectorSide S (ball v r ∩ {x | sideLeftOf a v b x}) a v b 1 := by
  have hsub : ball v r ∩ {x | sideLeftOf a v b x} ⊆ Sᶜ := fun x hx hxS => hS x hx.1 hxS hx.2
  have hS0 : ∀ x ∈ ball v r, x ∈ (∅ : Set Point) →
      x ∈ Chazelle.segment a v ∨ x ∈ Chazelle.segment v b := fun _ _ h => h.elim
  rcases lt_trichotomy (det a v b) 0 with hneg | hzero | hpos
  · have hpos' : 0 < det b v a := by rwli [Geometry.det_swap13]
    have hS0' : ∀ x ∈ ball v r, x ∈ (∅ : Set Point) →
        x ∈ Chazelle.segment b v ∨ x ∈ Chazelle.segment v a := fun _ _ h => h.elim
    have hss := (sectorSide_pos_right hpos' hbv hav.symm hr hS0').reverse
    rw [neg_neg] at hss
    have heq : (ball v r ∩ {x | 0 < (-1) * det b v x}) ∪ (ball v r ∩ {x | 0 < (-1) * det v a x}) =
        ball v r ∩ {x | sideLeftOf a v b x} := by
      ext x
      simp only [mem_union, mem_inter_iff, mem_ofPred_eq, sideLeftOf_iff_neg hneg]
      tauto
    rw [heq] at hss
    exact ⟨hsub, hss.2.1, hss.2.2⟩
  · by_cases hd : sideDot (b - v) (a - v) < 0
    · have hdir : 0 < (v.1 - a.1) * (b.1 - v.1) + (v.2 - a.2) * (b.2 - v.2) := by
        unfold sideDot at hd; sil only [Prod.fst_sub, Prod.snd_sub] at hd
      have hss := sectorSide_zero hzero hdir hav hr hS0 (σ := 1) one_ne_zero
      have heq : ball v r ∩ {x | 0 < 1 * det a v x} = ball v r ∩ {x | sideLeftOf a v b x} := by
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq, sideLeftOf_iff_zero hbv hzero hd]
      rw [heq] at hss
      exact ⟨hsub, hss.2.1, hss.2.2⟩
    · -- the full turn: `b` in the direction of `a`
      push Not at hd
      have hBB := sideDot_self_pos (sub_ne_zero_of_ne' hbv)
      set B : Point := b - v with hB
      have hL := side_lagrange B (a - v)
      rw [sideCross_corner, hzero] at hL
      have hAA := sideDot_self_pos (sub_ne_zero_of_ne' hav)
      have hdpos : 0 < sideDot B (a - v) := by
        rcases hd.lt_or_eq with h | h
        · exact h
        · exfalso; rw [← h] at hL; nlinarith [mul_pos hBB hAA]
      have hspike : ∀ x, sideLeftOf a v b x ↔ (sideCross B (x - v) ≠ 0 ∨ sideDot B (x - v) < 0) := by
        intro x
        unfold sideLeftOf sideCcw
        rw [sideCross_corner a v b, hzero]
        constructor
        · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, -, h3⟩)
          · exact absurd h1 (lt_irrefl _)
          · exact absurd h1 (lt_irrefl _)
          · linarith
          · exact h3
        · intro h; exact Or.inr (Or.inr (Or.inr ⟨rfl, hdpos, h⟩))
      -- the three convex pieces
      set J : Point := (-B.2, B.1) with hJ
      have hcrossJ : ∀ x : Point, sideCross B (x - v) = det v b x := fun x => sideCross_out v b x
      have hdotJ : ∀ x : Point, sideDot B (x - v) = -det v (v + J) x := by
        intro x; unfold sideDot det; simp only [hJ, hB, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_add, Prod.snd_add]; ring
      set H1 : Set Point := ball v r ∩ {x | 0 < 1 * det v b x}
      set H2 : Set Point := ball v r ∩ {x | 0 < (-1) * det v b x}
      set F : Set Point := ball v r ∩ {x | 0 < 1 * det v (v + J) x}
      have hU : ball v r ∩ {x | sideLeftOf a v b x} = (H1 ∪ F) ∪ (H2 ∪ F) := by
        ext x
        simp only [H1, H2, F, mem_union, mem_inter_iff, mem_ofPred_eq, hspike, hcrossJ, hdotJ,
          one_mul, neg_one_mul]
        constructor
        · rintro ⟨hx, h | h⟩
          · rcases lt_or_gt_of_ne h with h | h
            · right; left; exact ⟨hx, by linarith⟩
            · left; left; exact ⟨hx, h⟩
          · left; right; exact ⟨hx, by linarith⟩
        · rintro ((⟨hx, h⟩ | ⟨hx, h⟩) | (⟨hx, h⟩ | ⟨hx, h⟩))
          · exact ⟨hx, Or.inl h.ne'⟩
          · exact ⟨hx, Or.inr (by linarith)⟩
          · exact ⟨hx, Or.inl (by linarith)⟩
          · exact ⟨hx, Or.inr (by linarith)⟩
      have hcH1 : IsPreconnected H1 :=
        ((convex_ball v r).inter (convex_det_pos v b 1)).isPreconnected
      have hcH2 : IsPreconnected H2 :=
        ((convex_ball v r).inter (convex_det_pos v b (-1))).isPreconnected
      have hcF : IsPreconnected F :=
        ((convex_ball v r).inter (convex_det_pos v (v + J) 1)).isPreconnected
      -- common points
      have hBn : 0 < ‖(-B + J : Point)‖ + ‖(-B - J : Point)‖ + 1 := by positivity
      set ε := r / (‖(-B + J : Point)‖ + ‖(-B - J : Point)‖ + 1) with hε
      have hε0 : 0 < ε := div_pos hr hBn
      have hεb : ∀ w : Point, ‖w‖ ≤ ‖(-B + J : Point)‖ + ‖(-B - J : Point)‖ → v + ε • w ∈ ball v r := by
        intro w hw
        rw [mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
        calc ε * ‖w‖ ≤ ε * (‖(-B + J : Point)‖ + ‖(-B - J : Point)‖) :=
              mul_le_mul_of_nonneg_left hw hε0.le
          _ < ε * (‖(-B + J : Point)‖ + ‖(-B - J : Point)‖ + 1) := by nlinarith
          _ = r := div_mul_cancel₀ _ hBn.ne'
      have hdetvb : ∀ w : Point, det v b (v + ε • w) = ε * sideCross B w := by
        intro w; unfold det sideCross; simp only [hB, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]; ring
      have hdetJ : ∀ w : Point, det v (v + J) (v + ε • w) = -(ε * sideDot B w) := by
        intro w; unfold det sideDot; simp only [hJ, hB, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]; ring
      have hcr1 : sideCross B (-B + J) = sideDot B B := by
        unfold sideCross sideDot; simp only [hJ, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
          Prod.snd_neg]; ring
      have hdt1 : sideDot B (-B + J) = -sideDot B B := by
        unfold sideDot; sir only [hJ, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
      have hcr2 : sideCross B (-B - J) = -sideDot B B := by
        unfold sideCross sideDot; simp only [hJ, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg,
          Prod.snd_neg]; ring
      have hdt2 : sideDot B (-B - J) = -sideDot B B := by
        unfold sideDot; sir only [hJ, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]
      have hp1 : v + ε • (-B + J) ∈ H1 ∩ F := by
        refine ⟨⟨hεb _ (by linarith [norm_nonneg (-B - J : Point)]), ?_⟩,
          ⟨hεb _ (by linarith [norm_nonneg (-B - J : Point)]), ?_⟩⟩
        · show 0 < 1 * det v b _
          rw [one_mul, hdetvb, hcr1]; exact mul_pos hε0 hBB
        · show 0 < 1 * det v (v + J) _
          rw [one_mul, hdetJ, hdt1]; nlinarith [mul_pos hε0 hBB]
      have hp2 : v + ε • (-B - J) ∈ H2 ∩ F := by
        refine ⟨⟨hεb _ (by linarith [norm_nonneg (-B + J : Point)]), ?_⟩,
          ⟨hεb _ (by linarith [norm_nonneg (-B + J : Point)]), ?_⟩⟩
        · show 0 < (-1) * det v b _
          rw [hdetvb, hcr2]; nlinarith [mul_pos hε0 hBB]
        · show 0 < 1 * det v (v + J) _
          rw [one_mul, hdetJ, hdt2]; nlinarith [mul_pos hε0 hBB]
      have hc1 : IsPreconnected (H1 ∪ F) := hcH1.union _ hp1.1 hp1.2 hcF
      have hc2 : IsPreconnected (H2 ∪ F) := hcH2.union _ hp2.1 hp2.2 hcF
      have hc : IsPreconnected ((H1 ∪ F) ∪ (H2 ∪ F)) :=
        hc1.union _ (Or.inr hp1.2) (Or.inr hp1.2) hc2
      refine ⟨hsub, hU ▸ hc, ?_⟩
      -- the offset points
      have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp a v (1 - s) ∈ ball v r :=
        (tendsto_lerp_one_sub a v).eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp v b s ∈ ball v r :=
        (tendsto_lerp_zero v b).eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
      filter_upwards [h1, h2] with s hs1 hs2
      filter_upwards [eventually_offset_mem 1 isOpen_ball hs1,
        eventually_offset_mem 1 isOpen_ball hs2, self_mem_nhdsWithin] with δ hδ1 hδ2 hδ0
      have hδ0' : (0 : ℝ) < δ := hδ0
      refine ⟨⟨hδ1, ?_⟩, ⟨hδ2, ?_⟩⟩
      · show sideLeftOf a v b _
        rw [hspike]
        left
        rw [hcrossJ, det_offset_gen, det_lerp, Geometry.det_self_outer]
        have e1 : det v b a = det a v b := Geometry.det_cyclic a v b
        have e2 : det v b (v + nrm a v) = -sideDot B (a - v) := by
          unfold det nrm sideDot; simp only [hB, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
            Prod.snd_sub]; ring
        rw [e1, hzero, e2]
        have : (1 - (1 - s)) * 0 + (1 - s) * 0 + 1 * δ * -sideDot B (a - v) =
            -(δ * sideDot B (a - v)) := by ring
        rw [this]
        exact neg_ne_zero.2 (mul_pos hδ0' hdpos).ne'
      · show sideLeftOf a v b _
        rw [hspike]
        left
        rw [hcrossJ, det_offset]
        exact (mul_pos (by linarith) (sqLen_pos hbv.symm)).ne'
  · have hss := sectorSide_pos_left hpos hav hbv.symm hr hS0
    have heq : ball v r ∩ ({x | 0 < 1 * det a v x} ∩ {x | 0 < 1 * det v b x}) =
        ball v r ∩ {x | sideLeftOf a v b x} := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, sideLeftOf_iff_pos hpos]
    rw [heq] at hss
    exact ⟨hsub, hss.2.1, hss.2.2⟩

/-! ### Chaining left sides along edges and around corners -/

omit C in
/-- **Parallelogram lemma.**  If near every point of the segment `u v` with parameter in
`[t₁, t₂]` the set `S` lies in the closed right half-plane of `u → v`, then a thin
parallelogram of left offset points over `(t₁, t₂)` avoids `S`. -/
theorem sideEdge_par {u v : Point} (huv : u ≠ v) {S : Set Point} {t₁ t₂ : ℝ}
    (hS : ∀ t ∈ Icc t₁ t₂, ∃ r > 0, ∀ x ∈ ball (lerp u v t) r, x ∈ S → det u v x ≤ 0) :
    ∃ δ₀ > 0, par u v 1 t₁ t₂ δ₀ ⊆ Sᶜ := by
  set K : Set Point := lerp u v '' Icc t₁ t₂ with hK
  have hKc : IsCompact K := isCompact_Icc.image (Geometry.continuous_lerp u v)
  set O : Set Point := {y | ∃ t ∈ Icc t₁ t₂, ∃ r > 0, y ∈ ball (lerp u v t) r ∧
    ∀ x ∈ ball (lerp u v t) r, x ∈ S → det u v x ≤ 0} with hO
  have hOo : IsOpen O := by
    rw [Metric.isOpen_iff]
    rintro y ⟨t, ht, r, hr, hy, hball⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 isOpen_ball y hy
    exact ⟨ε, hε, fun z hz => ⟨t, ht, r, hr, hεsub hz, hball⟩⟩
  have hKO : K ⊆ O := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨r, hr, hball⟩ := hS t ht
    exact ⟨t, ht, r, hr, mem_ball_self hr, hball⟩
  obtain ⟨δ', hδ', hthick⟩ := hKc.exists_thickening_subset_open hOo hKO
  have hden : 0 < ‖nrm u v‖ + 1 := by positivity
  refine ⟨δ' / (‖nrm u v‖ + 1), by positivity, ?_⟩
  rintro x ⟨t, δ, ht1, ht2, hδ1, hδ2, rfl⟩ hxS
  have hmem : offset u v t (1 * δ) ∈ thickening δ' K := by
    rw [mem_thickening_iff]
    refine ⟨lerp u v t, ⟨t, ⟨ht1.le, ht2.le⟩, rfl⟩, ?_⟩
    unfold offset
    rw [dist_self_add_left, norm_smul, Real.norm_eq_abs, one_mul, abs_of_pos hδ1]
    calc δ * ‖nrm u v‖ ≤ δ * (‖nrm u v‖ + 1) := by nlinarith
      _ < δ' / (‖nrm u v‖ + 1) * (‖nrm u v‖ + 1) := mul_lt_mul_of_pos_right hδ2 hden
      _ = δ' := div_mul_cancel₀ _ hden.ne'
  obtain ⟨t', -, r, -, hy, hball⟩ := hthick hmem
  have := hball _ hy hxS
  rw [det_offset, one_mul] at this
  nlinarith [mul_pos hδ1 (sqLen_pos huv)]

omit C in
/-- The left offset points of the segment `u → v` at parameter `t` lie in `K` for all small
offsets. -/
def SideFaces (K : Set Point) (u v : Point) (t : ℝ) : Prop :=
  ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset u v t δ ∈ K

omit C in
/-- **Along an edge.**  If the complement of `D` stays in the closed right half-plane of
`u → v` near the points of parameter in `[t₁, t₂]`, then the left offset points at all
parameters in `(t₁, t₂)` lie in one component of `D`. -/
theorem sideFaces_edge {u v : Point} (huv : u ≠ v) {D : Set Point} {c₀ : Point} {t₁ t₂ t t' : ℝ}
    (hS : ∀ s ∈ Icc t₁ t₂, ∃ r > 0, ∀ x ∈ ball (lerp u v s) r, x ∉ D → det u v x ≤ 0)
    (ht : t ∈ Ioo t₁ t₂) (ht' : t' ∈ Ioo t₁ t₂)
    (h : SideFaces (connectedComponentIn D c₀) u v t) :
    SideFaces (connectedComponentIn D c₀) u v t' := by
  obtain ⟨δ₀, hδ₀, hpar⟩ := sideEdge_par huv (S := Dᶜ) hS
  have hparD : par u v 1 t₁ t₂ δ₀ ⊆ D := fun x hx => by simpa using hpar hx
  obtain ⟨δ, hδK, hδ⟩ := (h.and (Ioo_mem_nhdsGT hδ₀)).exists
  have hx : offset u v t (1 * δ) ∈ par u v 1 t₁ t₂ δ₀ := offset_mem_par ht.1 ht.2 hδ.1 hδ.2
  rw [one_mul] at hx
  have hsub : par u v 1 t₁ t₂ δ₀ ⊆ connectedComponentIn D c₀ := by
    rw [connectedComponentIn_eq hδK]
    exact (convex_par u v 1 t₁ t₂ δ₀).isPreconnected.subset_connectedComponentIn hx hparD
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ' hδ'
  have := offset_mem_par (u := u) (v := v) (σ := 1) ht'.1 ht'.2 hδ'.1 hδ'.2
  rw [one_mul] at this
  exact hsub this

omit C in
/-- **Around a corner.**  If the left sector at the corner `a → v → b` is joined by a
preconnected set avoiding `Dᶜ`, and the left offset points of `a → v` near `v` lie in a
component of `D`, then so do those of `v → b` near `v`, and the whole sector. -/
theorem sideFaces_corner {a v b : Point} {D U : Set Point} {c₀ : Point}
    (hU : SectorSide Dᶜ U a v b 1)
    (h : ∀ᶠ s in 𝓝[>] (0 : ℝ), SideFaces (connectedComponentIn D c₀) a v (1 - s)) :
    U ⊆ connectedComponentIn D c₀ ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), SideFaces (connectedComponentIn D c₀) v b s := by
  obtain ⟨hUS, hUc, hoff⟩ := hU
  have hUD : U ⊆ D := fun x hx => by simpa using hUS hx
  obtain ⟨s, hs1, hs2⟩ := (hoff.and h).exists
  obtain ⟨δ, hδ1, hδ2⟩ := (hs1.and hs2).exists
  rw [one_mul] at hδ1
  have hUK : U ⊆ connectedComponentIn D c₀ := by
    rw [connectedComponentIn_eq hδ2]
    exact hUc.subset_connectedComponentIn hδ1.1 hUD
  refine ⟨hUK, ?_⟩
  filter_upwards [hoff] with s hs
  filter_upwards [hs] with δ hδ
  rw [one_mul] at hδ
  exact hUK hδ.2

/-! ### Positions on a closed walk and their left sectors -/

omit C in
/-- The point of the closed walk `W` at position `(p, t)`: parameter `t` on edge `p`. -/
noncomputable def sidePt (W : Polygon) (p : ℕ) (t : ℝ) : Point :=
  lerp (W.vtx p) (W.vtx ((p + 1) % W.n)) t

omit C in
/-- The point before position `(p, t)`: the previous vertex if `t = 0` (a vertex of the walk),
the start of edge `p` otherwise. -/
noncomputable def sidePrev (W : Polygon) (p : ℕ) (t : ℝ) : Point :=
  if t = 0 then W.vtx ((p + W.n - 1) % W.n) else W.vtx p

omit C in
/-- The point after position `(p, t)`: the end of edge `p`. -/
noncomputable def sideNext (W : Polygon) (p : ℕ) : Point := W.vtx ((p + 1) % W.n)

omit C in
/-- `x` lies in the open left sector of the walk `W` at position `(p, t)`: the left sector of the
corner `sidePrev → sidePt → sideNext` (for `0 < t < 1` the open left half-plane of edge `p`). -/
def sideLeft (W : Polygon) (p : ℕ) (t : ℝ) (x : Point) : Prop :=
  sideLeftOf (sidePrev W p t) (sidePt W p t) (sideNext W p) x

omit C in
/-- Position `(p, t)` is clean for `D`: near its point, no point outside `D` lies in its left
sector. -/
def SideClean (W : Polygon) (D : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  ∃ r > 0, ∀ x ∈ ball (sidePt W p t) r, x ∉ D → ¬ sideLeft W p t x

omit C in
/-- The small left sector of `W` at position `(p, t)` lies in `K`. -/
def SideSectorIn (W : Polygon) (K : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  ∃ r > 0, ∀ x ∈ ball (sidePt W p t) r, sideLeft W p t x → x ∈ K

omit C in
/-- The set `d` **attaches** to the walk `W` at position `(p, t)`: the point of the position lies
on `d`, and the points of `d` near it lie in the open left sector of the walk there. -/
def SideAttach (W : Polygon) (d : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  p < W.n ∧ 0 ≤ t ∧ t < 1 ∧ sidePt W p t ∈ d ∧
    ∃ r > 0, ∀ x ∈ d, x ≠ sidePt W p t → dist x (sidePt W p t) < r → sideLeft W p t x

omit C in
/-- Cyclic betweenness of keys: `x` is strictly between `a` and `b` going up from `a` (and
wrapping around). -/
def sideInArc (a b x : ℝ) : Prop := if a < b then a < x ∧ x < b else (a < x ∨ x < b)

omit C in
theorem sidePt_zero (W : Polygon) (p : ℕ) : sidePt W p 0 = W.vtx p := by
  unfold sidePt; rw [lerp_zero]

omit C in
/-- At a vertex position the left sector is that of the corner of the walk. -/
theorem sideLeft_zero (W : Polygon) (p : ℕ) (x : Point) :
    sideLeft W p 0 x ↔
      sideLeftOf (W.vtx ((p + W.n - 1) % W.n)) (W.vtx p) (W.vtx ((p + 1) % W.n)) x := by
  unfold sideLeft sidePrev sideNext
  rw [sidePt_zero, ite_eq_left rfl]

omit C in
/-- At a position inside an edge the left sector is the open left half-plane of the edge. -/
theorem sideLeft_edge {W : Polygon} {p : ℕ} {t : ℝ} (hne : W.vtx p ≠ W.vtx ((p + 1) % W.n))
    (ht : t ∈ Ioo (0 : ℝ) 1) (x : Point) :
    sideLeft W p t x ↔ 0 < det (W.vtx p) (W.vtx ((p + 1) % W.n)) x := by
  set u := W.vtx p
  set v := W.vtx ((p + 1) % W.n)
  unfold sideLeft sidePrev sideNext
  rw [ite_eq_right ht.1.ne']
  unfold sidePt
  have hvq  := (lerp_ne_right hne ht.2).symm
  have h0 : det u (lerp u v t) v = 0 := by
    rwring [Geometry.det_lerp_mid, Geometry.det_self_left, Geometry.det_self_right]
  have hd : sideDot (v - lerp u v t) (u - lerp u v t) < 0 := by
    have := sqLen_pos hne
    unfold sideDot sqLen at *
    simp only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd]
    nlinarith [mul_pos (mul_pos ht.1 (sub_pos.2 ht.2)) this]
  rw [sideLeftOf_iff_zero hvq h0 hd, one_mul, Geometry.det_lerp_mid, Geometry.det_self_left]
  constructor
  · intro h; nlinarith [ht.1]
  · intro h; nlinarith [mul_pos ht.1 h]

omit C in
/-- From the left offsets at a clean position inside an edge to the whole small sector. -/
theorem sideSectorIn_of_faces {W : Polygon} {D : Set Point} {c₀ : Point} {p : ℕ} {t : ℝ}
    (hne : W.vtx p ≠ W.vtx ((p + 1) % W.n)) (ht : t ∈ Ioo (0 : ℝ) 1) (hcl : SideClean W D p t)
    (hf : SideFaces (connectedComponentIn D c₀) (W.vtx p) (W.vtx ((p + 1) % W.n)) t) :
    SideSectorIn W (connectedComponentIn D c₀) p t := by
  obtain ⟨r, hr, hcl⟩ := hcl
  set H : Set Point := ball (sidePt W p t) r ∩ {x | 0 < 1 * det (W.vtx p) (W.vtx ((p + 1) % W.n)) x}
  have hHc : IsPreconnected H :=
    ((convex_ball _ r).inter (convex_det_pos _ _ 1)).isPreconnected
  have hHD : H ⊆ D := by
    intro x hx
    by_contra hxD
    apply hcl x hx.1 hxD
    rw [sideLeft_edge hne ht]
    have := hx.2
    simp only [mem_ofPred_eq, one_mul] at this
    exact this
  have hoff : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset (W.vtx p) (W.vtx ((p + 1) % W.n)) t (1 * δ) ∈ H := by
    filter_upwards [eventually_offset_mem 1 isOpen_ball (mem_ball_self hr), self_mem_nhdsWithin]
      with δ hδ hδ0
    refine ⟨hδ, ?_⟩
    show 0 < 1 * det _ _ _
    rw [det_offset]
    have hδ0' : (0 : ℝ) < δ := hδ0
    nlinarith [mul_pos hδ0' (sqLen_pos hne)]
  obtain ⟨δ, h1, h2⟩ := (hoff.and hf).exists
  rw [one_mul] at h1
  have hHK : H ⊆ connectedComponentIn D c₀ := by
    rw [connectedComponentIn_eq h2]
    exact hHc.subset_connectedComponentIn h1 hHD
  refine ⟨r, hr, fun x hx hxl => hHK ⟨hx, ?_⟩⟩
  show 0 < 1 * det _ _ _
  rw [one_mul, ← sideLeft_edge hne ht]
  exact hxl

omit C in
/-- Decomposition of an arc of positions: a position strictly between `A = (pa, ta)` and
`B = (pb, tb)` lies on edge `(pa + j) % N` for some `j ≤ L = (pb + N - pa) % N`, after `A` if
`j = 0`, before `B` if `j = L`. -/
theorem sideInArc_cases {N pa pb p : ℕ} {ta tb t : ℝ} (hpa : pa < N) (hpb : pb < N)
    (hp : p < N) (hab : pa ≠ pb) (hta : 0 ≤ ta) (hta1 : ta < 1) (htb : 0 ≤ tb) (htb1 : tb < 1)
    (ht : 0 ≤ t) (ht1 : t < 1) (h : sideInArc (pa + ta) (pb + tb) (p + t)) :
    ∃ j, j ≤ (pb + N - pa) % N ∧ p = (pa + j) % N ∧ (j = 0 → ta < t) ∧
      (j = (pb + N - pa) % N → t < tb) := by
  -- natural-number consequences of real key inequalities
  have key1 : ∀ {q r : ℕ} {u w : ℝ}, 0 ≤ u → w < 1 → (q : ℝ) + u < r + w → q ≤ r := by
    intro q r u w hu hw h
    by_contra hc
    push Not at hc
    have : (r : ℝ) + 1 ≤ q := by exact_mod_cast hc
    linarith
  have key2 : ∀ {q : ℕ} {u w : ℝ}, (q : ℝ) + u < q + w → u < w := by
    intro q u w h; linarith
  unfold sideInArc at h
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hk : (pa : ℝ) + ta < pb + tb := by
      have : (pa : ℝ) + 1 ≤ pb := by exact_mod_cast hlt
      linarith
    rw [ite_eq_left hk] at h
    obtain ⟨h1, h2⟩ := h
    have hp1  := key1 hta ht1 h1
    have hp2  := key1 ht htb1 h2
    have hL : (pb + N - pa) % N = pb - pa := by
      rw [show pb + N - pa = (pb - pa) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    refine ⟨p - pa, by rwo [hL], ?_, ?_, ?_⟩
    · rw [show pa + (p - pa) = p by omega, Nat.mod_eq_of_lt hp]
    · intro hj
      have : p = pa := by omega
      subst this
      exact key2 h1
    · intro hj
      rw [hL] at hj
      have : p = pb := by omega
      subst this
      exact key2 h2
  · have hk : ¬ ((pa : ℝ) + ta < pb + tb) := by
      have : (pb : ℝ) + 1 ≤ pa := by exact_mod_cast hgt
      linarith
    rw [ite_eq_right hk] at h
    have hL : (pb + N - pa) % N = pb + N - pa := Nat.mod_eq_of_lt (by omega)
    rcases h with h1 | h2
    · have hp1 : pa ≤ p := key1 hta ht1 h1
      refine ⟨p - pa, by rwo [hL], ?_, ?_, ?_⟩
      · rw [show pa + (p - pa) = p by omega, Nat.mod_eq_of_lt hp]
      · intro hj
        have : p = pa := by omega
        subst this
        exact key2 h1
      · intro hj; rwo [hL] at hj
    · have hp2 : p ≤ pb := key1 ht htb1 h2
      refine ⟨p + N - pa, by rwo [hL], ?_, ?_, ?_⟩
      · rw [show pa + (p + N - pa) = p + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hp]
      · intro hj; omega
      · intro hj
        rw [hL] at hj
        have : p = pb := by omega
        subst this
        exact key2 h2

omit C in
/-- Along an edge of a walk: if all positions `(q, s)` with `s ∈ (lo, hi)` are clean for `D`,
the left offsets at all parameters in `(lo, hi)` lie in one component of `D`. -/
theorem sideFaces_walk_edge {W : Polygon} {D : Set Point} {c₀ : Point} {q : ℕ} {lo hi : ℝ}
    (hne : W.vtx q ≠ W.vtx ((q + 1) % W.n)) (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hcl : ∀ s ∈ Ioo lo hi, SideClean W D q s) {t : ℝ} (ht : t ∈ Ioo lo hi)
    (hf : SideFaces (connectedComponentIn D c₀) (W.vtx q) (W.vtx ((q + 1) % W.n)) t)
    {t' : ℝ} (ht' : t' ∈ Ioo lo hi) :
    SideFaces (connectedComponentIn D c₀) (W.vtx q) (W.vtx ((q + 1) % W.n)) t' := by
  set t₁ := (lo + min t t') / 2
  set t₂ := (hi + max t t') / 2
  have h1 : lo < t₁ := by have := lt_min ht.1 ht'.1; sil only [t₁]
  have h2 : t₂ < hi := by have := max_lt ht.2 ht'.2; sil only [t₂]
  have h3 : t₁ < t := by have := min_le_left t t'; have := ht.1; sil only [t₁]
  have h4 : t₁ < t' := by have := min_le_right t t'; have := ht'.1; sil only [t₁]
  have h5 : t < t₂ := by have := le_max_left t t'; have := ht.2; sil only [t₂]
  have h6 : t' < t₂ := by have := le_max_right t t'; have := ht'.2; sil only [t₂]
  refine sideFaces_edge hne ?_ ⟨h3, h5⟩ ⟨h4, h6⟩ hf
  intro s hs
  have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨r, hr, hcl'⟩ := hcl s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨r, hr, fun x hx hxD => ?_⟩
  have := hcl' x hx hxD
  rw [sideLeft_edge hne hs'] at this
  exact not_lt.1 this

omit C in
theorem side_mod_cases {x N : ℕ} (hx : x < 2 * N) :
    (x < N ∧ x % N = x) ∨ (N ≤ x ∧ x % N = x - N) := by
  rcases lt_or_ge x N with h | h
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · refine Or.inr ⟨h, ?_⟩
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

omit C in
theorem side_idx_succ {N : ℕ} (_hN : 0 < N) (a j : ℕ) :
    ((a + j) % N + 1) % N = (a + (j + 1)) % N := by
  rw [Nat.add_mod ((a + j) % N) 1 N, Nat.mod_mod, ← Nat.add_mod, add_assoc]

omit C in
theorem side_idx_prev {N : ℕ} (hN : 0 < N) (a j : ℕ) :
    ((a + (j + 1)) % N + N - 1) % N = (a + j) % N := by
  rw [← side_idx_succ hN]
  have hy := Nat.mod_lt (a + j) hN
  rcases lt_or_eq_of_le (show (a + j) % N + 1 ≤ N by omega) with h | h
  · rw [Nat.mod_eq_of_lt h, show (a + j) % N + 1 + N - 1 = (a + j) % N + N by omega,
      Nat.add_mod_right, Nat.mod_mod]
  · rw [h, Nat.mod_self, show 0 + N - 1 = (a + j) % N by omega, Nat.mod_mod]

omit C in
theorem side_arcLen_pos {N pa pb : ℕ} (hpa : pa < N) (hpb : pb < N) (hab : pa ≠ pb) :
    1 ≤ (pb + N - pa) % N := by
  rcases side_mod_cases (show pb + N - pa < 2 * N by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

omit C in
theorem side_arcLen_end {N pa pb : ℕ} (hpa : pa < N) (hpb : pb < N) :
    (pa + (pb + N - pa) % N) % N = pb := by
  rcases side_mod_cases (show pb + N - pa < 2 * N by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2]
    rcases side_mod_cases (show pa + (pb + N - pa) < 2 * N by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      omega
  · rw [h2]
    rcases side_mod_cases (show pa + (pb + N - pa - N) < 2 * N by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      omega

omit C in
theorem side_arc_ne_start {N pa j : ℕ} (hpa : pa < N) (hj1 : 1 ≤ j) (hjN : j < N) :
    (pa + j) % N ≠ pa := by
  rcases side_mod_cases (show pa + j < 2 * N by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

omit C in
theorem side_arc_eq_end {N pa pb j : ℕ} (hpa : pa < N) (hpb : pb < N) (hjN : j < N)
    (hLN : (pb + N - pa) % N < N) (h : (pa + j) % N = pb) : j = (pb + N - pa) % N := by
  have e := side_arcLen_end hpa hpb
  rcases side_mod_cases (show pb + N - pa < 2 * N by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h2] at e hLN ⊢ <;>
    rcases side_mod_cases (show pa + j < 2 * N by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    omega

omit C in
/-- **Chaining the left sides of a closed walk along an arc.**  Let `A = (pa, ta)` and
`B = (pb, tb)` be positions of a closed walk `W` on distinct edges, let every other position be
clean for an open set `D`, and suppose the left offsets just after `A` lie in the component `K` of
`D`.  Then the small left sector of every position strictly between `A` and `B` lies in `K`. -/
theorem sideArc_chain (W : Polygon) {D : Set Point} {pa pb : ℕ} {ta tb : ℝ}
    (hnd : ∀ p < W.n, W.vtx p ≠ W.vtx ((p + 1) % W.n))
    (hpa : pa < W.n) (hpb : pb < W.n) (hab : pa ≠ pb) (hta : 0 ≤ ta) (hta1 : ta < 1)
    (htb : 0 ≤ tb) (htb1 : tb < 1)
    (hclean : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → (p = pa → t ≠ ta) → (p = pb → t ≠ tb) →
      SideClean W D p t)
    {c₀ : Point}
    (hstart : ∃ s₀ > 0, ∀ s ∈ Ioo 0 s₀,
      SideFaces (connectedComponentIn D c₀) (W.vtx pa) (W.vtx ((pa + 1) % W.n)) (ta + s)) :
    ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc (pa + ta) (pb + tb) (p + t) →
      SideSectorIn W (connectedComponentIn D c₀) p t := by
  have hN0 : 0 < W.n := by omega
  obtain ⟨L, hL⟩ : ∃ L, L = (pb + W.n - pa) % W.n := ⟨_, rfl⟩
  have hLlt : L < W.n := hL ▸ Nat.mod_lt _ hN0
  have hL1  := hL ▸ side_arcLen_pos hpa hpb hab
  have hDL  := hL ▸ side_arcLen_end hpa hpb
  have hD0 : (pa + 0) % W.n = pa := by rw [add_zero]; exact Nat.mod_eq_of_lt hpa
  have hDlt : ∀ j, (pa + j) % W.n < W.n := fun j => Nat.mod_lt _ hN0
  have hDne : ∀ j, 1 ≤ j → j ≤ L → (pa + j) % W.n ≠ pa := fun j h1 h2 =>
    side_arc_ne_start hpa h1 (by omega)
  have hDpb : ∀ j, j ≤ L → (pa + j) % W.n = pb → j = L := fun j hj h => by
    rw [hL]; exact side_arc_eq_end hpa hpb (by omega) (hL ▸ hLlt) h
  -- the base edge `pa` after `ta`
  have hbase : ∀ t ∈ Ioo ta 1, SideFaces (connectedComponentIn D c₀) (W.vtx pa)
      (W.vtx ((pa + 1) % W.n)) t := by
    obtain ⟨s₀, hs₀, hstart⟩ := hstart
    obtain ⟨s, hs⟩ : ∃ s, s = min s₀ (1 - ta) / 2 := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; have := lt_min hs₀ (sub_pos.2 hta1); positivity
    have hss : s < s₀ := by rw [hs]; have := min_le_left s₀ (1 - ta); linarith
    have hs1 : s < 1 - ta := by rw [hs]; have := min_le_right s₀ (1 - ta); linarith
    intro t ht
    have hcl : ∀ s' ∈ Ioo ta 1, SideClean W D pa s' := fun s' hs' =>
      hclean pa hpa s' (by linarith [hs'.1]) hs'.2 (fun _ => ne_of_gt hs'.1)
        (fun h => absurd h hab)
    exact sideFaces_walk_edge (hnd pa hpa) hta le_rfl hcl (t := ta + s) ⟨by linarith, by linarith⟩
      (hstart s ⟨hs0, hss⟩) ht
  -- the induction along the arc
  have hstep : ∀ j, 1 ≤ j → j ≤ L → (j < L ∨ 0 < tb) →
      SideSectorIn W (connectedComponentIn D c₀) ((pa + j) % W.n) 0 ∧
        ∀ t ∈ Ioo 0 (if j < L then (1 : ℝ) else tb),
          SideFaces (connectedComponentIn D c₀) (W.vtx ((pa + j) % W.n))
            (W.vtx (((pa + j) % W.n + 1) % W.n)) t := by
    intro j hj1
    induction j with
    | zero => omega
    | succ i ih =>
      intro hjL hcase
      -- the edge before the vertex
      have hprev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
          SideFaces (connectedComponentIn D c₀) (W.vtx ((pa + i) % W.n))
            (W.vtx (((pa + i) % W.n + 1) % W.n)) (1 - s) := by
        rcases Nat.eq_zero_or_pos i with hi0 | hi0
        · subst hi0
          rw [hD0]
          filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hta1)] with s hs
          exact hbase _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
        · have hi := (ih hi0 (by omega) (Or.inl (by omega))).2
          rw [ite_eq_left (show i < L by omega)] at hi
          filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
          exact hi _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
      rw [side_idx_succ hN0] at hprev
      -- the corner
      have hcl0 : SideClean W D ((pa + (i + 1)) % W.n) 0 :=
        hclean _ (hDlt _) 0 le_rfl one_pos (fun h => absurd h (hDne _ (by omega) hjL))
          (fun h => by
            have := hDpb _ hjL h
            rcases hcase with hc | hc
            · omega
            · exact hc.ne)
      obtain ⟨r, hr, hcl0⟩ := hcl0
      have hne1 : W.vtx ((pa + i) % W.n) ≠ W.vtx ((pa + (i + 1)) % W.n) := by
        have := hnd _ (hDlt i); rwa [side_idx_succ hN0] at this
      have hne2 : W.vtx ((pa + (i + 1)) % W.n) ≠ W.vtx (((pa + (i + 1)) % W.n + 1) % W.n) :=
        hnd _ (hDlt _)
      have hsec := sideSector hne1 hne2.symm (S := Dᶜ) hr (fun x hx hxS => by
        have := hcl0 x (by rwx [sidePt_zero]) hxS
        rwa [sideLeft_zero, side_idx_prev hN0] at this)
      obtain ⟨hUK, hnext⟩ := sideFaces_corner hsec hprev
      refine ⟨⟨r, hr, fun x hx hxl => hUK ⟨by rw [sidePt_zero] at hx; exact hx, ?_⟩⟩, ?_⟩
      · rw [sideLeft_zero, side_idx_prev hN0] at hxl; exact hxl
      · have hhi : (0 : ℝ) < (if i + 1 < L then (1 : ℝ) else tb) := by
          split_ifs with h
          · exact one_pos
          · rcases hcase with hc | hc
            · exact absurd hc h
            · exact hc
        have hhi1 : (if i + 1 < L then (1 : ℝ) else tb) ≤ 1 := by
          split_ifs
          · exact le_rfl
          · exact htb1.le
        obtain ⟨s, hs1, hs2⟩ := (hnext.and (Ioo_mem_nhdsGT hhi)).exists
        intro t ht
        refine sideFaces_walk_edge hne2 le_rfl hhi1 ?_ hs2 hs1 ht
        intro s' hs'
        refine hclean _ (hDlt _) s' hs'.1.le (lt_of_lt_of_le hs'.2 hhi1)
          (fun h => absurd h (hDne _ (by omega) hjL)) (fun h => ?_)
        have := hDpb _ hjL h
        rw [ite_eq_right (show ¬ (i + 1 < L) by omega)] at hs'
        exact hs'.2.ne
  -- conclusion
  intro p hp t ht ht1 harc
  obtain ⟨j, hjL, hpj, hj0, hjL'⟩ := sideInArc_cases hpa hpb hp hab hta hta1 htb htb1 ht ht1 harc
  rw [← hL] at hjL hjL'
  subst hpj
  rcases ht.lt_or_eq with htpos | htz
  · -- inside an edge
    have hclp : SideClean W D ((pa + j) % W.n) t := by
      refine hclean _ (hDlt _) t ht ht1 (fun h => ?_) (fun h => ?_)
      · rcases Nat.eq_zero_or_pos j with h0 | h0
        · exact (hj0 h0).ne'
        · exact absurd h (hDne j h0 hjL)
      · exact (hjL' (hDpb j hjL h)).ne
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      have hf := hbase t ⟨hj0 rfl, ht1⟩
      rw [← hD0] at hf
      exact sideSectorIn_of_faces (hnd _ (hDlt _)) ⟨htpos, ht1⟩ hclp hf
    · have hcase : j < L ∨ 0 < tb := by
        rcases lt_or_eq_of_le hjL with h | h
        · exact Or.inl h
        · exact Or.inr (by linarith [hjL' h])
      have hf := (hstep j h0 hjL hcase).2 t ⟨htpos, by
        split_ifs with h
        · exact ht1
        · exact hjL' (by omega)⟩
      exact sideSectorIn_of_faces (hnd _ (hDlt _)) ⟨htpos, ht1⟩ hclp hf
  · -- a vertex
    subst htz
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact absurd (hj0 h0) (not_lt.2 hta)
    · have hcase : j < L ∨ 0 < tb := by
        rcases lt_or_eq_of_le hjL with h | h
        · exact Or.inl h
        · exact Or.inr (hjL' h)
      exact (hstep j h0 hjL hcase).1

omit C in
/-- The circular order depends only on the direction of the middle vector. -/
theorem sideCcw_smul {B X A : Point} {ε : ℝ} (hε : 0 < ε) :
    sideCcw B (ε • X) A ↔ sideCcw B X A := by
  have e1 : sideCross B (ε • X) = ε * sideCross B X := by
    unfold sideCross; sir only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have e2 : sideCross (ε • X) A = ε * sideCross X A := by
    unfold sideCross; sir only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have e3 : sideDot B (ε • X) = ε * sideDot B X := by
    unfold sideDot; sir only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hpos : ∀ x : ℝ, 0 < ε * x ↔ 0 < x := fun x => mul_pos_iff_of_pos_left hε
  have hneg : ∀ x : ℝ, ε * x < 0 ↔ x < 0 := fun x => by
    constructor
    · intro h; by_contra h'; push Not at h'; nlinarith
    · intro h; nlinarith
  have hne : ∀ x : ℝ, ε * x ≠ 0 ↔ x ≠ 0 := fun x => by
    rw [ne_eq, ne_eq, mul_eq_zero, not_or]; exact ⟨fun h => h.2, fun h => ⟨hε.ne', h⟩⟩
  unfold sideCcw
  rw [e1, e2, e3]
  simp only [hpos, hneg, hne]

omit C in
/-- Reparametrising offsets on a final piece of a segment. -/
theorem offset_lerp_left (u v : Point) (t s δ : ℝ) :
    offset (lerp u v t) v s δ = offset u v (t + s * (1 - t)) (δ * (1 - t)) := by
  apply point_ext <;> simp only [offset_fst, offset_snd, lerp_fst, lerp_snd] <;> ring

omit C in
/-- **Cutting the walk at an attachment.**  Let the segment `c = [q, q']` (`q ≠ q'`) attach to
the walk `W` at the position `A = (p, t)` of point `q`, and let `A` be clean for `D₀`.  Then
there is a component `K` of `D₀ \ c` containing the left offsets of the walk just after `A` and
the left offsets of `q' → q` near `q`. -/
theorem sideCut {W : Polygon} {D₀ : Set Point} {p : ℕ} {t : ℝ} {q' : Point}
    (hA : SideAttach W (Chazelle.segment (sidePt W p t) q') p t) (hq : sidePt W p t ≠ q')
    (hne : W.vtx p ≠ W.vtx ((p + 1) % W.n)) (hcl : SideClean W D₀ p t) :
    ∃ c₀ : Point,
      (∃ s₀ > 0, ∀ s ∈ Ioo 0 s₀,
        SideFaces (connectedComponentIn (D₀ \ Chazelle.segment (sidePt W p t) q') c₀)
          (W.vtx p) (W.vtx ((p + 1) % W.n)) (t + s)) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        SideFaces (connectedComponentIn (D₀ \ Chazelle.segment (sidePt W p t) q') c₀)
          q' (sidePt W p t) (1 - s) := by
  set q := sidePt W p t with hqdef
  set c := Chazelle.segment q q' with hc
  set D := D₀ \ c with hD
  obtain ⟨hp, ht0, ht1, -, ra, hra, hatt⟩ := hA
  obtain ⟨rc, hrc, hcl⟩ := hcl
  have hnext : sideNext W p ≠ q := by
    unfold sideNext; rw [hqdef]; unfold sidePt
    exact (lerp_ne_right hne ht1).symm
  -- the direction of `c` is in the left sector at `A`
  have hdir : sideCcw (sideNext W p - q) (q' - q) (sidePrev W p t - q) := by
    set ε := min ra 1 / (2 * (‖q' - q‖ + 1)) with hε
    have hε0 : 0 < ε := by
      rw [hε]; have := lt_min hra one_pos; positivity
    have hεx : q + ε • (q' - q) ∈ c := by
      rw [hc, Geometry.mem_segment_iff_lerp]
      refine ⟨ε, hε0.le, ?_, ?_⟩
      · rw [hε, div_le_one (by positivity)]
        have := min_le_right ra 1
        nlinarith [norm_nonneg (q' - q)]
      · apply point_ext <;> simp [lerp]
    have hεne : q + ε • (q' - q) ≠ q := by
      intro h
      have : ε • (q' - q) = 0 := by
        have := congrArg (fun x => x - q) h; simpa using this
      rcases smul_eq_zero.1 this with h1 | h1
      · exact hε0.ne' h1
      · exact hq (sub_eq_zero.1 h1).symm
    have hεd : dist (q + ε • (q' - q)) q < ra := by
      rw [dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
      have hden : 0 < 2 * (‖q' - q‖ + 1) := by positivity
      calc ε * ‖q' - q‖ < ε * (2 * (‖q' - q‖ + 1)) := by
            nlinarith [norm_nonneg (q' - q)]
        _ = min ra 1 := by rw [hε]; field_simp
        _ ≤ ra := min_le_left ra 1
    have := hatt _ hεx hεne hεd
    unfold sideLeft sideLeftOf at this
    rw [show q + ε • (q' - q) - q = ε • (q' - q) by abel, sideCcw_smul hε0] at this
    exact this
  -- the sector of the sub-corner `q' → q → next`
  have hsec : SectorSide Dᶜ (ball q rc ∩ {x | sideLeftOf q' q (sideNext W p) x}) q' q
      (sideNext W p) 1 := by
    refine sideSector hq.symm hnext hrc ?_
    intro x hx hxS hxl
    by_cases hx0 : x ∈ D₀
    · have hxc : x ∈ c := by
        by_contra h; exact hxS ⟨hx0, h⟩
      -- `x` on the chord: its direction is that of `q'`
      obtain ⟨μ, hμ0, hμ1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hxc
      apply sideCcw_not_ray_right (sub_ne_zero_of_ne' (Ne.symm hq)) (Y := lerp q q' μ - q) ?_ ?_ hxl
      · have e : lerp q q' μ - q = μ • (q' - q) := by
          apply point_ext <;> simp [lerp]
        rw [e]; unfold sideCross; sir only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      · have e : lerp q q' μ - q = μ • (q' - q) := by
          apply point_ext <;> simp [lerp]
        rw [e]; unfold sideDot; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        nlinarith [sq_nonneg (q' - q).1, sq_nonneg (q' - q).2]
    · apply hcl x hx hx0
      exact sideCcw_sub_left (sub_ne_zero_of_ne' hnext) hdir hxl
  obtain ⟨hUS, hUc, hoff⟩ := hsec
  have hUD : ball q rc ∩ {x | sideLeftOf q' q (sideNext W p) x} ⊆ D :=
    fun x hx => by simpa using hUS hx
  obtain ⟨s, hs⟩ := hoff.exists
  obtain ⟨δ, hδ⟩ := hs.exists
  set c₀ := offset q' q (1 - s) (1 * δ) with hc₀
  have hUK : ball q rc ∩ {x | sideLeftOf q' q (sideNext W p) x} ⊆ connectedComponentIn D c₀ :=
    hUc.subset_connectedComponentIn hδ.1 hUD
  refine ⟨c₀, ?_, ?_⟩
  · -- the walk just after `A`, reparametrised
    obtain ⟨s₁, hs₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hoff
    have h1t  := sub_pos.2 ht1
    refine ⟨s₁ * (1 - t), mul_pos (mem_Ioi.1 hs₁) h1t, fun s' hs' => ?_⟩
    have hs'' : s' / (1 - t) ∈ Ioo 0 s₁ :=
      ⟨div_pos hs'.1 h1t, (div_lt_iff₀ h1t).2 hs'.2⟩
    have hev := hsub hs''
    obtain ⟨δ₁, hδ₁, hsubδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨δ₁ * (1 - t), mul_pos (mem_Ioi.1 hδ₁) h1t,
      fun δ' hδ' => ?_⟩
    have hδ'' : δ' / (1 - t) ∈ Ioo 0 δ₁ :=
      ⟨div_pos hδ'.1 h1t, (div_lt_iff₀ h1t).2 hδ'.2⟩
    have := (hsubδ hδ'').2
    rw [one_mul] at this
    have e : offset q (sideNext W p) (s' / (1 - t)) (δ' / (1 - t)) =
        offset (W.vtx p) (W.vtx ((p + 1) % W.n)) (t + s') δ' := by
      rw [hqdef]; unfold sidePt sideNext
      rw [offset_lerp_left]
      congr 1
      · field_simp
      · field_simp
    rw [e] at this
    exact hUK this
  · filter_upwards [hoff] with s hs
    filter_upwards [hs] with δ hδ
    rw [one_mul] at hδ
    exact hUK hδ.1

omit C in
theorem sideNext_ne_pt {W : Polygon} {p : ℕ} {t : ℝ} (hne : W.vtx p ≠ W.vtx ((p + 1) % W.n))
    (ht1 : t < 1) : sideNext W p ≠ sidePt W p t := by
  unfold sideNext sidePt
  exact (lerp_ne_right hne ht1).symm

omit C in
/-- The point of a position is not in its own open left sector. -/
theorem sideLeft_not_self {W : Polygon} {p : ℕ} {t : ℝ} (hne : W.vtx p ≠ W.vtx ((p + 1) % W.n))
    (ht1 : t < 1) : ¬ sideLeft W p t (sidePt W p t) := by
  unfold sideLeft sideLeftOf
  rw [sub_self]
  exact sideCcw_not_ray_left (sub_ne_zero_of_ne' (sideNext_ne_pt hne ht1))
    (by ufs sideCross) (by ufs sideDot)

omit C in
/-- The left offsets of a segment whose open part lies in the open set `D₀` all lie in one
component of `D₀ \ segment`. -/
theorem sideFaces_chord {D₀ : Set Point} (hD₀ : IsOpen D₀) {a b : Point} (hab : a ≠ b)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ D₀) {c₀ : Point} {t t' : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (h : SideFaces (connectedComponentIn (D₀ \ Chazelle.segment a b) c₀) a b t) :
    SideFaces (connectedComponentIn (D₀ \ Chazelle.segment a b) c₀) a b t' := by
  set t₁ := min t t' / 2
  set t₂ := (max t t' + 1) / 2
  have h1 : 0 < t₁ := by have := lt_min ht.1 ht'.1; sil only [t₁]
  have h2 : t₂ < 1 := by have := max_lt ht.2 ht'.2; sil only [t₂]
  have h3 : t₁ < t := by have := min_le_left t t'; have := ht.1; sil only [t₁]
  have h4 : t₁ < t' := by have := min_le_right t t'; have := ht'.1; sil only [t₁]
  have h5 : t < t₂ := by have := le_max_left t t'; have := ht.2; sil only [t₂]
  have h6 : t' < t₂ := by have := le_max_right t t'; have := ht'.2; sil only [t₂]
  refine sideFaces_edge hab ?_ ⟨h3, h5⟩ ⟨h4, h6⟩ h
  intro s hs
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hD₀ _ (hopen s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  refine ⟨r, hr, fun x hx hxD => ?_⟩
  have hxc : x ∈ Chazelle.segment a b := by
    by_contra hc; exact hxD ⟨hball hx, hc⟩
  exact (Geometry.det_eq_zero_of_mem_segment hxc).le

omit C in
/-- **Splitting a closed walk by a chord (generic form of the side-aware Lemma 2.1).**
Let `W` be a closed walk with nondegenerate edges, `D₀` an open set avoiding the walk in which
every position of `W` is clean, and `c = [a, b]` a segment whose open part lies in `D₀`, meeting
the walk only at `a` and `b`, attached to the walk at positions `A` (point `a`) and `B` (point
`b`).  Suppose that the other positions at `a` (resp. `b`) have left sectors disjoint near `a`
(resp. `b`) from that of `A` (resp. `B`), and that the two sides of `c` at its midpoint lie in
different components of `D₀ \ c`.  Then there are two distinct components `K₁ ≠ K₂` of
`D₀ \ c` such that the small left sector of every position strictly between `A` and `B` lies in
`K₁`, and that of every position strictly between `B` and `A` lies in `K₂`; moreover `K₁` is on
the left of `b → a` and `K₂` on the left of `a → b` (at the midpoint of `c`). -/
theorem sideArc_split (W : Polygon) {D₀ : Set Point} (hD₀ : IsOpen D₀) {a b : Point}
    (hab : a ≠ b) (hnd : ∀ p < W.n, W.vtx p ≠ W.vtx ((p + 1) % W.n))
    (htrace : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → sidePt W p t ∉ D₀)
    (hclean0 : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → SideClean W D₀ p t)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ D₀)
    {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach W (Chazelle.segment a b) pa ta) (hAa : sidePt W pa ta = a)
    (hB : SideAttach W (Chazelle.segment a b) pb tb) (hBb : sidePt W pb tb = b)
    (hdisjA : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → (p = pa → t ≠ ta) → sidePt W p t = a →
      ∃ r > 0, ∀ x ∈ ball a r, sideLeft W pa ta x → ¬ sideLeft W p t x)
    (hdisjB : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → (p = pb → t ≠ tb) → sidePt W p t = b →
      ∃ r > 0, ∀ x ∈ ball b r, sideLeft W pb tb x → ¬ sideLeft W p t x)
    (hsep : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      connectedComponentIn (D₀ \ Chazelle.segment a b) (offset a b (1 / 2) δ) ≠
        connectedComponentIn (D₀ \ Chazelle.segment a b) (offset b a (1 / 2) δ)) :
    ∃ K₁ K₂ : Set Point, K₁ ≠ K₂ ∧
      (∃ c₁, K₁ = connectedComponentIn (D₀ \ Chazelle.segment a b) c₁) ∧
      (∃ c₂, K₂ = connectedComponentIn (D₀ \ Chazelle.segment a b) c₂) ∧
      (∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc (pa + ta) (pb + tb) (p + t) →
        SideSectorIn W K₁ p t) ∧
      (∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc (pb + tb) (pa + ta) (p + t) →
        SideSectorIn W K₂ p t) ∧
      SideFaces K₁ b a (1 / 2) ∧ SideFaces K₂ a b (1 / 2) := by
  set c := Chazelle.segment a b with hc
  set D := D₀ \ c with hD
  obtain ⟨hpa, hta, hta1, haA, ra, hra, hattA⟩ := hA
  obtain ⟨hpb, htb, htb1, hbB, rb, hrb, hattB⟩ := hB
  -- `A` and `B` are on distinct edges
  have hpab : pa ≠ pb := by
    intro h
    subst h
    have hmid := hopen (1 / 2) ⟨by norm_num, by norm_num⟩
    apply htrace pa hpa ((ta + tb) / 2) (by linarith) (by linarith)
    have e : sidePt W pa ((ta + tb) / 2) = lerp a b (1 / 2) := by
      rw [← hAa, ← hBb]; unfold sidePt
      apply point_ext <;> simp [lerp] <;> ring
    rwx [e]
  -- cleanness for `D`
  have hclean : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → (p = pa → t ≠ ta) → (p = pb → t ≠ tb) →
      SideClean W D p t := by
    intro p hp t ht ht1 hnA hnB
    obtain ⟨r0, hr0, hcl0⟩ := hclean0 p hp t ht ht1
    by_cases hpc : sidePt W p t ∈ c
    · -- the point is an endpoint of `c`
      have hcpt : sidePt W p t = a ∨ sidePt W p t = b := by
        obtain ⟨μ, hμ0, hμ1, he⟩ := Geometry.mem_segment_iff_lerp.1 hpc
        rcases hμ0.lt_or_eq with hμ0 | hμ0
        · rcases hμ1.lt_or_eq with hμ1 | hμ1
          · exact absurd (he ▸ hopen μ ⟨hμ0, hμ1⟩) (htrace p hp t ht ht1.le)
          · right; rw [he, hμ1, lerp_one]
        · left; rw [he, ← hμ0, lerp_zero]
      rcases hcpt with hq | hq
      · obtain ⟨r1, hr1, hdis⟩ := hdisjA p hp t ht ht1 hnA hq
        refine ⟨min r0 (min r1 ra), lt_min hr0 (lt_min hr1 hra), fun x hx hxD hxl => ?_⟩
        have hx0 : x ∈ ball (sidePt W p t) r0 := ball_subset_ball (min_le_left _ _) hx
        rw [hq] at hx
        by_cases hxD0 : x ∈ D₀
        · have hxc : x ∈ c := by by_contra h; exact hxD ⟨hxD0, h⟩
          by_cases hxa : x = a
          · -- the point itself is not in any open sector
            rw [hxa, ← hq] at hxl
            exact sideLeft_not_self (hnd p hp) ht1 hxl
          · refine hdis x (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx) ?_ hxl
            refine hattA x hxc (by rwx [hAa]) ?_
            rw [hAa]
            exact lt_of_lt_of_le (mem_ball.1 hx) ((min_le_right _ _).trans (min_le_right _ _))
        · exact hcl0 x hx0 hxD0 hxl
      · obtain ⟨r1, hr1, hdis⟩ := hdisjB p hp t ht ht1 hnB hq
        refine ⟨min r0 (min r1 rb), lt_min hr0 (lt_min hr1 hrb), fun x hx hxD hxl => ?_⟩
        have hx0 : x ∈ ball (sidePt W p t) r0 := ball_subset_ball (min_le_left _ _) hx
        rw [hq] at hx
        by_cases hxD0 : x ∈ D₀
        · have hxc : x ∈ c := by by_contra h; exact hxD ⟨hxD0, h⟩
          by_cases hxb : x = b
          · rw [hxb, ← hq] at hxl
            exact sideLeft_not_self (hnd p hp) ht1 hxl
          · refine hdis x (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx) ?_ hxl
            refine hattB x hxc (by rwx [hBb]) ?_
            rw [hBb]
            exact lt_of_lt_of_le (mem_ball.1 hx) ((min_le_right _ _).trans (min_le_right _ _))
        · exact hcl0 x hx0 hxD0 hxl
    · -- away from `c`
      obtain ⟨r1, hr1, hball⟩ := Metric.isOpen_iff.1
        (Geometry.isClosed_segment a b).isOpen_compl _ hpc
      refine ⟨min r0 r1, lt_min hr0 hr1, fun x hx hxD hxl => ?_⟩
      have hx0 : x ∈ ball (sidePt W p t) r0 := ball_subset_ball (min_le_left _ _) hx
      have hx1 : x ∉ c := hball (ball_subset_ball (min_le_right _ _) hx)
      have hxD0 : x ∉ D₀ := fun h => hxD ⟨h, hx1⟩
      exact hcl0 x hx0 hxD0 hxl
  -- cutting at `A` and at `B`
  have hsegA : Chazelle.segment (sidePt W pa ta) b = c := by rw [hAa]
  have hsegB : Chazelle.segment (sidePt W pb tb) a = c := by rw [hBb, hc, segment_comm]
  have hA' : SideAttach W (Chazelle.segment (sidePt W pa ta) b) pa ta :=
    ⟨hpa, hta, hta1, by rwx [hsegA], ra, hra, by rwx [hsegA]⟩
  have hB' : SideAttach W (Chazelle.segment (sidePt W pb tb) a) pb tb :=
    ⟨hpb, htb, htb1, by rwx [hsegB], rb, hrb, by rwx [hsegB]⟩
  obtain ⟨c₁, hstart₁, hleft₁⟩ := sideCut hA' (by rwx [hAa]) (hnd pa hpa)
    (hclean0 pa hpa ta hta hta1)
  obtain ⟨c₂, hstart₂, hleft₂⟩ := sideCut hB' (by rw [hBb]; exact hab.symm) (hnd pb hpb)
    (hclean0 pb hpb tb htb htb1)
  rw [hsegA] at hstart₁
  rw [hsegA, hAa] at hleft₁
  rw [hsegB] at hstart₂
  rw [hsegB, hBb] at hleft₂
  -- the two sides of the chord
  have hopen' : ∀ s ∈ Ioo (0 : ℝ) 1, lerp b a s ∈ D₀ := by
    intro s hs
    have : lerp b a s = lerp a b (1 - s) := by
      apply point_ext <;> simp [lerp] <;> ring
    rw [this]; exact hopen _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hDba : D₀ \ Chazelle.segment b a = D := by rw [hD, hc, segment_comm]
  obtain ⟨s₁, hs₁, hs₁'⟩ := (hleft₁.and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  obtain ⟨s₂, hs₂, hs₂'⟩ := (hleft₂.and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have h1 : SideFaces (connectedComponentIn D c₁) b a (1 / 2) := by
    have := sideFaces_chord (a := b) (b := a) (c₀ := c₁) hD₀ hab.symm hopen'
      (t := 1 - s₁) (t' := 1 / 2) ⟨by linarith [hs₁'.2], by linarith [hs₁'.1]⟩
      ⟨by norm_num, by norm_num⟩ (by rwx [hDba])
    rwa [hDba] at this
  have h2 : SideFaces (connectedComponentIn D c₂) a b (1 / 2) :=
    sideFaces_chord hD₀ hab hopen ⟨by linarith [hs₂'.2], by linarith [hs₂'.1]⟩
      ⟨by norm_num, by norm_num⟩ hs₂
  refine ⟨connectedComponentIn D c₁, connectedComponentIn D c₂, ?_, ⟨c₁, rfl⟩, ⟨c₂, rfl⟩, ?_, ?_,
    h1, h2⟩
  · -- the two sides of the chord are in different components
    obtain ⟨δ, ⟨hδ1, hδ2⟩, hδ3⟩ := ((h1.and h2).and hsep).exists
    intro heq
    apply hδ3
    rw [← connectedComponentIn_eq hδ1, ← connectedComponentIn_eq hδ2, heq]
  · exact sideArc_chain W hnd hpa hpb hpab hta hta1 htb htb1 hclean hstart₁
  · exact sideArc_chain W hnd hpb hpa hpab.symm htb htb1 hta hta1
      (fun p hp t ht ht1 hB hA => hclean p hp t ht ht1 hA hB) hstart₂

/-! ### The corrected boundary walk -/

omit C in
/-- The Euler tour of the path `0, 1, …, m` rooted at `0`: tour position `j ≤ 2m` visits vertex
`j` for `j ≤ m` and `2m - j` for `j ≥ m`. -/
def sideE (m j : ℕ) : ℕ := if j ≤ m then j else 2 * m - j

/-- The tour position at which the box block is inserted (the top vertex `T` is visited at the
tour positions `T` and `2m - T`): `T` if `β`, else `2m - T`. -/
noncomputable def sideS (β : Bool) : ℕ := if β then C.topIdx else 2 * C.m - C.topIdx

/-- The chain vertex index at position `i ≤ 2m` of the tour of the double boundary starting (and
ending) at the top vertex. -/
noncomputable def sideIdx (β : Bool) (i : ℕ) : ℕ := sideE C.m ((C.sideS β + i) % (2 * C.m))

/-- The tour of the double boundary from the top vertex. -/
noncomputable def sideTour (β : Bool) (i : ℕ) : Point := C.vertex (C.sideIdx β i)

/-- **The corrected boundary walk of `dom C`**: the box block (as in `boundaryWalk`: top of the
slit, the four corners counterclockwise, top of the slit, down the slit) followed by the tour of
the double boundary of the chain from the top vertex, in which the top vertex is left towards
`v_{T+1}` (`β = true`, as in `boundaryWalk`) or towards `v_{T-1}` (`β = false`); the closing edge
goes up the slit.  With `β = C.sideBeta` the walk keeps `dom C` on its left at every corner. -/
noncomputable def sideWalk (β : Bool) : Polygon :=
  ⟨C.boxList ++ C.slitTop :: (List.range (2 * C.m + 1)).map (C.sideTour β)⟩

theorem sideWalk_n (β : Bool) : (C.sideWalk β).n = 2 * C.m + 7 := by
  simp [Polygon.n, sideWalk, boxList]

theorem sideWalk_vtx_zero (β : Bool) : (C.sideWalk β).vtx 0 = C.slitTop := rfl
theorem sideWalk_vtx_one (β : Bool) : (C.sideWalk β).vtx 1 = (-C.radius, C.radius) := rfl
theorem sideWalk_vtx_two (β : Bool) : (C.sideWalk β).vtx 2 = (-C.radius, -C.radius) := rfl
theorem sideWalk_vtx_three (β : Bool) : (C.sideWalk β).vtx 3 = (C.radius, -C.radius) := rfl
theorem sideWalk_vtx_four (β : Bool) : (C.sideWalk β).vtx 4 = (C.radius, C.radius) := rfl
theorem sideWalk_vtx_five (β : Bool) : (C.sideWalk β).vtx 5 = C.slitTop := rfl

theorem sideWalk_vtx_tour (β : Bool) {i : ℕ} (hi : i ≤ 2 * C.m) :
    (C.sideWalk β).vtx (i + 6) = C.sideTour β i := by
  unfold Polygon.vtx sideWalk boxList
  rw [List.getD_eq_getElem?_getD]
  simp only [List.cons_append, List.nil_append]
  rw [show i + 6 = (i + 1) + 5 by ring]
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem sideWalk_vtx_wrap (β : Bool) :
    (C.sideWalk β).vtx ((2 * C.m + 6 + 1) % (C.sideWalk β).n) = C.slitTop := by
  rwr [sideWalk_n, show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self]

theorem two_m_pos : 0 < 2 * C.m := by have := C.one_le; omega

omit C in
theorem sideE_le {m j : ℕ} (hj : j ≤ 2 * m) : sideE m j ≤ m := by
  unfold sideE; splao

omit C in
theorem sideE_zero (m : ℕ) : sideE m 0 = 0 := by simp [sideE]

omit C in
theorem sideE_two_m (m : ℕ) : sideE m (2 * m) = 0 := by
  unfold sideE; splao

theorem sideS_lt (β : Bool) : C.sideS β ≤ 2 * C.m := by
  unfold sideS; have := C.topIdx_le; splao

theorem sideE_sideS (β : Bool) : sideE C.m (C.sideS β % (2 * C.m)) = C.topIdx := by
  have hT := C.topIdx_le
  have hm := C.two_m_pos
  unfold sideS
  cases β
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases Nat.eq_zero_or_pos C.topIdx with h0 | h0
    · rw [h0, Nat.sub_zero, Nat.mod_self, sideE_zero]
    · rw [Nat.mod_eq_of_lt (by omega)]; unfold sideE; splao
  · simp only [↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega)]; unfold sideE; rw [ite_eq_left hT]

theorem sideIdx_zero (β : Bool) : C.sideIdx β 0 = C.topIdx := by
  unfold sideIdx; rw [add_zero, sideE_sideS]

theorem sideIdx_two_m (β : Bool) : C.sideIdx β (2 * C.m) = C.topIdx := by
  unfold sideIdx; rw [Nat.add_mod_right, sideE_sideS]

theorem sideIdx_le (β : Bool) (i : ℕ) : C.sideIdx β i ≤ C.m :=
  sideE_le (Nat.mod_lt _ C.two_m_pos).le

theorem sideTour_zero (β : Bool) : C.sideTour β 0 = C.top := by
  unfold sideTour top; rw [sideIdx_zero]

theorem sideTour_two_m (β : Bool) : C.sideTour β (2 * C.m) = C.top := by
  unfold sideTour top; rw [sideIdx_two_m]

/-- The tour index one step later, in terms of the tour position `j = (s + i) mod 2m`. -/
theorem sideIdx_succ (β : Bool) (i : ℕ) :
    C.sideIdx β (i + 1) = sideE C.m ((C.sideS β + i) % (2 * C.m) + 1) := by
  unfold sideIdx
  have hm := C.two_m_pos
  have hlt := Nat.mod_lt (C.sideS β + i) hm
  have e : (C.sideS β + (i + 1)) % (2 * C.m) = ((C.sideS β + i) % (2 * C.m) + 1) % (2 * C.m) :=
    (side_idx_succ hm _ _).symm
  rw [e]
  rcases lt_or_eq_of_le (show (C.sideS β + i) % (2 * C.m) + 1 ≤ 2 * C.m by omega) with h | h
  · rw [Nat.mod_eq_of_lt h]
  · rw [h, Nat.mod_self, sideE_zero, sideE_two_m]

/-! ### Local structure of the chain -/

theorem sideEdgeIdx_inj {j k : ℕ} (hj : j ≤ C.m) (hk : k ≤ C.m) (h : C.edgeIdx j = C.edgeIdx k) :
    j = k := by
  unfold edgeIdx at h
  have hmn := C.m_lt
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' C.s h) (by omega) (by omega)

/-- Distinct chain vertex indices give distinct vertices. -/
theorem sideVertex_inj (hP : C.P.Simple) {j k : ℕ} (hj : j ≤ C.m) (hk : k ≤ C.m)
    (h : C.vertex j = C.vertex k) : j = k :=
  C.sideEdgeIdx_inj hj hk (simple_vtx_inj hP (C.edgeIdx_lt j) (C.edgeIdx_lt k) h)

/-- Consecutive chain vertices are distinct. -/
theorem sideVertex_succ_ne (hP : C.P.Simple) (k : ℕ) : C.vertex k ≠ C.vertex (k + 1) := by
  have := simple_vtx_succ_ne hP (C.edgeIdx_lt k)
  rw [C.edgeIdx_succ] at this
  exact this

/-- A chain vertex lies exactly on its incident chain edges. -/
theorem sideVertex_mem_chainEdge_iff (hP : C.P.Simple) {j k : ℕ} (hj : j ≤ C.m) (hk : k < C.m) :
    C.vertex j ∈ C.chainEdge k ↔ j = k ∨ j = k + 1 := by
  constructor
  · intro h
    rcases (simple_vtx_mem_edge_iff hP (C.edgeIdx_lt j) (C.edgeIdx_lt k)).1 h with h1 | h1
    · exact Or.inl (C.sideEdgeIdx_inj hj hk.le h1.symm)
    · right
      have h2 : (C.edgeIdx k + 1) % C.P.n = C.edgeIdx j := by
        rw [h1]; exact prevIdx_succ C.P (C.edgeIdx_lt j)
      rw [C.edgeIdx_succ] at h2
      exact (C.sideEdgeIdx_inj (by omega) hj h2).symm
  · rintro (rfl | rfl)
    · exact C.vertex_mem_chainEdge j
    · exact C.vertex_succ_mem_chainEdge k

/-- A point of an open chain edge lies on no other chain edge. -/
theorem sideOpen_not_mem_chainEdge (hP : C.P.Simple) {k j : ℕ} (hk : k < C.m) (hj : j < C.m)
    (hjk : j ≠ k) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    lerp (C.vertex k) (C.vertex (k + 1)) t ∉ C.chainEdge j := by
  have := simple_openEdge_not_mem_other hP (C.edgeIdx_lt k) ht (C.edgeIdx_lt j)
    (fun h => hjk (C.sideEdgeIdx_inj hj.le hk.le h))
  rw [C.edgeIdx_succ] at this
  exact this

/-- A point of an open chain edge is not a chain vertex. -/
theorem sideOpen_ne_vertex (hP : C.P.Simple) {k j : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    lerp (C.vertex k) (C.vertex (k + 1)) t ≠ C.vertex j := by
  have := simple_openEdge_ne_vtx hP (C.edgeIdx_lt k) ht (C.edgeIdx_lt j)
  rw [C.edgeIdx_succ] at this
  exact this

/-- The chain meets the slit only at the top vertex. -/
theorem sideSet_inter_slit {x : Point} (hx : x ∈ C.set) (hs : x ∈ C.slit) : x = C.top := by
  have h1 := C.snd_le_top_of_mem_set hx
  obtain ⟨h2, h3, -⟩ := C.mem_slit_iff.1 hs
  exact Prod.ext h2 (le_antisymm h1 h3)

/-- **Local obstacles near a point of the box**: near `q`, the points outside the domain lie on
the chain edges through `q`, or on the slit if `q` is on it. -/
theorem sideLocal (q : Point) (hq : q ∈ box C.radius) :
    ∃ r > 0, ∀ x ∈ ball q r, x ∉ C.dom →
      (∃ k < C.m, q ∈ C.chainEdge k ∧ x ∈ C.chainEdge k) ∨ (q ∈ C.slit ∧ x ∈ C.slit) := by
  classical
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 (isOpen_box C.radius) q hq
  set F : Set Point := ⋃ k ∈ (Finset.range C.m).filter (fun k => q ∉ C.chainEdge k), C.chainEdge k
    with hF
  have hFc : IsClosed F := isClosed_biUnion_finset fun k _ => isClosed_edge C.P _
  have hqF : q ∉ F := by
    simp only [hF, mem_iUnion, Finset.mem_filter, not_exists]
    intro k hk hq'; exact hk.2 hq'
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl q hqF
  obtain ⟨r₃, hr₃, hb₃⟩ : ∃ r₃ > 0, q ∉ C.slit → ∀ x ∈ ball q r₃, x ∉ C.slit := by
    by_cases hqs : q ∈ C.slit
    · exact ⟨1, one_pos, fun h => absurd hqs h⟩
    · obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 (Geometry.isClosed_segment _ _).isOpen_compl q hqs
      exact ⟨r, hr, fun _ x hx => hb hx⟩
  refine ⟨min r₁ (min r₂ r₃), lt_min hr₁ (lt_min hr₂ hr₃), fun x hx hxd => ?_⟩
  have hx1 : x ∈ ball q r₁ := ball_subset_ball (min_le_left _ _) hx
  have hx2 : x ∈ ball q r₂ := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx
  have hx3 : x ∈ ball q r₃ := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hx
  rw [C.mem_dom_iff] at hxd
  push Not at hxd
  by_cases hxs : x ∈ C.set
  · left
    obtain ⟨k, hk, hxk⟩ := hxs
    refine ⟨k, hk, ?_, hxk⟩
    by_contra hqk
    apply hb₂ hx2
    simp only [hF, mem_iUnion, Finset.mem_filter, Finset.mem_range]
    exact ⟨k, ⟨hk, hqk⟩, hxk⟩
  · right
    have hxs'  := hxd (hb₁ hx1) hxs
    by_cases hqs : q ∈ C.slit
    · exact ⟨hqs, hxs'⟩
    · exact absurd hxs' (hb₃ hqs x hx3)

/-- Near a chain vertex, the points outside the domain lie on its (at most two) chain edges, or on
the slit if it is the top vertex. -/
theorem sideLocal_vertex (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) :
    ∃ r > 0, ∀ x ∈ ball (C.vertex k) r, x ∉ C.dom →
      (1 ≤ k ∧ x ∈ Chazelle.segment (C.vertex (k - 1)) (C.vertex k)) ∨
      (k < C.m ∧ x ∈ Chazelle.segment (C.vertex k) (C.vertex (k + 1))) ∨
      (k = C.topIdx ∧ x ∈ C.slit) := by
  obtain ⟨r, hr, h⟩ := C.sideLocal (C.vertex k) (C.set_subset_box (C.vertex_mem_set hk))
  refine ⟨r, hr, fun x hx hxd => ?_⟩
  rcases h x hx hxd with ⟨j, hj, hkj, hxj⟩ | ⟨hks, hxs⟩
  · rw [C.chainEdge_eq] at hxj
    rcases (C.sideVertex_mem_chainEdge_iff hP hk hj).1 hkj with rfl | rfl
    · exact Or.inr (Or.inl ⟨hj, hxj⟩)
    · left; refine ⟨by omega, ?_⟩; rwa [Nat.add_sub_cancel]
  · right; right
    refine ⟨?_, hxs⟩
    have := C.sideSet_inter_slit (C.vertex_mem_set hk) hks
    exact C.sideVertex_inj hP hk C.topIdx_le this

/-- Near a point of an open chain edge, the points outside the domain lie on that edge. -/
theorem sideLocal_open (hP : C.P.Simple) {k : ℕ} (hk : k < C.m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ r > 0, ∀ x ∈ ball (lerp (C.vertex k) (C.vertex (k + 1)) t) r, x ∉ C.dom →
      x ∈ Chazelle.segment (C.vertex k) (C.vertex (k + 1)) := by
  have hq : lerp (C.vertex k) (C.vertex (k + 1)) t ∈ C.set := by
    refine ⟨k, hk, ?_⟩
    rw [C.chainEdge_eq]; exact lerp_mem_segment _ _ ht.1.le ht.2.le
  obtain ⟨r, hr, h⟩ := C.sideLocal _ (C.set_subset_box hq)
  refine ⟨r, hr, fun x hx hxd => ?_⟩
  rcases h x hx hxd with ⟨j, hj, hkj, hxj⟩ | ⟨hks, hxs⟩
  · by_cases hjk : j = k
    · subst hjk; rwa [C.chainEdge_eq] at hxj
    · exact absurd hkj (C.sideOpen_not_mem_chainEdge hP hk hj hjk ht)
  · exfalso
    have := C.sideSet_inter_slit hq hks
    exact C.sideOpen_ne_vertex hP ht this

/-! ### Left sectors and segments -/

omit C in
theorem sideCcw_zero (B A : Point) : ¬ sideCcw B 0 A := by
  unfold sideCcw sideCross sideDot
  simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, zero_mul, sub_self]
  rintro (⟨-, h, -⟩ | ⟨-, h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h | h⟩) <;> simp_all

omit C in
/-- The segments of a corner are not in its open left sector. -/
theorem sideLeftOf_not_seg_prev {a v b x : Point} (hav : a ≠ v)
    (hx : x ∈ Chazelle.segment a v) : ¬ sideLeftOf a v b x := by
  obtain ⟨μ, hμ0, hμ1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  unfold sideLeftOf
  apply sideCcw_not_ray_right (sub_ne_zero_of_ne' hav)
  · unfold sideCross; sir only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd]
  · unfold sideDot; simp only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd]
    nlinarith [mul_nonneg (sub_nonneg.2 hμ1) (add_nonneg (sq_nonneg (a.1 - v.1))
      (sq_nonneg (a.2 - v.2)))]

omit C in
theorem sideLeftOf_not_seg_next {a v b x : Point} (hbv : b ≠ v)
    (hx : x ∈ Chazelle.segment v b) : ¬ sideLeftOf a v b x := by
  obtain ⟨μ, hμ0, hμ1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  unfold sideLeftOf
  apply sideCcw_not_ray_left (sub_ne_zero_of_ne' hbv)
  · unfold sideCross; sir only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd]
  · unfold sideDot; simp only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd]
    nlinarith [mul_nonneg hμ0 (add_nonneg (sq_nonneg (b.1 - v.1)) (sq_nonneg (b.2 - v.2)))]

omit C in
/-- If a point `w` is not in the open left sector, neither is any point of `[v, w]`. -/
theorem sideLeftOf_not_seg {a v b w x : Point} (hw : ¬ sideLeftOf a v b w)
    (hx : x ∈ Chazelle.segment v w) : ¬ sideLeftOf a v b x := by
  obtain ⟨μ, hμ0, hμ1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  unfold sideLeftOf at *
  have e : lerp v w μ - v = μ • (w - v) := by
    apply point_ext <;> simp [lerp]
  rw [e]
  rcases hμ0.lt_or_eq with hμ | hμ
  · rwa [sideCcw_smul hμ]
  · rw [← hμ, zero_smul]; exact sideCcw_zero _ _

/-! ### The corners of the tour -/

theorem sideIdx_eq (β : Bool) (i : ℕ) : C.sideIdx β i = sideE C.m ((C.sideS β + i) % (2 * C.m)) :=
  rfl

theorem sideS_mod (β : Bool) :
    (C.sideS β % (2 * C.m) = C.topIdx ∧ (β = true ∨ C.topIdx = 0 ∨ C.topIdx = C.m)) ∨
      (C.sideS β % (2 * C.m) = 2 * C.m - C.topIdx ∧ 0 < C.topIdx ∧ β = false) := by
  have hT := C.topIdx_le
  have hm := C.one_le
  unfold sideS
  cases β
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases Nat.eq_zero_or_pos C.topIdx with h0 | h0
    · left; rw [h0, Nat.sub_zero, Nat.mod_self]; exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    · right; rw [Nat.mod_eq_of_lt (by omega)]; exact ⟨rfl, h0, trivial⟩
  · simp only [↓reduceIte]
    left; rw [Nat.mod_eq_of_lt (by omega)]; exact ⟨rfl, Or.inl trivial⟩

/-- **Classification of the corners of the tour**: at an inner position of the tour the walk
passes a chain vertex `k` forwards (`k-1, k, k+1`) or backwards (`k+1, k, k-1`), or turns around
a chain endpoint. -/
theorem sideTour_corner (β : Bool) {i : ℕ} (hi0 : 0 < i) (_hi : i < 2 * C.m) :
    (0 < C.sideIdx β i ∧ C.sideIdx β i < C.m ∧ C.sideIdx β (i - 1) + 1 = C.sideIdx β i ∧
        C.sideIdx β (i + 1) = C.sideIdx β i + 1) ∨
      (0 < C.sideIdx β i ∧ C.sideIdx β i < C.m ∧ C.sideIdx β (i - 1) = C.sideIdx β i + 1 ∧
        C.sideIdx β (i + 1) + 1 = C.sideIdx β i) ∨
      (C.sideIdx β i = 0 ∧ C.sideIdx β (i - 1) = 1 ∧ C.sideIdx β (i + 1) = 1) ∨
      (C.sideIdx β i = C.m ∧ C.sideIdx β (i - 1) + 1 = C.m ∧ C.sideIdx β (i + 1) + 1 = C.m) := by
  have hm := C.one_le
  have hm2 := C.two_m_pos
  have e1 : C.sideIdx β i = sideE C.m ((C.sideS β + (i - 1)) % (2 * C.m) + 1) := by
    have := C.sideIdx_succ β (i - 1); rwa [Nat.sub_add_cancel hi0] at this
  have e2 := C.sideIdx_succ β i
  have e0 := C.sideIdx_eq β (i - 1)
  have hj' := Nat.mod_lt (C.sideS β + (i - 1)) hm2
  have hj : (C.sideS β + i) % (2 * C.m) = ((C.sideS β + (i - 1)) % (2 * C.m) + 1) % (2 * C.m) := by
    rw [side_idx_succ hm2, Nat.sub_add_cancel hi0]
  rw [e1, e2, e0, hj]
  generalize (C.sideS β + (i - 1)) % (2 * C.m) = j at hj' ⊢
  rcases lt_or_eq_of_le (show j + 1 ≤ 2 * C.m by omega) with h | h
  · rw [Nat.mod_eq_of_lt h]
    unfold sideE
    splao
  · rw [h, Nat.mod_self]
    unfold sideE
    splao

/-- The tour positions other than the ends that visit the top vertex: the middle passage, with
the same neighbours as the ends but traversed from the first neighbour to the last. -/
theorem sideTour_top_mid (β : Bool) {i : ℕ} (hi0 : 0 < i) (hi : i < 2 * C.m)
    (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) (hiT : C.sideIdx β i = C.topIdx) :
    C.sideIdx β (i - 1) = C.sideIdx β 1 ∧ C.sideIdx β (i + 1) = C.sideIdx β (2 * C.m - 1) := by
  have hm2 := C.two_m_pos
  obtain ⟨S, hSdef⟩ : ∃ S, S = C.sideS β % (2 * C.m) := ⟨_, rfl⟩
  have hS : S = C.topIdx ∨ S = 2 * C.m - C.topIdx := by
    rcases C.sideS_mod β with ⟨h, -⟩ | ⟨h, -⟩
    · left; rw [hSdef, h]
    · right; rw [hSdef, h]
  have f1 : C.sideIdx β 1 = sideE C.m (S + 1) := by
    rw [hSdef]; have := C.sideIdx_succ β 0; rwa [add_zero, zero_add] at this
  have f2 : C.sideIdx β (2 * C.m - 1) = sideE C.m (S - 1) := by
    rw [sideIdx_eq]; congr 1
    rw [Nat.add_mod, ← hSdef, Nat.mod_eq_of_lt (show 2 * C.m - 1 < 2 * C.m by omega)]
    rcases side_mod_cases (show S + (2 * C.m - 1) < 2 * (2 * C.m) by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · rwo [h2]
  obtain ⟨j, hjdef⟩ : ∃ j, j = (C.sideS β + (i - 1)) % (2 * C.m) := ⟨_, rfl⟩
  have hj2 : j < 2 * C.m := hjdef ▸ Nat.mod_lt _ hm2
  have e1 : C.sideIdx β i = sideE C.m (j + 1) := by
    rw [hjdef]; have := C.sideIdx_succ β (i - 1); rwa [Nat.sub_add_cancel hi0] at this
  have e0 : C.sideIdx β (i - 1) = sideE C.m j := by rwr [hjdef]
  have hji : (C.sideS β + i) % (2 * C.m) = (j + 1) % (2 * C.m) := by
    rw [hjdef, side_idx_succ hm2, Nat.sub_add_cancel hi0]
  have e2 : C.sideIdx β (i + 1) = sideE C.m ((j + 1) % (2 * C.m) + 1) := by
    rw [C.sideIdx_succ, hji]
  have hne : (j + 1) % (2 * C.m) ≠ S := by
    rw [← hji, hSdef]; intro h
    have h' : C.sideS β + i ≡ C.sideS β + 0 [MOD 2 * C.m] := by rwx [add_zero]
    have := Nat.ModEq.add_left_cancel' (C.sideS β) h'
    exact absurd (Nat.ModEq.eq_of_lt_of_lt this hi hm2) (by omega)
  rw [e1] at hiT
  rw [e0, e2, f1, f2]
  have hT := C.topIdx_le
  have key : j + 1 < 2 * C.m ∧ j + 1 = 2 * C.m - S := by
    unfold sideE at hiT
    rcases lt_or_eq_of_le (show j + 1 ≤ 2 * C.m by omega) with h | h
    · rw [Nat.mod_eq_of_lt h] at hne
      split_ifs at hiT <;> omega
    · split_ifs at hiT <;> omega
  rw [Nat.mod_eq_of_lt key.1]
  constructor <;> unfold sideE <;> split_ifs <;> omega

theorem sideIdx_one (β : Bool) : C.sideIdx β 1 = sideE C.m (C.sideS β % (2 * C.m) + 1) := by
  have := C.sideIdx_succ β 0; rwa [add_zero, zero_add] at this

theorem sideIdx_last (β : Bool) :
    C.sideIdx β (2 * C.m - 1) = sideE C.m ((C.sideS β % (2 * C.m) + (2 * C.m - 1)) % (2 * C.m)) := by
  rw [sideIdx_eq, Nat.add_mod (C.sideS β), Nat.mod_eq_of_lt (show 2 * C.m - 1 < 2 * C.m by
    have := C.two_m_pos; omega)]

/-- The neighbours of the top vertex along the walk: the first and the last chain vertex of the
tour are the chain neighbours of the top vertex (the same one if the top vertex is an endpoint of
the chain, different ones otherwise). -/
theorem sideTour_nbrs (β : Bool) :
    (1 ≤ C.topIdx → C.topIdx - 1 = C.sideIdx β 1 ∨ C.topIdx - 1 = C.sideIdx β (2 * C.m - 1)) ∧
    (C.topIdx < C.m → C.topIdx + 1 = C.sideIdx β 1 ∨ C.topIdx + 1 = C.sideIdx β (2 * C.m - 1)) ∧
    (C.sideIdx β 1 + 1 = C.topIdx ∨ C.sideIdx β 1 = C.topIdx + 1) ∧
    (C.sideIdx β (2 * C.m - 1) + 1 = C.topIdx ∨ C.sideIdx β (2 * C.m - 1) = C.topIdx + 1) ∧
    (0 < C.topIdx → C.topIdx < C.m → C.sideIdx β 1 ≠ C.sideIdx β (2 * C.m - 1)) := by
  have hm := C.one_le
  have hT := C.topIdx_le
  rw [C.sideIdx_one, C.sideIdx_last]
  rcases C.sideS_mod β with ⟨hs, -⟩ | ⟨hs, h0, -⟩ <;> rw [hs]
  · rcases side_mod_cases (show C.topIdx + (2 * C.m - 1) < 2 * (2 * C.m) by omega) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> unfold sideE <;> split_ifs <;> omega
  · rcases side_mod_cases (show 2 * C.m - C.topIdx + (2 * C.m - 1) < 2 * (2 * C.m) by omega) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> unfold sideE <;> split_ifs <;> omega

/-- An inner tour position visits the top vertex only if it is not an endpoint of the chain. -/
theorem sideTour_top_inner (β : Bool) {i : ℕ} (hi0 : 0 < i) (hi : i < 2 * C.m)
    (hiT : C.sideIdx β i = C.topIdx) : 0 < C.topIdx ∧ C.topIdx < C.m := by
  have hm2 := C.two_m_pos
  have hT := C.topIdx_le
  have hne : (C.sideS β + i) % (2 * C.m) ≠ C.sideS β % (2 * C.m) := by
    intro h
    have h' : C.sideS β + i ≡ C.sideS β + 0 [MOD 2 * C.m] := by rwx [add_zero]
    have := Nat.ModEq.add_left_cancel' (C.sideS β) h'
    exact absurd (Nat.ModEq.eq_of_lt_of_lt this hi hm2) (by omega)
  rw [sideIdx_eq] at hiT
  have hj := Nat.mod_lt (C.sideS β + i) hm2
  rcases C.sideS_mod β with ⟨hs, -⟩ | ⟨hs, h0, -⟩
  · rw [hs] at hne
    generalize (C.sideS β + i) % (2 * C.m) = j at hne hiT hj
    unfold sideE at hiT; split_ifs at hiT <;> omega
  · rw [hs] at hne
    generalize (C.sideS β + i) % (2 * C.m) = j at hne hiT hj
    unfold sideE at hiT; split_ifs at hiT <;> omega

/-- One step of the tour moves to an adjacent chain vertex. -/
theorem sideTour_step (β : Bool) (i : ℕ) :
    C.sideIdx β (i + 1) = C.sideIdx β i + 1 ∨ C.sideIdx β (i + 1) + 1 = C.sideIdx β i := by
  have hm2 := C.two_m_pos
  rw [C.sideIdx_succ, sideIdx_eq]
  have hj := Nat.mod_lt (C.sideS β + i) hm2
  generalize (C.sideS β + i) % (2 * C.m) = j at hj ⊢
  unfold sideE; splao

/-! ### The order at the top vertex -/

/-- The two chain edges at an inner chain vertex meet only at it. -/
theorem sideChain_meet (hP : C.P.Simple) {k : ℕ} (hk0 : 0 < k) (hkm : k < C.m) :
    Chazelle.segment (C.vertex (k - 1)) (C.vertex k) ∩
      Chazelle.segment (C.vertex k) (C.vertex (k + 1)) ⊆ {C.vertex k} := by
  rintro x ⟨hx1, hx2⟩
  have e1 : C.chainEdge (k - 1) = Chazelle.segment (C.vertex (k - 1)) (C.vertex k) := by
    rw [C.chainEdge_eq, Nat.sub_add_cancel hk0]
  have hx1' : x ∈ C.P.edge (C.edgeIdx (k - 1)) := by
    show x ∈ C.chainEdge (k - 1); rwx [e1]
  have hx2' : x ∈ C.P.edge (C.edgeIdx k) := by
    show x ∈ C.chainEdge k; rwx [C.chainEdge_eq]
  have hne : C.edgeIdx (k - 1) ≠ C.edgeIdx k := fun h =>
    absurd (C.sideEdgeIdx_inj (by omega) (by omega) h) (by omega)
  have hmem : x ∈ C.P.edge (C.edgeIdx (k - 1)) ∩ C.P.edge (C.edgeIdx k) := ⟨hx1', hx2'⟩
  rw [simple_edge_inter hP (C.edgeIdx_lt _) (C.edgeIdx_lt _) hne] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [C.edgeIdx_succ, Nat.sub_add_cancel hk0] at h1
  rw [C.edgeIdx_succ] at h2
  rcases h1 with h1 | h1
  · exfalso
    have h1'  := h1
    rcases h2 with h2 | h2
    · have := C.sideVertex_inj hP (by omega) (by omega) (h1'.symm.trans h2)
      omega
    · have := C.sideVertex_inj hP (by omega) (by omega) (h1'.symm.trans h2)
      omega
  · exact h1

/-- The two chain edges at an inner chain vertex do not leave it in the same direction. -/
theorem sideChain_nonSpike (hP : C.P.Simple) {k : ℕ} (hk0 : 0 < k) (hkm : k < C.m) :
    sideNonSpike (C.vertex (k + 1) - C.vertex k) (C.vertex (k - 1) - C.vertex k) ∧
      sideNonSpike (C.vertex (k - 1) - C.vertex k) (C.vertex (k + 1) - C.vertex k) := by
  have hav : C.vertex (k - 1) ≠ C.vertex k := by
    have := C.sideVertex_succ_ne hP (k - 1); rwa [Nat.sub_add_cancel hk0] at this
  have hvb  := C.sideVertex_succ_ne hP k
  have key : sideCross (C.vertex (k + 1) - C.vertex k) (C.vertex (k - 1) - C.vertex k) = 0 →
      sideDot (C.vertex (k + 1) - C.vertex k) (C.vertex (k - 1) - C.vertex k) < 0 := by
    intro hc
    rw [sideCross_corner] at hc
    have := dir_pos_of_collinear hav hvb (C.sideChain_meet hP hk0 hkm) hc
    unfold sideDot; sil only [Prod.fst_sub, Prod.snd_sub]
  refine ⟨fun ⟨hc, hd⟩ => absurd (key hc) (not_lt.2 hd.le), fun ⟨hc, hd⟩ => ?_⟩
  rw [sideCross_swap] at hc
  rw [sideDot_comm] at hd
  exact absurd (key (neg_eq_zero.1 hc)) (not_lt.2 hd.le)

/-- **The walk turns correctly at the top vertex**: the top vertex is an endpoint of the chain,
or, going down the slit, the direction of the slit lies strictly inside the counterclockwise arc
from the first chain neighbour of the walk to the last one. -/
def SideGood (β : Bool) : Prop :=
  C.topIdx = 0 ∨ C.topIdx = C.m ∨
    sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top) (C.sideTour β (2 * C.m - 1) - C.top)

theorem sideSlitTop_ne_top : C.slitTop ≠ C.top := by
  intro h
  have := congrArg Prod.snd h
  simp only [slitTop] at this
  linarith [C.top_snd_lt_radius]

theorem sideTour_one_ne_top (hP : C.P.Simple) (β : Bool) : C.sideTour β 1 ≠ C.top := by
  intro h
  have := C.sideVertex_inj hP (C.sideIdx_le β 1) C.topIdx_le h
  rcases (C.sideTour_nbrs β).2.2.1 with h' | h' <;> omega

theorem sideTour_last_ne_top (hP : C.P.Simple) (β : Bool) :
    C.sideTour β (2 * C.m - 1) ≠ C.top := by
  intro h
  have := C.sideVertex_inj hP (C.sideIdx_le β _) C.topIdx_le h
  rcases (C.sideTour_nbrs β).2.2.2.1 with h' | h' <;> omega

theorem sideTop_nonSpike (hP : C.P.Simple) (β : Bool) (hT0 : 0 < C.topIdx)
    (hTm : C.topIdx < C.m) :
    sideNonSpike (C.sideTour β 1 - C.top) (C.sideTour β (2 * C.m - 1) - C.top) := by
  obtain ⟨-, -, h1, h2, h3⟩ := C.sideTour_nbrs β
  have hne := h3 hT0 hTm
  have hns := C.sideChain_nonSpike hP hT0 hTm
  unfold sideTour top
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · omega
  · rw [show C.sideIdx β 1 = C.topIdx - 1 by omega, h2]; exact hns.2
  · rw [h1, show C.sideIdx β (2 * C.m - 1) = C.topIdx - 1 by omega]; exact hns.1
  · omega

/-- At the middle passage through the top vertex, the slit is not in the left sector. -/
theorem sideTop_mid_slit (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) (hT0 : 0 < C.topIdx)
    (hTm : C.topIdx < C.m) :
    ¬ sideLeftOf (C.sideTour β 1) C.top (C.sideTour β (2 * C.m - 1)) C.slitTop := by
  have hord : sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top)
      (C.sideTour β (2 * C.m - 1) - C.top) := by
    rcases hβ with h | h | h
    · omega
    · omega
    · exact h
  unfold sideLeftOf
  exact sideCcw_asymm (sub_ne_zero_of_ne' (C.sideTour_one_ne_top hP β))
    (C.sideTop_nonSpike hP β hT0 hTm) hord

/-- At the first corner of the top vertex (down the slit, then to the first neighbour), the
last neighbour is not in the left sector. -/
theorem sideTop_first_other (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β)
    (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) :
    ¬ sideLeftOf C.slitTop C.top (C.sideTour β 1) (C.sideTour β (2 * C.m - 1)) := by
  have hord : sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top)
      (C.sideTour β (2 * C.m - 1) - C.top) := by
    rcases hβ with h | h | h
    · omega
    · omega
    · exact h
  unfold sideLeftOf
  intro h
  have := sideCcw_sub_left (sub_ne_zero_of_ne' (C.sideTour_one_ne_top hP β)) hord h
  exact sideCcw_not_ray_right (sub_ne_zero_of_ne' (C.sideTour_last_ne_top hP β))
    (sideCross_self _) (sideDot_self_pos (sub_ne_zero_of_ne' (C.sideTour_last_ne_top hP β))).le
    this

/-- At the last corner of the top vertex (from the last neighbour, then up the slit), the first
neighbour is not in the left sector. -/
theorem sideTop_last_other (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β)
    (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) :
    ¬ sideLeftOf (C.sideTour β (2 * C.m - 1)) C.top C.slitTop (C.sideTour β 1) := by
  have hord : sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top)
      (C.sideTour β (2 * C.m - 1) - C.top) := by
    rcases hβ with h | h | h
    · omega
    · omega
    · exact h
  unfold sideLeftOf
  intro h
  have := sideCcw_sub_right (sub_ne_zero_of_ne' (C.sideTour_one_ne_top hP β))
    (sub_ne_zero_of_ne' C.sideSlitTop_ne_top) (sub_ne_zero_of_ne' (C.sideTour_last_ne_top hP β))
    hord h
  exact sideCcw_not_ray_left (sub_ne_zero_of_ne' (C.sideTour_one_ne_top hP β))
    (sideCross_self _) (sideDot_self_pos (sub_ne_zero_of_ne' (C.sideTour_one_ne_top hP β))).le
    this

/-! ### Cleanness of the tour positions of the corrected walk -/

theorem sideWalk_prev_tour (β : Bool) {i : ℕ} (hi : 1 ≤ i) (hi2 : i ≤ 2 * C.m) :
    (i + 6 + (C.sideWalk β).n - 1) % (C.sideWalk β).n = (i - 1) + 6 := by
  rw [sideWalk_n, show i + 6 + (2 * C.m + 7) - 1 = (i - 1 + 6) + (2 * C.m + 7) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem sideWalk_next_tour (β : Bool) {i : ℕ} (hi : i < 2 * C.m) :
    (i + 6 + 1) % (C.sideWalk β).n = (i + 1) + 6 := by
  rw [sideWalk_n, Nat.mod_eq_of_lt (by omega)]

theorem sideWalk_prev_six (β : Bool) : (0 + 6 + (C.sideWalk β).n - 1) % (C.sideWalk β).n = 5 := by
  rw [sideWalk_n, show 0 + 6 + (2 * C.m + 7) - 1 = 5 + (2 * C.m + 7) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem sideWalk_next_last (β : Bool) : (2 * C.m + 6 + 1) % (C.sideWalk β).n = 0 := by
  rw [sideWalk_n, show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self]

theorem sideVertex_pred_ne (hP : C.P.Simple) {k : ℕ} (hk : 1 ≤ k) :
    C.vertex (k - 1) ≠ C.vertex k := by
  have := C.sideVertex_succ_ne hP (k - 1); rwa [Nat.sub_add_cancel hk] at this

/-- **Cleanness at an inner corner of the tour.** -/
theorem sideClean_tour_vertex (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) {i : ℕ}
    (hi0 : 0 < i) (hi : i < 2 * C.m) : SideClean (C.sideWalk β) C.dom (i + 6) 0 := by
  have hprev : (C.sideWalk β).vtx ((i + 6 + (C.sideWalk β).n - 1) % (C.sideWalk β).n) =
      C.vertex (C.sideIdx β (i - 1)) := by
    rwr [C.sideWalk_prev_tour β hi0 hi.le, C.sideWalk_vtx_tour β (by omega)]
  have hcur : (C.sideWalk β).vtx (i + 6) = C.vertex (C.sideIdx β i) :=
    C.sideWalk_vtx_tour β hi.le
  have hnext : (C.sideWalk β).vtx ((i + 6 + 1) % (C.sideWalk β).n) =
      C.vertex (C.sideIdx β (i + 1)) := by
    rwr [C.sideWalk_next_tour β hi, C.sideWalk_vtx_tour β (by omega)]
  obtain ⟨r, hr, hloc⟩ := C.sideLocal_vertex hP (C.sideIdx_le β i)
  refine ⟨r, hr, fun x hx hxd hxl => ?_⟩
  rw [sidePt_zero, hcur] at hx
  rw [sideLeft_zero, hprev, hcur, hnext] at hxl
  -- the middle passage through the top vertex
  have hmid : C.sideIdx β i = C.topIdx → x ∈ C.slit → False := by
    intro hkT hxs
    obtain ⟨hT0, hTm⟩ := C.sideTour_top_inner β hi0 hi hkT
    obtain ⟨hp, hn⟩ := C.sideTour_top_mid β hi0 hi hT0 hTm hkT
    rw [hp, hn, hkT] at hxl
    exact sideLeftOf_not_seg (C.sideTop_mid_slit hP hβ hT0 hTm) hxs hxl
  rcases C.sideTour_corner β hi0 hi with ⟨h0, hm, hp, hn⟩ | ⟨h0, hm, hp, hn⟩ | ⟨h0, hp, hn⟩ |
      ⟨h0, hp, hn⟩
  · rcases hloc x hx hxd with ⟨-, hxs⟩ | ⟨-, hxs⟩ | ⟨hkT, hxs⟩
    · rw [show C.sideIdx β (i - 1) = C.sideIdx β i - 1 by omega] at hxl
      exact sideLeftOf_not_seg_prev (C.sideVertex_pred_ne hP (by omega)) hxs hxl
    · rw [hn] at hxl
      exact sideLeftOf_not_seg_next (C.sideVertex_succ_ne hP _).symm hxs hxl
    · exact hmid hkT hxs
  · rcases hloc x hx hxd with ⟨-, hxs⟩ | ⟨-, hxs⟩ | ⟨hkT, hxs⟩
    · rw [show C.sideIdx β (i + 1) = C.sideIdx β i - 1 by omega] at hxl
      rw [segment_comm] at hxs
      exact sideLeftOf_not_seg_next (C.sideVertex_pred_ne hP (by omega)) hxs hxl
    · rw [hp] at hxl
      rw [segment_comm] at hxs
      exact sideLeftOf_not_seg_prev (C.sideVertex_succ_ne hP _).symm hxs hxl
    · exact hmid hkT hxs
  · rcases hloc x hx hxd with ⟨h1, -⟩ | ⟨-, hxs⟩ | ⟨hkT, hxs⟩
    · omega
    · rw [hn, h0] at hxl
      rw [h0] at hxs
      exact sideLeftOf_not_seg_next (C.sideVertex_succ_ne hP 0).symm hxs hxl
    · exact hmid hkT hxs
  · rcases hloc x hx hxd with ⟨-, hxs⟩ | ⟨h1, -⟩ | ⟨hkT, hxs⟩
    · rw [show C.sideIdx β (i - 1) = C.sideIdx β i - 1 by omega] at hxl
      exact sideLeftOf_not_seg_prev (C.sideVertex_pred_ne hP (by omega)) hxs hxl
    · omega
    · exact hmid hkT hxs

/-- **Cleanness at the first corner of the top vertex** (down the slit, then along the chain). -/
theorem sideClean_top_first (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) :
    SideClean (C.sideWalk β) C.dom (0 + 6) 0 := by
  have hm := C.one_le
  have hprev : (C.sideWalk β).vtx ((0 + 6 + (C.sideWalk β).n - 1) % (C.sideWalk β).n) =
      C.slitTop := by rwr [C.sideWalk_prev_six β]
  have hcur : (C.sideWalk β).vtx (0 + 6) = C.top := by
    rw [C.sideWalk_vtx_tour β (by omega), sideTour_zero]
  have hnext : (C.sideWalk β).vtx ((0 + 6 + 1) % (C.sideWalk β).n) = C.sideTour β 1 := by
    rw [C.sideWalk_next_tour β (by omega), C.sideWalk_vtx_tour β (by omega)]
  obtain ⟨r, hr, hloc⟩ := C.sideLocal_vertex hP C.topIdx_le
  refine ⟨r, hr, fun x hx hxd hxl => ?_⟩
  rw [sidePt_zero, hcur] at hx
  rw [sideLeft_zero, hprev, hcur, hnext] at hxl
  obtain ⟨hn1, hn2, hn3, -, -⟩ := C.sideTour_nbrs β
  have hle1 := C.sideIdx_le β 1
  have hle2 := C.sideIdx_le β (2 * C.m - 1)
  -- a chain neighbour `w` of the top vertex is not in the left sector
  have hnb : ∀ w, w + 1 = C.topIdx ∨ w = C.topIdx + 1 → w ≤ C.m →
      w = C.sideIdx β 1 ∨ w = C.sideIdx β (2 * C.m - 1) →
      ∀ y ∈ Chazelle.segment C.top (C.vertex w), ¬ sideLeftOf C.slitTop C.top (C.sideTour β 1) y := by
    intro w hw hwm hw' y hy
    by_cases h1 : w = C.sideIdx β 1
    · subst h1
      exact sideLeftOf_not_seg_next (C.sideTour_one_ne_top hP β) hy
    · have h2 : w = C.sideIdx β (2 * C.m - 1) := hw'.resolve_left h1
      have hT0 : 0 < C.topIdx := by
        rcases hn3 with h | h <;> omega
      have hTm : C.topIdx < C.m := by
        rcases hn3 with h | h <;> omega
      rw [h2] at hy
      exact sideLeftOf_not_seg (C.sideTop_first_other hP hβ hT0 hTm) hy
  rcases hloc x hx hxd with ⟨h1, hxs⟩ | ⟨h1, hxs⟩ | ⟨-, hxs⟩
  · rw [segment_comm] at hxs
    exact hnb _ (Or.inl (by omega)) (by omega) (hn1 h1) x hxs hxl
  · exact hnb _ (Or.inr rfl) (by omega) (hn2 h1) x hxs hxl
  · have : x ∈ Chazelle.segment C.slitTop C.top := by rwx [segment_comm]
    exact sideLeftOf_not_seg_prev C.sideSlitTop_ne_top this hxl

/-- **Cleanness at the last corner of the top vertex** (along the chain, then up the slit). -/
theorem sideClean_top_last (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) :
    SideClean (C.sideWalk β) C.dom (2 * C.m + 6) 0 := by
  have hm := C.one_le
  have hprev : (C.sideWalk β).vtx ((2 * C.m + 6 + (C.sideWalk β).n - 1) % (C.sideWalk β).n) =
      C.sideTour β (2 * C.m - 1) := by
    rw [C.sideWalk_prev_tour β (by omega) le_rfl, C.sideWalk_vtx_tour β (by omega)]
  have hcur : (C.sideWalk β).vtx (2 * C.m + 6) = C.top := by
    rw [C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
  have hnext : (C.sideWalk β).vtx ((2 * C.m + 6 + 1) % (C.sideWalk β).n) = C.slitTop := by
    rwr [C.sideWalk_next_last β]
  obtain ⟨r, hr, hloc⟩ := C.sideLocal_vertex hP C.topIdx_le
  refine ⟨r, hr, fun x hx hxd hxl => ?_⟩
  rw [sidePt_zero, hcur] at hx
  rw [sideLeft_zero, hprev, hcur, hnext] at hxl
  obtain ⟨hn1, hn2, -, hn4, -⟩ := C.sideTour_nbrs β
  have hle1 := C.sideIdx_le β 1
  have hle2 := C.sideIdx_le β (2 * C.m - 1)
  have hnb : ∀ w, w + 1 = C.topIdx ∨ w = C.topIdx + 1 → w ≤ C.m →
      w = C.sideIdx β 1 ∨ w = C.sideIdx β (2 * C.m - 1) →
      ∀ y ∈ Chazelle.segment (C.vertex w) C.top,
        ¬ sideLeftOf (C.sideTour β (2 * C.m - 1)) C.top C.slitTop y := by
    intro w hw hwm hw' y hy
    by_cases h2 : w = C.sideIdx β (2 * C.m - 1)
    · subst h2
      exact sideLeftOf_not_seg_prev (C.sideTour_last_ne_top hP β) hy
    · have h1 : w = C.sideIdx β 1 := hw'.resolve_right h2
      have hT0 : 0 < C.topIdx := by
        rcases hn4 with h | h <;> omega
      have hTm : C.topIdx < C.m := by
        rcases hn4 with h | h <;> omega
      rw [h1, segment_comm] at hy
      exact sideLeftOf_not_seg (C.sideTop_last_other hP hβ hT0 hTm) hy
  rcases hloc x hx hxd with ⟨h1, hxs⟩ | ⟨h1, hxs⟩ | ⟨-, hxs⟩
  · exact hnb _ (Or.inl (by omega)) (by omega) (hn1 h1) x hxs hxl
  · rw [segment_comm] at hxs
    exact hnb _ (Or.inr rfl) (by omega) (hn2 h1) x hxs hxl
  · exact sideLeftOf_not_seg_next C.sideSlitTop_ne_top hxs hxl

/-- **Cleanness inside an edge of the tour.** -/
theorem sideClean_tour_edge (hP : C.P.Simple) (β : Bool) {i : ℕ} (hi : i < 2 * C.m) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : SideClean (C.sideWalk β) C.dom (i + 6) t := by
  have hcur : (C.sideWalk β).vtx (i + 6) = C.vertex (C.sideIdx β i) :=
    C.sideWalk_vtx_tour β hi.le
  have hnext : (C.sideWalk β).vtx ((i + 6 + 1) % (C.sideWalk β).n) =
      C.vertex (C.sideIdx β (i + 1)) := by
    rwr [C.sideWalk_next_tour β hi, C.sideWalk_vtx_tour β (by omega)]
  have hle := C.sideIdx_le β (i + 1)
  have hle' := C.sideIdx_le β i
  rcases C.sideTour_step β i with h | h
  · have hne : (C.sideWalk β).vtx (i + 6) ≠ (C.sideWalk β).vtx ((i + 6 + 1) % (C.sideWalk β).n) := by
      rw [hcur, hnext, h]; exact C.sideVertex_succ_ne hP _
    obtain ⟨r, hr, hloc⟩ := C.sideLocal_open hP (k := C.sideIdx β i) (by omega) ht
    refine ⟨r, hr, fun x hx hxd hxl => ?_⟩
    rw [sideLeft_edge hne ht, hcur, hnext, h] at hxl
    unfold sidePt at hx
    rw [hcur, hnext, h] at hx
    rw [Geometry.det_eq_zero_of_mem_segment (hloc x hx hxd)] at hxl
    exact lt_irrefl _ hxl
  · have hne : (C.sideWalk β).vtx (i + 6) ≠ (C.sideWalk β).vtx ((i + 6 + 1) % (C.sideWalk β).n) := by
      rw [hcur, hnext, ← h]; exact (C.sideVertex_succ_ne hP _).symm
    have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨r, hr, hloc⟩ := C.sideLocal_open hP (k := C.sideIdx β (i + 1)) (by omega) ht'
    refine ⟨r, hr, fun x hx hxd hxl => ?_⟩
    rw [sideLeft_edge hne ht, hcur, hnext, ← h] at hxl
    unfold sidePt at hx
    rw [hcur, hnext, ← h] at hx
    have e : lerp (C.vertex (C.sideIdx β (i + 1) + 1)) (C.vertex (C.sideIdx β (i + 1))) t =
        lerp (C.vertex (C.sideIdx β (i + 1))) (C.vertex (C.sideIdx β (i + 1) + 1)) (1 - t) := by
      apply point_ext <;> simp [lerp] <;> ring
    rw [e] at hx
    have hxs := hloc x hx hxd
    rw [segment_comm] at hxs
    rw [Geometry.det_eq_zero_of_mem_segment hxs] at hxl
    exact lt_irrefl _ hxl

/-! ### Cleanness of the box block of the corrected walk -/

theorem sideClean_box {W : Polygon} {p : ℕ} {t : ℝ} (hset : sidePt W p t ∉ C.set) {r : ℝ}
    (hr : 0 < r)
    (h : ∀ x ∈ ball (sidePt W p t) r, sideLeft W p t x → x ∈ box C.radius ∧ x ∉ C.slit) :
    SideClean W C.dom p t := by
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 C.isClosed_set.isOpen_compl _ hset
  refine ⟨min r r₁, lt_min hr hr₁, fun x hx hxd hxl => ?_⟩
  have hx1 : x ∈ ball (sidePt W p t) r := ball_subset_ball (min_le_left _ _) hx
  have hx2 : x ∉ C.set := hb₁ (ball_subset_ball (min_le_right _ _) hx)
  obtain ⟨hb, hs⟩ := h x hx1 hxl
  exact hxd (C.mem_dom_iff.2 ⟨hb, hx2, hs⟩)

theorem sideNot_mem_set_of_abs {q : Point} (h : C.radius ≤ |q.1| ∨ C.radius ≤ |q.2|) :
    q ∉ C.set := by
  intro hq
  have h1 := C.abs_le_coordBound_of_mem_set hq
  have h2 := C.coordBound_lt_radius
  rcases h with h | h <;> linarith [h1.1, h1.2]

theorem sideNot_mem_set_of_high {q : Point} (h : C.top.2 < q.2) : q ∉ C.set := fun hq =>
  absurd (C.snd_le_top_of_mem_set hq) (not_le.2 h)

theorem sideNot_mem_slit_of_fst {x : Point} (h : x.1 ≠ C.top.1) : x ∉ C.slit := fun hs =>
  h (C.mem_slit_iff.1 hs).1

theorem sideNot_mem_slit_of_low {x : Point} (h : x.2 < C.top.2) : x ∉ C.slit := fun hs =>
  absurd (C.mem_slit_iff.1 hs).2.1 (not_le.2 h)

theorem sideWalk_mod_small (β : Bool) {p : ℕ} (hp : p < 2 * C.m + 7) :
    p % (C.sideWalk β).n = p := by rw [sideWalk_n]; exact Nat.mod_eq_of_lt hp

theorem sideWalk_prev_zero (β : Bool) :
    (C.sideWalk β).vtx ((0 + (C.sideWalk β).n - 1) % (C.sideWalk β).n) = C.top := by
  rw [sideWalk_n, show 0 + (2 * C.m + 7) - 1 = 2 * C.m + 6 by omega,
    Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]

theorem sideWalk_prev_small (β : Bool) {p : ℕ} (hp1 : 1 ≤ p) (hp : p ≤ 5) :
    (p + (C.sideWalk β).n - 1) % (C.sideWalk β).n = p - 1 := by
  rw [sideWalk_n, show p + (2 * C.m + 7) - 1 = (p - 1) + (2 * C.m + 7) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem sideWalk_vtx_six (β : Bool) : (C.sideWalk β).vtx 6 = C.top := by
  have := C.sideWalk_vtx_tour β (i := 0) (by omega); rwa [zero_add, sideTour_zero] at this

/-- **Cleanness of the box block**: the corners of the box and the two corners at the top of the
slit. -/
theorem sideClean_box_vertex (β : Bool) {p : ℕ} (hp : p ≤ 5) :
    SideClean (C.sideWalk β) C.dom p 0 := by
  have hR := C.radius_pos
  have ht := abs_lt.1 C.abs_top_fst_lt_radius
  have htop := C.top_snd_lt_radius
  have hr : 0 < C.radius - |C.top.1| := by have := C.abs_top_fst_lt_radius; linarith
  have hta := abs_le.1 (le_refl |C.top.1|)
  have hnext : ((p + 1) % (C.sideWalk β).n) = p + 1 := C.sideWalk_mod_small β (by omega)
  interval_cases p
  · -- the top of the slit, from the slit to the top side
    have hset : sidePt (C.sideWalk β) 0 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_zero]
      apply C.sideNot_mem_set_of_abs; right
      simp only [slitTop]; rw [abs_of_pos hR]
    refine C.sideClean_box hset hr ?_
    intro x hx hxl
    rw [sidePt_zero, C.sideWalk_vtx_zero, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_zero, C.sideWalk_vtx_zero, hnext] at hxl
    change sideLeftOf C.top C.slitTop (-C.radius, C.radius) x at hxl
    have hdet : 0 < det C.top C.slitTop (-C.radius, C.radius) := by
      sinl only [det, slitTop]
    rw [sideLeftOf_iff_pos hdet] at hxl
    obtain ⟨h1, h2⟩ := hxl
    simp only [det, slitTop, one_mul] at h1 h2 hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [abs_lt] at hx1 hx2
    have e1 : x.1 < C.top.1 := by nlinarith
    have e2 : x.2 < C.radius := by nlinarith
    exact ⟨⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, e2⟩⟩,
      C.sideNot_mem_slit_of_fst (ne_of_lt e1)⟩
  · have hset : sidePt (C.sideWalk β) 1 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_one]
      apply C.sideNot_mem_set_of_abs; right
      simp only; rw [abs_of_pos hR]
    refine C.sideClean_box hset hr ?_
    intro x hx hxl
    rw [sidePt_zero, C.sideWalk_vtx_one, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β le_rfl (by norm_num), C.sideWalk_vtx_one,
      hnext] at hxl
    change sideLeftOf C.slitTop (-C.radius, C.radius) (-C.radius, -C.radius) x at hxl
    have hdet : 0 < det C.slitTop (-C.radius, C.radius) (-C.radius, -C.radius) := by
      sinl only [det, slitTop]
    rw [sideLeftOf_iff_pos hdet] at hxl
    obtain ⟨h1, h2⟩ := hxl
    simp only [det, slitTop, one_mul] at h1 h2 hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [abs_lt] at hx1 hx2
    have e1 : x.2 < C.radius := by nlinarith
    have e2 : -C.radius < x.1 := by nlinarith
    exact ⟨⟨abs_lt.2 ⟨e2, by linarith⟩, abs_lt.2 ⟨by linarith, e1⟩⟩,
      C.sideNot_mem_slit_of_fst (by linarith)⟩
  · have hset : sidePt (C.sideWalk β) 2 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_two]
      apply C.sideNot_mem_set_of_abs; right
      simp only; rw [abs_neg, abs_of_pos hR]
    refine C.sideClean_box hset hr ?_
    intro x hx hxl
    rw [sidePt_zero, C.sideWalk_vtx_two, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β (by norm_num) (by norm_num), C.sideWalk_vtx_two,
      hnext] at hxl
    change sideLeftOf (-C.radius, C.radius) (-C.radius, -C.radius) (C.radius, -C.radius) x at hxl
    have hdet : 0 < det (-C.radius, C.radius) (-C.radius, -C.radius) (C.radius, -C.radius) := by
      sinl only [det]
    rw [sideLeftOf_iff_pos hdet] at hxl
    obtain ⟨h1, h2⟩ := hxl
    simp only [det, one_mul] at h1 h2 hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [abs_lt] at hx1 hx2
    have e1 : -C.radius < x.1 := by nlinarith
    have e2 : -C.radius < x.2 := by nlinarith
    exact ⟨⟨abs_lt.2 ⟨e1, by linarith⟩, abs_lt.2 ⟨e2, by linarith⟩⟩,
      C.sideNot_mem_slit_of_fst (by linarith)⟩
  · have hset : sidePt (C.sideWalk β) 3 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_three]
      apply C.sideNot_mem_set_of_abs; right
      simp only; rw [abs_neg, abs_of_pos hR]
    refine C.sideClean_box hset hr ?_
    intro x hx hxl
    rw [sidePt_zero, C.sideWalk_vtx_three, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β (by norm_num) (by norm_num), C.sideWalk_vtx_three,
      hnext] at hxl
    change sideLeftOf (-C.radius, -C.radius) (C.radius, -C.radius) (C.radius, C.radius) x at hxl
    have hdet : 0 < det (-C.radius, -C.radius) (C.radius, -C.radius) (C.radius, C.radius) := by
      sinl only [det]
    rw [sideLeftOf_iff_pos hdet] at hxl
    obtain ⟨h1, h2⟩ := hxl
    simp only [det, one_mul] at h1 h2 hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [abs_lt] at hx1 hx2
    have e1 : x.1 < C.radius := by nlinarith
    have e2 : -C.radius < x.2 := by nlinarith
    exact ⟨⟨abs_lt.2 ⟨by linarith, e1⟩, abs_lt.2 ⟨e2, by linarith⟩⟩,
      C.sideNot_mem_slit_of_fst (by linarith)⟩
  · have hset : sidePt (C.sideWalk β) 4 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_four]
      apply C.sideNot_mem_set_of_abs; right
      simp only; rw [abs_of_pos hR]
    refine C.sideClean_box hset hr ?_
    intro x hx hxl
    rw [sidePt_zero, C.sideWalk_vtx_four, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β (by norm_num) (by norm_num), C.sideWalk_vtx_four,
      hnext] at hxl
    change sideLeftOf (C.radius, -C.radius) (C.radius, C.radius) C.slitTop x at hxl
    have hdet : 0 < det (C.radius, -C.radius) (C.radius, C.radius) C.slitTop := by
      sinl only [det, slitTop]
    rw [sideLeftOf_iff_pos hdet] at hxl
    obtain ⟨h1, h2⟩ := hxl
    simp only [det, slitTop, one_mul] at h1 h2 hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [abs_lt] at hx1 hx2
    have e1 : x.1 < C.radius := by nlinarith
    have e2 : x.2 < C.radius := by nlinarith
    exact ⟨⟨abs_lt.2 ⟨by linarith, e1⟩, abs_lt.2 ⟨by linarith, e2⟩⟩,
      C.sideNot_mem_slit_of_fst (by linarith)⟩
  · have hset : sidePt (C.sideWalk β) 5 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_five]
      apply C.sideNot_mem_set_of_abs; right
      simp only [slitTop]; rw [abs_of_pos hR]
    refine C.sideClean_box hset hr ?_
    intro x hx hxl
    rw [sidePt_zero, C.sideWalk_vtx_five, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β (by norm_num) (by norm_num), C.sideWalk_vtx_five,
      hnext, C.sideWalk_vtx_six] at hxl
    change sideLeftOf (C.radius, C.radius) C.slitTop C.top x at hxl
    have hdet : 0 < det (C.radius, C.radius) C.slitTop C.top := by
      sinl only [det, slitTop]
    rw [sideLeftOf_iff_pos hdet] at hxl
    obtain ⟨h1, h2⟩ := hxl
    simp only [det, slitTop, one_mul] at h1 h2 hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [abs_lt] at hx1 hx2
    have e1 : x.2 < C.radius := by nlinarith
    have e2 : C.top.1 < x.1 := by nlinarith
    exact ⟨⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, e1⟩⟩,
      C.sideNot_mem_slit_of_fst (ne_of_gt e2)⟩

theorem sideClean_box_edge_aux {W : Polygon} {p : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hne : W.vtx p ≠ W.vtx ((p + 1) % W.n)) (hset : sidePt W p t ∉ C.set) {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ ball (sidePt W p t) r, 0 < det (W.vtx p) (W.vtx ((p + 1) % W.n)) x →
      x ∈ box C.radius ∧ x ∉ C.slit) :
    SideClean W C.dom p t :=
  C.sideClean_box hset hr (fun x hx hxl => h x hx ((sideLeft_edge hne ht x).1 hxl))

/-- Cleanness inside the closing edge (up the slit). -/
theorem sideClean_slit_up (β : Bool) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    SideClean (C.sideWalk β) C.dom (2 * C.m + 6) t := by
  have hR := C.radius_pos
  have hta := abs_lt.1 C.abs_top_fst_lt_radius
  have htop := C.top_snd_lt_radius
  have htb := abs_le.1 (C.abs_le_coordBound_of_mem_set C.top_mem_set).2
  have hcR := C.coordBound_lt_radius
  obtain ⟨ht0, ht1⟩ := ht
  have hcur : (C.sideWalk β).vtx (2 * C.m + 6) = C.top := by
    rw [C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
  have hnext : (C.sideWalk β).vtx ((2 * C.m + 6 + 1) % (C.sideWalk β).n) = C.slitTop := by
    rwr [C.sideWalk_next_last β]
  have hne : (C.sideWalk β).vtx (2 * C.m + 6) ≠
      (C.sideWalk β).vtx ((2 * C.m + 6 + 1) % (C.sideWalk β).n) := by
    rw [hcur, hnext]; exact C.sideSlitTop_ne_top.symm
  have hq : sidePt (C.sideWalk β) (2 * C.m + 6) t =
      (C.top.1, C.top.2 + t * (C.radius - C.top.2)) := by
    unfold sidePt; rw [hcur, hnext]
    apply point_ext <;> simp [lerp, slitTop]
  have hpos : 0 < t * (C.radius - C.top.2) := mul_pos ht0 (by linarith)
  have hpos' : 0 < (1 - t) * (C.radius - C.top.2) := mul_pos (by linarith) (by linarith)
  have hset : sidePt (C.sideWalk β) (2 * C.m + 6) t ∉ C.set := by
    rw [hq]; apply C.sideNot_mem_set_of_high; show C.top.2 < C.top.2 + t * (C.radius - C.top.2)
    linarith
  have hr : 0 < min (min (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2)))
      (C.top.1 + C.radius) :=
    lt_min (lt_min hpos hpos') (by linarith)
  refine C.sideClean_box_edge_aux ⟨ht0, ht1⟩ hne hset hr (fun x hx hxl => ?_)
  rw [hq, mem_ball_iff_abs] at hx
  rw [hcur, hnext] at hxl
  simp only [det, slitTop] at hxl hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [abs_lt] at hx1 hx2
  have hm1 := min_le_left (min (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2)))
    (C.top.1 + C.radius)
  have hm2 := min_le_right (min (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2)))
    (C.top.1 + C.radius)
  have hm3 := min_le_left (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2))
  have hm4 := min_le_right (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2))
  have e1 : x.1 < C.top.1 := by nlinarith
  exact ⟨⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩,
    C.sideNot_mem_slit_of_fst (ne_of_lt e1)⟩

/-- **Cleanness inside the edges of the box block** (the sides of the box and the slit). -/
theorem sideClean_box_edge (β : Bool) {p : ℕ} (hp : p ≤ 5 ∨ p = 2 * C.m + 6) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : SideClean (C.sideWalk β) C.dom p t := by
  have hR := C.radius_pos
  have hta := abs_lt.1 C.abs_top_fst_lt_radius
  have htop := C.top_snd_lt_radius
  have htb := abs_le.1 (C.abs_le_coordBound_of_mem_set C.top_mem_set).2
  have hcR := C.coordBound_lt_radius
  obtain ⟨ht0, ht1⟩ := ht
  rcases hp with hp | hp
  · have hnext : ((p + 1) % (C.sideWalk β).n) = p + 1 := C.sideWalk_mod_small β (by omega)
    interval_cases p
    · -- the top side, west of the slit
      have hne : (C.sideWalk β).vtx 0 ≠ (C.sideWalk β).vtx ((0 + 1) % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_zero]
        intro h; have := congrArg Prod.fst h; simp only [slitTop] at this
        change C.top.1 = -C.radius at this; linarith
      have hq : sidePt (C.sideWalk β) 0 t = (C.top.1 + t * (-C.radius - C.top.1), C.radius) := by
        have e1  := C.sideWalk_vtx_one β
        unfold sidePt; rw [hnext, C.sideWalk_vtx_zero, e1]
        apply point_ext <;> simp [lerp, slitTop]
      have hset : sidePt (C.sideWalk β) 0 t ∉ C.set := by
        rw [hq]; apply C.sideNot_mem_set_of_abs; right; simp only; rw [abs_of_pos hR]
      have hr : 0 < min (t * (C.radius + C.top.1)) ((1 - t) * (C.radius + C.top.1)) :=
        lt_min (by nlinarith) (by nlinarith)
      refine C.sideClean_box_edge_aux ⟨ht0, ht1⟩ hne hset hr (fun x hx hxl => ?_)
      rw [hq, mem_ball_iff_abs] at hx
      rw [hnext, C.sideWalk_vtx_zero] at hxl
      change 0 < det C.slitTop (-C.radius, C.radius) x at hxl
      simp only [det, slitTop] at hxl hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [abs_lt] at hx1 hx2
      have hm1 := min_le_left (t * (C.radius + C.top.1)) ((1 - t) * (C.radius + C.top.1))
      have hm2 := min_le_right (t * (C.radius + C.top.1)) ((1 - t) * (C.radius + C.top.1))
      have e1 : x.2 < C.radius := by nlinarith
      exact ⟨⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, abs_lt.2 ⟨by nlinarith, e1⟩⟩,
        C.sideNot_mem_slit_of_fst (by nlinarith)⟩
    · -- the left side
      have hne : (C.sideWalk β).vtx 1 ≠ (C.sideWalk β).vtx ((1 + 1) % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_one]
        intro h; have := congrArg Prod.snd h
        change C.radius = -C.radius at this; linarith
      have hq : sidePt (C.sideWalk β) 1 t = (-C.radius, C.radius - 2 * t * C.radius) := by
        have e2  := C.sideWalk_vtx_two β
        unfold sidePt; rw [hnext, C.sideWalk_vtx_one, e2]
        apply point_ext <;> simp [lerp]
        ring
      have hset : sidePt (C.sideWalk β) 1 t ∉ C.set := by
        rw [hq]; apply C.sideNot_mem_set_of_abs; left; simp only; rw [abs_neg, abs_of_pos hR]
      have hr : 0 < min (min (2 * t * C.radius) (2 * (1 - t) * C.radius)) (C.top.1 + C.radius) :=
        lt_min (lt_min (by nlinarith) (by nlinarith)) (by linarith)
      refine C.sideClean_box_edge_aux ⟨ht0, ht1⟩ hne hset hr (fun x hx hxl => ?_)
      rw [hq, mem_ball_iff_abs] at hx
      rw [hnext, C.sideWalk_vtx_one] at hxl
      change 0 < det (-C.radius, C.radius) (C.sideWalk β |>.vtx 2) x at hxl
      rw [C.sideWalk_vtx_two] at hxl
      simp only [det] at hxl hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [abs_lt] at hx1 hx2
      have hm1 := min_le_left (min (2 * t * C.radius) (2 * (1 - t) * C.radius)) (C.top.1 + C.radius)
      have hm2 := min_le_right (min (2 * t * C.radius) (2 * (1 - t) * C.radius)) (C.top.1 + C.radius)
      have hm3 := min_le_left (2 * t * C.radius) (2 * (1 - t) * C.radius)
      have hm4 := min_le_right (2 * t * C.radius) (2 * (1 - t) * C.radius)
      have e1 : -C.radius < x.1 := by nlinarith
      exact ⟨⟨abs_lt.2 ⟨e1, by nlinarith⟩, abs_lt.2 ⟨by nlinarith, by nlinarith⟩⟩,
        C.sideNot_mem_slit_of_fst (by nlinarith)⟩
    · -- the bottom side
      have hne : (C.sideWalk β).vtx 2 ≠ (C.sideWalk β).vtx ((2 + 1) % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_two]
        intro h; have := congrArg Prod.fst h
        change -C.radius = (C.sideWalk β |>.vtx 3).1 at this
        rw [C.sideWalk_vtx_three] at this; sil only at this
      have hq : sidePt (C.sideWalk β) 2 t = (-C.radius + 2 * t * C.radius, -C.radius) := by
        unfold sidePt; rw [hnext, C.sideWalk_vtx_two, C.sideWalk_vtx_three]
        apply point_ext <;> simp [lerp]
        ring
      have hset : sidePt (C.sideWalk β) 2 t ∉ C.set := by
        rw [hq]; apply C.sideNot_mem_set_of_abs; right; simp only; rw [abs_neg, abs_of_pos hR]
      have hr : 0 < min (min (2 * t * C.radius) (2 * (1 - t) * C.radius)) (C.top.2 + C.radius) :=
        lt_min (lt_min (by nlinarith) (by nlinarith)) (by linarith)
      refine C.sideClean_box_edge_aux ⟨ht0, ht1⟩ hne hset hr (fun x hx hxl => ?_)
      rw [hq, mem_ball_iff_abs] at hx
      rw [hnext, C.sideWalk_vtx_two, C.sideWalk_vtx_three] at hxl
      simp only [det] at hxl hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [abs_lt] at hx1 hx2
      have hm1 := min_le_left (min (2 * t * C.radius) (2 * (1 - t) * C.radius)) (C.top.2 + C.radius)
      have hm2 := min_le_right (min (2 * t * C.radius) (2 * (1 - t) * C.radius)) (C.top.2 + C.radius)
      have hm3 := min_le_left (2 * t * C.radius) (2 * (1 - t) * C.radius)
      have hm4 := min_le_right (2 * t * C.radius) (2 * (1 - t) * C.radius)
      have e1 : -C.radius < x.2 := by nlinarith
      exact ⟨⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, abs_lt.2 ⟨e1, by nlinarith⟩⟩,
        C.sideNot_mem_slit_of_low (by nlinarith)⟩
    · -- the right side
      have hne : (C.sideWalk β).vtx 3 ≠ (C.sideWalk β).vtx ((3 + 1) % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_three, C.sideWalk_vtx_four]
        intro h; have := congrArg Prod.snd h; sil only at this
      have hq : sidePt (C.sideWalk β) 3 t = (C.radius, -C.radius + 2 * t * C.radius) := by
        unfold sidePt; rw [hnext, C.sideWalk_vtx_three, C.sideWalk_vtx_four]
        apply point_ext <;> simp [lerp]
        ring
      have hset : sidePt (C.sideWalk β) 3 t ∉ C.set := by
        rw [hq]; apply C.sideNot_mem_set_of_abs; left; simp only; rw [abs_of_pos hR]
      have hr : 0 < min (min (2 * t * C.radius) (2 * (1 - t) * C.radius)) (C.radius - C.top.1) :=
        lt_min (lt_min (by nlinarith) (by nlinarith)) (by linarith)
      refine C.sideClean_box_edge_aux ⟨ht0, ht1⟩ hne hset hr (fun x hx hxl => ?_)
      rw [hq, mem_ball_iff_abs] at hx
      rw [hnext, C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hxl
      simp only [det] at hxl hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [abs_lt] at hx1 hx2
      have hm1 := min_le_left (min (2 * t * C.radius) (2 * (1 - t) * C.radius)) (C.radius - C.top.1)
      have hm2 := min_le_right (min (2 * t * C.radius) (2 * (1 - t) * C.radius)) (C.radius - C.top.1)
      have hm3 := min_le_left (2 * t * C.radius) (2 * (1 - t) * C.radius)
      have hm4 := min_le_right (2 * t * C.radius) (2 * (1 - t) * C.radius)
      have e1 : x.1 < C.radius := by nlinarith
      exact ⟨⟨abs_lt.2 ⟨by nlinarith, e1⟩, abs_lt.2 ⟨by nlinarith, by nlinarith⟩⟩,
        C.sideNot_mem_slit_of_fst (by nlinarith)⟩
    · -- the top side, east of the slit
      have hne : (C.sideWalk β).vtx 4 ≠ (C.sideWalk β).vtx ((4 + 1) % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_four, C.sideWalk_vtx_five]
        intro h; have := congrArg Prod.fst h; sil only [slitTop] at this
      have hq : sidePt (C.sideWalk β) 4 t = (C.radius + t * (C.top.1 - C.radius), C.radius) := by
        unfold sidePt; rw [hnext, C.sideWalk_vtx_four, C.sideWalk_vtx_five]
        apply point_ext <;> simp [lerp, slitTop]
      have hset : sidePt (C.sideWalk β) 4 t ∉ C.set := by
        rw [hq]; apply C.sideNot_mem_set_of_abs; right; simp only; rw [abs_of_pos hR]
      have hr : 0 < min (t * (C.radius - C.top.1)) ((1 - t) * (C.radius - C.top.1)) :=
        lt_min (by nlinarith) (by nlinarith)
      refine C.sideClean_box_edge_aux ⟨ht0, ht1⟩ hne hset hr (fun x hx hxl => ?_)
      rw [hq, mem_ball_iff_abs] at hx
      rw [hnext, C.sideWalk_vtx_four, C.sideWalk_vtx_five] at hxl
      simp only [det, slitTop] at hxl hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [abs_lt] at hx1 hx2
      have hm1 := min_le_left (t * (C.radius - C.top.1)) ((1 - t) * (C.radius - C.top.1))
      have hm2 := min_le_right (t * (C.radius - C.top.1)) ((1 - t) * (C.radius - C.top.1))
      have e1 : x.2 < C.radius := by nlinarith
      exact ⟨⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, abs_lt.2 ⟨by nlinarith, e1⟩⟩,
        C.sideNot_mem_slit_of_fst (by nlinarith)⟩
    · -- down the slit
      have hne : (C.sideWalk β).vtx 5 ≠ (C.sideWalk β).vtx ((5 + 1) % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_five, C.sideWalk_vtx_six]; exact C.sideSlitTop_ne_top
      have hq : sidePt (C.sideWalk β) 5 t = (C.top.1, C.radius + t * (C.top.2 - C.radius)) := by
        unfold sidePt; rw [hnext, C.sideWalk_vtx_five, C.sideWalk_vtx_six]
        apply point_ext <;> simp [lerp, slitTop]
      have hset : sidePt (C.sideWalk β) 5 t ∉ C.set := by
        rw [hq]; apply C.sideNot_mem_set_of_high; sinl only
      have hr : 0 < min (min (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2)))
          (C.radius - C.top.1) :=
        lt_min (lt_min (by nlinarith) (by nlinarith)) (by linarith)
      refine C.sideClean_box_edge_aux ⟨ht0, ht1⟩ hne hset hr (fun x hx hxl => ?_)
      rw [hq, mem_ball_iff_abs] at hx
      rw [hnext, C.sideWalk_vtx_five, C.sideWalk_vtx_six] at hxl
      simp only [det, slitTop] at hxl hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [abs_lt] at hx1 hx2
      have hm1 := min_le_left (min (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2)))
        (C.radius - C.top.1)
      have hm2 := min_le_right (min (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2)))
        (C.radius - C.top.1)
      have hm3 := min_le_left (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2))
      have hm4 := min_le_right (t * (C.radius - C.top.2)) ((1 - t) * (C.radius - C.top.2))
      have e1 : C.top.1 < x.1 := by nlinarith
      exact ⟨⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, abs_lt.2 ⟨by nlinarith, by nlinarith⟩⟩,
        C.sideNot_mem_slit_of_fst (ne_of_gt e1)⟩
  · rw [hp]; exact C.sideClean_slit_up β ⟨ht0, ht1⟩

/-! ### The corrected walk: nondegeneracy, trace and cleanness of every position -/

theorem sideWalk_lt_cases (β : Bool) {p : ℕ} (hp : p < (C.sideWalk β).n) :
    p ≤ 5 ∨ (∃ i, i < 2 * C.m ∧ p = i + 6) ∨ p = 2 * C.m + 6 := by
  rw [sideWalk_n] at hp
  by_cases h5 : p ≤ 5
  · exact Or.inl h5
  · by_cases hl : p = 2 * C.m + 6
    · exact Or.inr (Or.inr hl)
    · exact Or.inr (Or.inl ⟨p - 6, by omega, by omega⟩)

/-- The corrected walk has nondegenerate edges. -/
theorem sideWalk_nd (hP : C.P.Simple) (β : Bool) :
    ∀ p < (C.sideWalk β).n, (C.sideWalk β).vtx p ≠ (C.sideWalk β).vtx ((p + 1) % (C.sideWalk β).n) := by
  intro p hp
  have hR := C.radius_pos
  have hta := abs_lt.1 C.abs_top_fst_lt_radius
  rcases C.sideWalk_lt_cases β hp with h5 | ⟨i, hi, rfl⟩ | rfl
  · have hnext : ((p + 1) % (C.sideWalk β).n) = p + 1 := C.sideWalk_mod_small β (by omega)
    rw [hnext]
    interval_cases p
    · rw [C.sideWalk_vtx_zero, show (0 + 1 : ℕ) = 1 from rfl, C.sideWalk_vtx_one]
      intro h; have := congrArg Prod.fst h; sil only [slitTop] at this
    · rw [C.sideWalk_vtx_one, show (1 + 1 : ℕ) = 2 from rfl, C.sideWalk_vtx_two]
      intro h; have := congrArg Prod.snd h; sil only at this
    · rw [C.sideWalk_vtx_two, show (2 + 1 : ℕ) = 3 from rfl, C.sideWalk_vtx_three]
      intro h; have := congrArg Prod.fst h; sil only at this
    · rw [C.sideWalk_vtx_three, show (3 + 1 : ℕ) = 4 from rfl, C.sideWalk_vtx_four]
      intro h; have := congrArg Prod.snd h; sil only at this
    · rw [C.sideWalk_vtx_four, show (4 + 1 : ℕ) = 5 from rfl, C.sideWalk_vtx_five]
      intro h; have := congrArg Prod.fst h; sil only [slitTop] at this
    · rw [C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 6 from rfl, C.sideWalk_vtx_six]
      exact C.sideSlitTop_ne_top
  · rw [C.sideWalk_next_tour β hi, C.sideWalk_vtx_tour β hi.le, C.sideWalk_vtx_tour β (by omega)]
    unfold sideTour
    rcases C.sideTour_step β i with h | h
    · rw [h]; exact C.sideVertex_succ_ne hP _
    · rw [← h]; exact (C.sideVertex_succ_ne hP _).symm
  · rw [C.sideWalk_next_last β, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m, C.sideWalk_vtx_zero]
    exact C.sideSlitTop_ne_top.symm

theorem sideLerp_mem_set {a b : ℕ} (hab : b = a + 1 ∨ b + 1 = a) (hle : a ≤ C.m) (hle' : b ≤ C.m)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : lerp (C.vertex a) (C.vertex b) t ∈ C.set := by
  rcases hab with rfl | rfl
  · exact ⟨a, by omega, by rw [C.chainEdge_eq]; exact lerp_mem_segment _ _ ht0 ht1⟩
  · refine ⟨b, by omega, ?_⟩
    rw [C.chainEdge_eq, segment_comm]
    exact lerp_mem_segment _ _ ht0 ht1

theorem sideNot_mem_dom_of_abs {x : Point} (h : |x.1| = C.radius ∨ |x.2| = C.radius) :
    x ∉ C.dom := fun hx => by
  have := hx.1
  rcases h with h | h
  · exact absurd this.1 (by rw [h]; exact lt_irrefl _)
  · exact absurd this.2 (by rw [h]; exact lt_irrefl _)

/-- **The corrected walk avoids the domain.** -/
theorem sideWalk_trace (β : Bool) :
    ∀ p < (C.sideWalk β).n, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → sidePt (C.sideWalk β) p t ∉ C.dom := by
  intro p hp t ht0 ht1
  have hR := C.radius_pos
  rcases C.sideWalk_lt_cases β hp with h5 | ⟨i, hi, rfl⟩ | rfl
  · have hnext : ((p + 1) % (C.sideWalk β).n) = p + 1 := C.sideWalk_mod_small β (by omega)
    unfold sidePt
    rw [hnext]
    interval_cases p
    · rw [C.sideWalk_vtx_zero, show (0 + 1 : ℕ) = 1 from rfl, C.sideWalk_vtx_one]
      apply C.sideNot_mem_dom_of_abs; right; simp [lerp, slitTop, abs_of_pos hR]
    · rw [C.sideWalk_vtx_one, show (1 + 1 : ℕ) = 2 from rfl, C.sideWalk_vtx_two]
      apply C.sideNot_mem_dom_of_abs; left; simp [lerp, abs_of_pos hR]
    · rw [C.sideWalk_vtx_two, show (2 + 1 : ℕ) = 3 from rfl, C.sideWalk_vtx_three]
      apply C.sideNot_mem_dom_of_abs; right; simp [lerp, abs_of_pos hR]
    · rw [C.sideWalk_vtx_three, show (3 + 1 : ℕ) = 4 from rfl, C.sideWalk_vtx_four]
      apply C.sideNot_mem_dom_of_abs; left; simp [lerp, abs_of_pos hR]
    · rw [C.sideWalk_vtx_four, show (4 + 1 : ℕ) = 5 from rfl, C.sideWalk_vtx_five]
      apply C.sideNot_mem_dom_of_abs; right; simp [lerp, slitTop, abs_of_pos hR]
    · rw [C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 6 from rfl, C.sideWalk_vtx_six]
      intro hd
      apply C.not_mem_slit_of_mem_dom hd
      rw [slit, segment_comm]; exact lerp_mem_segment _ _ ht0 ht1
  · unfold sidePt
    rw [C.sideWalk_next_tour β hi, C.sideWalk_vtx_tour β hi.le, C.sideWalk_vtx_tour β (by omega)]
    intro hd
    apply C.not_mem_set_of_mem_dom hd
    unfold sideTour
    rcases C.sideTour_step β i with h | h
    · exact C.sideLerp_mem_set (Or.inl h) (C.sideIdx_le β i) (C.sideIdx_le β _) ht0 ht1
    · exact C.sideLerp_mem_set (Or.inr h) (C.sideIdx_le β i) (C.sideIdx_le β _) ht0 ht1
  · unfold sidePt
    rw [C.sideWalk_next_last β, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m, C.sideWalk_vtx_zero]
    intro hd
    apply C.not_mem_slit_of_mem_dom hd
    exact lerp_mem_segment _ _ ht0 ht1

/-- **Every position of the corrected walk is clean for the domain**: near every point of the
walk, no point outside `dom C` lies in the open left sector of the walk there. -/
theorem sideWalk_clean (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) :
    ∀ p < (C.sideWalk β).n, ∀ t : ℝ, 0 ≤ t → t < 1 → SideClean (C.sideWalk β) C.dom p t := by
  intro p hp t ht0 ht1
  rcases ht0.lt_or_eq with htp | htz
  · rcases C.sideWalk_lt_cases β hp with h5 | ⟨i, hi, rfl⟩ | rfl
    · exact C.sideClean_box_edge β (Or.inl h5) ⟨htp, ht1⟩
    · exact C.sideClean_tour_edge hP β hi ⟨htp, ht1⟩
    · exact C.sideClean_slit_up β ⟨htp, ht1⟩
  · subst htz
    rcases C.sideWalk_lt_cases β hp with h5 | ⟨i, hi, rfl⟩ | rfl
    · exact C.sideClean_box_vertex β h5
    · rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; exact C.sideClean_top_first hP hβ
      · exact C.sideClean_tour_vertex hP hβ h0 hi
    · exact C.sideClean_top_last hP hβ

/-! ### Disjointness of the left sectors of distinct positions at a common point -/

/-- Two distinct inner visits of the same chain vertex leave it in opposite directions. -/
theorem sideTour_two_visits (β : Bool) {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m)
    (hne : i ≠ i') (heq : C.sideIdx β i = C.sideIdx β i') :
    (C.sideIdx β (i + 1) = C.sideIdx β i + 1 ∧ C.sideIdx β (i' + 1) + 1 = C.sideIdx β i) ∨
      (C.sideIdx β (i + 1) + 1 = C.sideIdx β i ∧ C.sideIdx β (i' + 1) = C.sideIdx β i + 1) := by
  have hm2 := C.two_m_pos
  have hj : (C.sideS β + i) % (2 * C.m) ≠ (C.sideS β + i') % (2 * C.m) := by
    intro h
    exact hne (Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' (C.sideS β) h) hi hi')
  rw [C.sideIdx_succ, C.sideIdx_succ]
  rw [sideIdx_eq, sideIdx_eq] at heq
  rw [sideIdx_eq]
  have h1 := Nat.mod_lt (C.sideS β + i) hm2
  have h2 := Nat.mod_lt (C.sideS β + i') hm2
  generalize (C.sideS β + i) % (2 * C.m) = j at hj heq h1 ⊢
  generalize (C.sideS β + i') % (2 * C.m) = j' at hj heq h2 ⊢
  unfold sideE at *
  split_ifs at * <;> omega

theorem sideTop_nonSpike_up (k : ℕ) (hk : k ≤ C.m) :
    sideNonSpike (C.vertex k - C.top) (C.slitTop - C.top) := by
  rintro ⟨hc, hd⟩
  have hy := C.vertex_snd_le_top hk
  have htop := C.top_snd_lt_radius
  unfold sideCross sideDot at *
  simp only [Prod.fst_sub, Prod.snd_sub, slitTop, sub_self, mul_zero, sub_zero] at hc hd
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hy) (sub_pos.2 htop).le]

theorem sideTour_one_eq_last (β : Bool) (hT : C.topIdx = 0 ∨ C.topIdx = C.m) :
    C.sideTour β 1 = C.sideTour β (2 * C.m - 1) := by
  obtain ⟨-, -, h3, h4, -⟩ := C.sideTour_nbrs β
  have hle1 := C.sideIdx_le β 1
  have hle2 := C.sideIdx_le β (2 * C.m - 1)
  unfold sideTour
  congr 1
  rcases hT with hT | hT <;> omega

/-- The three corners at the top vertex have pairwise disjoint left sectors. -/
theorem sideTop_disj (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) (x : Point) :
    ¬ (sideLeftOf C.slitTop C.top (C.sideTour β 1) x ∧
        sideLeftOf (C.sideTour β (2 * C.m - 1)) C.top C.slitTop x) ∧
      ((0 < C.topIdx ∧ C.topIdx < C.m) →
        ¬ (sideLeftOf C.slitTop C.top (C.sideTour β 1) x ∧
          sideLeftOf (C.sideTour β 1) C.top (C.sideTour β (2 * C.m - 1)) x)) ∧
      ((0 < C.topIdx ∧ C.topIdx < C.m) →
        ¬ (sideLeftOf (C.sideTour β (2 * C.m - 1)) C.top C.slitTop x ∧
          sideLeftOf (C.sideTour β 1) C.top (C.sideTour β (2 * C.m - 1)) x)) := by
  have hn0  := sub_ne_zero_of_ne' (C.sideTour_one_ne_top hP β)
  have hp0  := sub_ne_zero_of_ne' (C.sideTour_last_ne_top hP β)
  have hU0  := sub_ne_zero_of_ne' C.sideSlitTop_ne_top
  have hnU := C.sideTop_nonSpike_up _ (C.sideIdx_le β 1)
  unfold sideLeftOf
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    by_cases hT : C.topIdx = 0 ∨ C.topIdx = C.m
    · rw [← C.sideTour_one_eq_last β hT] at h2
      exact sideCcw_asymm hn0 hnU h1 h2
    · have hord : sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top)
          (C.sideTour β (2 * C.m - 1) - C.top) := by
        rcases hβ with h | h | h
        · exact absurd (Or.inl h) hT
        · exact absurd (Or.inr h) hT
        · exact h
      have hT' : 0 < C.topIdx ∧ C.topIdx < C.m := by
        have := C.topIdx_le; push Not at hT; omega
      have hns := C.sideTop_nonSpike hP β hT'.1 hT'.2
      have h3 := sideCcw_rotate hn0 hU0 hns hord
      have h4 := sideCcw_sub_left hU0 h3 h2
      exact sideCcw_asymm hn0 hnU h1 h4
  · rintro ⟨hT0, hTm⟩ ⟨h1, h2⟩
    have hord : sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top)
        (C.sideTour β (2 * C.m - 1) - C.top) := by
      rcases hβ with h | h | h
      · omega
      · omega
      · exact h
    have h3 := sideCcw_sub_left hn0 hord h1
    exact sideCcw_asymm hn0 (C.sideTop_nonSpike hP β hT0 hTm) h3 h2
  · rintro ⟨hT0, hTm⟩ ⟨h1, h2⟩
    have hord : sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top)
        (C.sideTour β (2 * C.m - 1) - C.top) := by
      rcases hβ with h | h | h
      · omega
      · omega
      · exact h
    have h3 := sideCcw_sub_right hn0 hU0 hp0 hord h1
    exact sideCcw_asymm hn0 (C.sideTop_nonSpike hP β hT0 hTm) h3 h2

/-- The points of the box block of the walk. -/
theorem sidePt_box (β : Bool) (t : ℝ) :
    sidePt (C.sideWalk β) 0 t = (C.top.1 + t * (-C.radius - C.top.1), C.radius) ∧
    sidePt (C.sideWalk β) 1 t = (-C.radius, C.radius - 2 * t * C.radius) ∧
    sidePt (C.sideWalk β) 2 t = (-C.radius + 2 * t * C.radius, -C.radius) ∧
    sidePt (C.sideWalk β) 3 t = (C.radius, -C.radius + 2 * t * C.radius) ∧
    sidePt (C.sideWalk β) 4 t = (C.radius + t * (C.top.1 - C.radius), C.radius) ∧
    sidePt (C.sideWalk β) 5 t = (C.top.1, C.radius + t * (C.top.2 - C.radius)) ∧
    sidePt (C.sideWalk β) (2 * C.m + 6) t = (C.top.1, C.top.2 + t * (C.radius - C.top.2)) := by
  have hm := C.one_le
  have h1 : ∀ p, p ≤ 5 → (p + 1) % (C.sideWalk β).n = p + 1 := fun p hp =>
    C.sideWalk_mod_small β (by omega)
  unfold sidePt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1 0 (by norm_num), C.sideWalk_vtx_zero, show (0 + 1 : ℕ) = 1 from rfl, C.sideWalk_vtx_one]
    apply point_ext <;> simp [lerp, slitTop]
  · rw [h1 1 (by norm_num), C.sideWalk_vtx_one, show (1 + 1 : ℕ) = 2 from rfl, C.sideWalk_vtx_two]
    apply point_ext <;> simp [lerp]
    ring
  · rw [h1 2 (by norm_num), C.sideWalk_vtx_two, show (2 + 1 : ℕ) = 3 from rfl,
      C.sideWalk_vtx_three]
    apply point_ext <;> simp [lerp]
    ring
  · rw [h1 3 (by norm_num), C.sideWalk_vtx_three, show (3 + 1 : ℕ) = 4 from rfl,
      C.sideWalk_vtx_four]
    apply point_ext <;> simp [lerp]
    ring
  · rw [h1 4 (by norm_num), C.sideWalk_vtx_four, show (4 + 1 : ℕ) = 5 from rfl,
      C.sideWalk_vtx_five]
    apply point_ext <;> simp [lerp, slitTop]
  · rw [h1 5 (by norm_num), C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 6 from rfl,
      C.sideWalk_vtx_six]
    apply point_ext <;> simp [lerp, slitTop]
  · rw [C.sideWalk_next_last β, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m, C.sideWalk_vtx_zero]
    apply point_ext <;> simp [lerp, slitTop]

/-- The points of the box block are off the chain, and those on the open vertical sides of the
box are on the edges `1` or `3`. -/
theorem sideWalk_box_pt (β : Bool) {p : ℕ} {t : ℝ} (hp : p ≤ 5 ∨ (p = 2 * C.m + 6 ∧ 0 < t))
    (ht : 0 ≤ t) (ht1 : t < 1) :
    sidePt (C.sideWalk β) p t ∉ C.set ∧
      (|(sidePt (C.sideWalk β) p t).1| = C.radius → |(sidePt (C.sideWalk β) p t).2| < C.radius →
        ((p = 1 ∧ (sidePt (C.sideWalk β) p t).1 = -C.radius) ∨
          (p = 3 ∧ (sidePt (C.sideWalk β) p t).1 = C.radius)) ∧ 0 < t) := by
  have hR := C.radius_pos
  have hta := abs_lt.1 C.abs_top_fst_lt_radius
  have htop := C.top_snd_lt_radius
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := C.sidePt_box β t
  rcases hp with hp | ⟨rfl, htp⟩
  · interval_cases p
    · rw [e0]
      refine ⟨C.sideNot_mem_set_of_abs (Or.inr (by simp only; rw [abs_of_pos hR])), ?_⟩
      intro _ h; simp only [abs_of_pos hR] at h; exact absurd h (lt_irrefl _)
    · rw [e1]
      refine ⟨C.sideNot_mem_set_of_abs (Or.inl (by simp only; rw [abs_neg, abs_of_pos hR])), ?_⟩
      intro _ h
      refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
      rcases ht.lt_or_eq with h' | h'
      · exact h'
      · subst h'; simp only [mul_zero, zero_mul, sub_zero, abs_of_pos hR] at h
        exact absurd h (lt_irrefl _)
    · rw [e2]
      refine ⟨C.sideNot_mem_set_of_abs (Or.inr (by simp only; rw [abs_neg, abs_of_pos hR])), ?_⟩
      intro _ h; simp only [abs_neg, abs_of_pos hR] at h; exact absurd h (lt_irrefl _)
    · rw [e3]
      refine ⟨C.sideNot_mem_set_of_abs (Or.inl (by simp only; rw [abs_of_pos hR])), ?_⟩
      intro _ h
      refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      rcases ht.lt_or_eq with h' | h'
      · exact h'
      · subst h'; simp only [mul_zero, zero_mul, add_zero, abs_neg, abs_of_pos hR] at h
        exact absurd h (lt_irrefl _)
    · rw [e4]
      refine ⟨C.sideNot_mem_set_of_abs (Or.inr (by simp only; rw [abs_of_pos hR])), ?_⟩
      intro _ h; simp only [abs_of_pos hR] at h; exact absurd h (lt_irrefl _)
    · rw [e5]
      refine ⟨C.sideNot_mem_set_of_high (by sinl only), ?_⟩
      intro h; simp only at h
      exact absurd h (ne_of_lt (abs_lt.2 hta))
  · rw [e6]
    refine ⟨C.sideNot_mem_set_of_high (by sinl only), ?_⟩
    intro h; simp only at h
    exact absurd h (ne_of_lt (abs_lt.2 hta))

theorem sidePt_tour (β : Bool) {i : ℕ} (hi : i < 2 * C.m) (t : ℝ) :
    sidePt (C.sideWalk β) (i + 6) t = lerp (C.sideTour β i) (C.sideTour β (i + 1)) t := by
  unfold sidePt
  rw [C.sideWalk_next_tour β hi, C.sideWalk_vtx_tour β hi.le, C.sideWalk_vtx_tour β (by omega)]

theorem sideLeft_tour_first (β : Bool) (x : Point) :
    sideLeft (C.sideWalk β) (0 + 6) 0 x ↔ sideLeftOf C.slitTop C.top (C.sideTour β 1) x := by
  have hm := C.one_le
  rw [sideLeft_zero, C.sideWalk_prev_six β, C.sideWalk_next_tour β (by omega),
    C.sideWalk_vtx_tour β (by omega), C.sideWalk_vtx_tour β (by omega), sideTour_zero]
  rfl

theorem sideLeft_tour_inner (β : Bool) {i : ℕ} (hi0 : 0 < i) (hi : i < 2 * C.m) (x : Point) :
    sideLeft (C.sideWalk β) (i + 6) 0 x ↔
      sideLeftOf (C.sideTour β (i - 1)) (C.sideTour β i) (C.sideTour β (i + 1)) x := by
  rw [sideLeft_zero, C.sideWalk_prev_tour β hi0 hi.le, C.sideWalk_next_tour β hi,
    C.sideWalk_vtx_tour β (by omega), C.sideWalk_vtx_tour β hi.le, C.sideWalk_vtx_tour β (by omega)]

theorem sideLeft_tour_last (β : Bool) (x : Point) :
    sideLeft (C.sideWalk β) (2 * C.m + 6) 0 x ↔
      sideLeftOf (C.sideTour β (2 * C.m - 1)) C.top C.slitTop x := by
  have hm := C.one_le
  rw [sideLeft_zero, C.sideWalk_prev_tour β (by omega) le_rfl, C.sideWalk_next_last β,
    C.sideWalk_vtx_tour β (by omega), C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
  rfl

/-- A point inside a tour edge is a point of an open chain edge. -/
theorem sideTour_open (β : Bool) {i : ℕ} (hi : i < 2 * C.m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ k, k < C.m ∧ ∃ s ∈ Ioo (0 : ℝ) 1,
      sidePt (C.sideWalk β) (i + 6) t = lerp (C.vertex k) (C.vertex (k + 1)) s ∧
      ((C.sideIdx β i = k ∧ C.sideIdx β (i + 1) = k + 1) ∨
        (C.sideIdx β i = k + 1 ∧ C.sideIdx β (i + 1) = k)) := by
  rw [C.sidePt_tour β hi]
  have hle := C.sideIdx_le β (i + 1)
  have hle' := C.sideIdx_le β i
  unfold sideTour
  rcases C.sideTour_step β i with h | h
  · exact ⟨C.sideIdx β i, by omega, t, ht, by rw [h], Or.inl ⟨rfl, h⟩⟩
  · refine ⟨C.sideIdx β (i + 1), by omega, 1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_,
      Or.inr ⟨h.symm, rfl⟩⟩
    rw [← h]
    apply point_ext <;> simp [lerp] <;> ring

/-- **Disjointness at the chain**: two distinct positions of the corrected walk at the same point
of the chain have disjoint open left sectors. -/
theorem sideDisj_tour (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) {i i' : ℕ} {t t' : ℝ}
    (hi : i ≤ 2 * C.m) (hi' : i' ≤ 2 * C.m) (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (hit : i = 2 * C.m → t = 0) (hit' : i' = 2 * C.m → t' = 0) (hne : i = i' → t ≠ t')
    (heq : sidePt (C.sideWalk β) (i + 6) t = sidePt (C.sideWalk β) (i' + 6) t') (x : Point) :
    ¬ (sideLeft (C.sideWalk β) (i + 6) t x ∧ sideLeft (C.sideWalk β) (i' + 6) t' x) := by
  have hm := C.one_le
  -- the vertex case
  have hvv : ∀ j j' : ℕ, j < j' → j' ≤ 2 * C.m → C.sideIdx β j = C.sideIdx β j' →
      ¬ (sideLeft (C.sideWalk β) (j + 6) 0 x ∧ sideLeft (C.sideWalk β) (j' + 6) 0 x) := by
    intro j j' hjj hj' hidx
    by_cases hT : C.sideIdx β j = C.topIdx
    · obtain ⟨d1, d2, d3⟩ := C.sideTop_disj hP hβ x
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        rw [C.sideLeft_tour_first]
        rcases lt_or_eq_of_le hj' with h2 | h2
        · have hT' : C.sideIdx β j' = C.topIdx := hidx ▸ hT
          obtain ⟨hT0, hTm⟩ := C.sideTour_top_inner β hjj h2 hT'
          obtain ⟨hp1, hn1⟩ := C.sideTour_top_mid β hjj h2 hT0 hTm hT'
          rw [C.sideLeft_tour_inner β hjj h2]
          unfold sideTour at *
          rw [hp1, hn1, hT']
          exact d2 ⟨hT0, hTm⟩
        · subst h2; rwx [C.sideLeft_tour_last]
      · rcases lt_or_eq_of_le hj' with h2 | h2
        · -- two inner visits of the top vertex: impossible
          exfalso
          have hT'  := hidx ▸ hT
          obtain ⟨hT0, hTm⟩ := C.sideTour_top_inner β h0 (by omega) hT
          have e1 := (C.sideTour_top_mid β h0 (by omega) hT0 hTm hT).2
          have e2 := (C.sideTour_top_mid β (by omega) h2 hT0 hTm hT').2
          rcases C.sideTour_two_visits β (by omega) h2 (by omega) hidx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
            omega
        · subst h2
          have hjm : j < 2 * C.m := by omega
          obtain ⟨hT0, hTm⟩ := C.sideTour_top_inner β h0 hjm hT
          obtain ⟨hp1, hn1⟩ := C.sideTour_top_mid β h0 hjm hT0 hTm hT
          rw [C.sideLeft_tour_inner β h0 hjm, C.sideLeft_tour_last]
          unfold sideTour at *
          rw [hp1, hn1, hT]
          exact fun h => d3 ⟨hT0, hTm⟩ ⟨h.2, h.1⟩
    · -- a chain vertex other than the top vertex: two inner visits, forwards and backwards
      have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; exact absurd (C.sideIdx_zero β) hT
        · exact h
      have hj2 : j' < 2 * C.m := by
        rcases lt_or_eq_of_le hj' with h | h
        · exact h
        · subst h; exact absurd (hidx.trans (C.sideIdx_two_m β)) hT
      rw [C.sideLeft_tour_inner β hj0 (by omega), C.sideLeft_tour_inner β (by omega) hj2]
      have hv := C.sideTour_two_visits β (by omega) hj2 (by omega) hidx
      have hk := C.sideIdx_le β j
      have hk1 := C.sideIdx_le β (j + 1)
      have hk1' := C.sideIdx_le β (j' + 1)
      rcases C.sideTour_corner β hj0 (by omega) with ⟨a0, am, ap, an⟩ | ⟨a0, am, ap, an⟩ |
          ⟨a0, ap, an⟩ | ⟨a0, ap, an⟩ <;>
        rcases C.sideTour_corner β (i := j') (by omega) hj2 with ⟨b0, bm, bp, bn⟩ |
          ⟨b0, bm, bp, bn⟩ | ⟨b0, bp, bn⟩ | ⟨b0, bp, bn⟩
      all_goals first
        | (exfalso; rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
        | skip
      all_goals unfold sideTour sideLeftOf
      · -- forward then backward
        have e1 : C.sideIdx β (j - 1) = C.sideIdx β j - 1 := by omega
        have e2 : C.sideIdx β (j' - 1) = C.sideIdx β j + 1 := by omega
        have e3 : C.sideIdx β (j' + 1) = C.sideIdx β j - 1 := by omega
        rw [e1, e2, e3, an, ← hidx]
        have hns := (C.sideChain_nonSpike hP a0 am).1
        exact fun h => sideCcw_asymm (sub_ne_zero_of_ne' (C.sideVertex_succ_ne hP _).symm)
          hns h.1 h.2
      · -- backward then forward
        have e1 : C.sideIdx β (j + 1) = C.sideIdx β j - 1 := by omega
        have e2 : C.sideIdx β (j' - 1) = C.sideIdx β j - 1 := by omega
        have e3 : C.sideIdx β (j' + 1) = C.sideIdx β j + 1 := by omega
        rw [ap, e1, e2, e3, ← hidx]
        have hns := (C.sideChain_nonSpike hP a0 am).2
        exact fun h => sideCcw_asymm (sub_ne_zero_of_ne' (C.sideVertex_pred_ne hP a0))
          hns h.1 h.2
  -- the edge case
  have hee : ∀ j j' : ℕ, j < 2 * C.m → j' < 2 * C.m → ∀ s s' : ℝ, s ∈ Ioo (0 : ℝ) 1 →
      s' ∈ Ioo (0 : ℝ) 1 → (j = j' → s ≠ s') →
      sidePt (C.sideWalk β) (j + 6) s = sidePt (C.sideWalk β) (j' + 6) s' →
      ¬ (sideLeft (C.sideWalk β) (j + 6) s x ∧ sideLeft (C.sideWalk β) (j' + 6) s' x) := by
    intro j j' hj hj' s s' hs hs' hne' heq'
    obtain ⟨k, hk, r, hr, hpk, hk1⟩ := C.sideTour_open β hj hs
    obtain ⟨k', hk', r', hr', hpk', hk1'⟩ := C.sideTour_open β hj' hs'
    have hkk : k = k' := by
      by_contra hkk
      have hmem : lerp (C.vertex k) (C.vertex (k + 1)) r ∈ C.chainEdge k' := by
        rw [← hpk, heq', hpk', C.chainEdge_eq]; exact lerp_mem_segment _ _ hr'.1.le hr'.2.le
      exact C.sideOpen_not_mem_chainEdge hP hk hk' (Ne.symm hkk) hr hmem
    subst hkk
    have hnd := C.sideWalk_nd hP β
    rw [sideLeft_edge (hnd _ (by rwo [sideWalk_n])) hs,
      sideLeft_edge (hnd _ (by rwo [sideWalk_n])) hs',
      C.sideWalk_next_tour β hj, C.sideWalk_next_tour β hj', C.sideWalk_vtx_tour β hj.le,
      C.sideWalk_vtx_tour β (by omega), C.sideWalk_vtx_tour β hj'.le,
      C.sideWalk_vtx_tour β (by omega)]
    unfold sideTour
    have hsame : ¬ (C.sideIdx β j = C.sideIdx β j') := by
      intro hidx
      by_cases hjj : j = j'
      · subst hjj
        apply hne' rfl
        rw [C.sidePt_tour β hj, C.sidePt_tour β hj] at heq'
        exact Geometry.lerp_injective (by
          have := hnd (j + 6) (by rwo [sideWalk_n])
          rwa [C.sideWalk_next_tour β hj, C.sideWalk_vtx_tour β hj.le,
            C.sideWalk_vtx_tour β (by omega)] at this) heq'
      · rcases C.sideTour_two_visits β hj hj' hjj hidx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          rcases hk1 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> rcases hk1' with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;> omega
    rcases hk1 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> rcases hk1' with ⟨d1, d2⟩ | ⟨d1, d2⟩
    · exact absurd (c1.trans d1.symm) hsame
    · rw [c1, c2, d1, d2]
      rintro ⟨h1, h2⟩
      rwli [Geometry.det_swap12] at h2
    · rw [c1, c2, d1, d2]
      rintro ⟨h1, h2⟩
      rwli [Geometry.det_swap12] at h2
    · exact absurd (c1.trans d1.symm) hsame
  -- assembling the cases
  rcases ht.lt_or_eq with htp | htz <;> rcases ht'.lt_or_eq with htp' | htz'
  · exact hee i i' (lt_of_le_of_ne hi (fun h => htp.ne' (hit h)))
      (lt_of_le_of_ne hi' (fun h => htp'.ne' (hit' h))) t t' ⟨htp, ht1⟩ ⟨htp', ht1'⟩ hne heq
  · -- a vertex and an open edge point cannot coincide
    exfalso
    subst htz'
    have hil : i < 2 * C.m := lt_of_le_of_ne hi (fun h => htp.ne' (hit h))
    obtain ⟨k, hk, r, hr, hpk, -⟩ := C.sideTour_open β hil ⟨htp, ht1⟩
    rw [hpk, sidePt_zero, C.sideWalk_vtx_tour β hi'] at heq
    exact C.sideOpen_ne_vertex hP hr heq
  · exfalso
    subst htz
    have hil : i' < 2 * C.m := lt_of_le_of_ne hi' (fun h => htp'.ne' (hit' h))
    obtain ⟨k, hk, r, hr, hpk, -⟩ := C.sideTour_open β hil ⟨htp', ht1'⟩
    rw [hpk, sidePt_zero, C.sideWalk_vtx_tour β hi] at heq
    exact C.sideOpen_ne_vertex hP hr heq.symm
  · subst htz htz'
    have hii : i ≠ i' := fun h => hne h rfl
    rw [sidePt_zero, sidePt_zero, C.sideWalk_vtx_tour β hi, C.sideWalk_vtx_tour β hi'] at heq
    have hidx := C.sideVertex_inj hP (C.sideIdx_le β i) (C.sideIdx_le β i') heq
    rcases lt_or_gt_of_ne hii with h | h
    · exact hvv i i' h hi' hidx
    · exact fun hh => hvv i' i h hi hidx.symm ⟨hh.2, hh.1⟩

theorem sideWalk_pos_cases (β : Bool) {p : ℕ} (hp : p < (C.sideWalk β).n) {t : ℝ} (ht : 0 ≤ t) :
    (p ≤ 5 ∨ (p = 2 * C.m + 6 ∧ 0 < t)) ∨ (∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ (i = 2 * C.m → t = 0)) := by
  rcases C.sideWalk_lt_cases β hp with h5 | ⟨i, hi, rfl⟩ | rfl
  · exact Or.inl (Or.inl h5)
  · exact Or.inr ⟨i, hi.le, rfl, fun h => absurd h (by omega)⟩
  · rcases ht.lt_or_eq with h | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr ⟨2 * C.m, le_rfl, rfl, fun _ => h.symm⟩

theorem sideWalk_tour_pt_mem (β : Bool) {i : ℕ} {t : ℝ} (hi : i ≤ 2 * C.m) (hit : i = 2 * C.m → t = 0)
    (ht : 0 ≤ t) (ht1 : t < 1) : sidePt (C.sideWalk β) (i + 6) t ∈ C.set := by
  rcases lt_or_eq_of_le hi with hi | hi
  · rw [C.sidePt_tour β hi]
    unfold sideTour
    rcases C.sideTour_step β i with h | h
    · exact C.sideLerp_mem_set (Or.inl h) (C.sideIdx_le β i) (C.sideIdx_le β _) ht ht1.le
    · exact C.sideLerp_mem_set (Or.inr h) (C.sideIdx_le β i) (C.sideIdx_le β _) ht ht1.le
  · subst hi
    rw [hit rfl, sidePt_zero, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
    exact C.top_mem_set

/-- **Disjointness of the left sectors at a chord endpoint.**  Two distinct positions of the
corrected walk at a common point of the chain, or of an open vertical side of the box, have
disjoint open left sectors. -/
theorem sideWalk_disj (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) {pa p : ℕ} {ta t : ℝ}
    (hpa : pa < (C.sideWalk β).n) (hta : 0 ≤ ta) (hta1 : ta < 1)
    (hp : p < (C.sideWalk β).n) (ht : 0 ≤ t) (ht1 : t < 1) (hne : p = pa → t ≠ ta)
    (heq : sidePt (C.sideWalk β) p t = sidePt (C.sideWalk β) pa ta)
    (hq : sidePt (C.sideWalk β) pa ta ∈ C.set ∨
      (|(sidePt (C.sideWalk β) pa ta).1| = C.radius ∧ |(sidePt (C.sideWalk β) pa ta).2| < C.radius))
    (x : Point) : ¬ (sideLeft (C.sideWalk β) pa ta x ∧ sideLeft (C.sideWalk β) p t x) := by
  have hcb := C.coordBound_lt_radius
  -- a point of the chain is not on an open vertical side
  have hsetv : ∀ y ∈ C.set, |y.1| = C.radius → False := fun y hy h => by
    have := (C.abs_le_coordBound_of_mem_set hy).1; linarith
  rcases C.sideWalk_pos_cases β hpa hta with hA | ⟨ia, hia, rfl, hiat⟩ <;>
    rcases C.sideWalk_pos_cases β hp ht with hX | ⟨i, hi, rfl, hit⟩
  · -- two positions of the box block
    obtain ⟨hA1, hA2⟩ := C.sideWalk_box_pt β hA hta hta1
    obtain ⟨hX1, hX2⟩ := C.sideWalk_box_pt β hX ht ht1
    rcases hq with hq | ⟨hq1, hq2⟩
    · exact absurd hq hA1
    · obtain ⟨hA3, hA4⟩ := hA2 hq1 hq2
      rw [← heq] at hq1 hq2
      obtain ⟨hX3, hX4⟩ := hX2 hq1 hq2
      have hR := C.radius_pos
      have hpp : p = pa := by
        rcases hA3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hX3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · rw [h1, h3]
        · exfalso; rwli [heq] at h4
        · exfalso; rwli [heq] at h4
        · rw [h1, h3]
      subst hpp
      exfalso
      apply hne rfl
      exact Geometry.lerp_injective (C.sideWalk_nd hP β p hp) heq
  · exfalso
    obtain ⟨hA1, hA2⟩ := C.sideWalk_box_pt β hA hta hta1
    have hmem := C.sideWalk_tour_pt_mem β hi hit ht ht1
    rw [heq] at hmem
    rcases hq with hq | ⟨hq1, -⟩
    · exact hA1 hq
    · exact hsetv _ hmem hq1
  · exfalso
    obtain ⟨hX1, -⟩ := C.sideWalk_box_pt β hX ht ht1
    have hmem := C.sideWalk_tour_pt_mem β hia hiat hta hta1
    rw [← heq] at hmem
    exact hX1 hmem
  · exact C.sideDisj_tour hP hβ hia hi hta hta1 ht ht1 hiat hit
      (fun h => by subst h; exact fun h' => hne rfl h'.symm) heq.symm x

/-! ### Chords as segments of the walk's complement -/

omit C in
theorem sideKey_inj {p p' : ℕ} {t t' : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h : (p : ℝ) + t = p' + t') : p = p' ∧ t = t' := by
  have hpp : p = p' := by
    rcases lt_trichotomy p p' with hlt | heq | hgt
    · exfalso
      have : (p : ℝ) + 1 ≤ p' := by exact_mod_cast hlt
      linarith
    · exact heq
    · exfalso
      have : (p' : ℝ) + 1 ≤ p := by exact_mod_cast hgt
      linarith
  subst hpp
  exact ⟨rfl, by linarith⟩

omit C in
/-- The two arcs cut by two distinct keys partition the other keys. -/
theorem sideInArc_swap {a b x : ℝ} (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    sideInArc a b x ↔ ¬ sideInArc b a x := by
  unfold sideInArc
  rcases lt_or_gt_of_ne hab with h | h
  · rw [ite_eq_left h, ite_eq_right (not_lt.2 h.le)]
    constructor
    · rintro ⟨h1, h2⟩ (h3 | h3) <;> linarith
    · intro h3
      push Not at h3
      exact ⟨lt_of_le_of_ne h3.2 (Ne.symm hxa), lt_of_le_of_ne h3.1 hxb⟩
  · rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h]
    constructor
    · rintro (h1 | h1) ⟨h2, h3⟩ <;> linarith
    · intro h3
      by_cases h4 : a < x
      · exact Or.inl h4
      · right
        have h5  := lt_of_le_of_ne (not_lt.1 h4) hxa
        by_contra h6
        push Not at h6
        exact h3 ⟨lt_of_le_of_ne h6 (Ne.symm hxb), h5⟩

/-! ### A correct turn at the top vertex always exists -/

omit C in
/-- **Coverage**: a direction `X` that lies on neither closed ray of the (non-spike) directions
`A`, `B` is strictly inside one of the two complementary counterclockwise arcs between them. -/
theorem sideCcw_or {A B X : Point} (hA : A ≠ 0) (hB : B ≠ 0) (hns : sideNonSpike A B)
    (hXA : ¬ (sideCross A X = 0 ∧ 0 ≤ sideDot A X))
    (hXB : ¬ (sideCross B X = 0 ∧ 0 ≤ sideDot B X)) : sideCcw A X B ∨ sideCcw B X A := by
  have hAA := sideDot_self_pos hA
  have hBB := sideDot_self_pos hB
  have eAB : sideCross B A = -sideCross A B := sideCross_swap _ _
  have eXA : sideCross X A = -sideCross A X := sideCross_swap _ _
  have eXB : sideCross X B = -sideCross B X := sideCross_swap _ _
  have D1 := side_dotCross A X B
  have D2 := side_dotCross B X A
  rw [eXB] at D1
  rw [eAB, eXA] at D2
  unfold sideCcw
  rw [eAB, eXA, eXB]
  push Not at hXA hXB
  rcases lt_trichotomy (sideCross A B) 0 with hab | hab | hab
  · -- `B` is clockwise from `A`: the arc from `B` to `A` is convex
    by_cases h1 : 0 < sideCross B X ∧ 0 < -sideCross A X
    · exact Or.inr (Or.inl ⟨by linarith, h1.1, h1.2⟩)
    · left; right; left
      refine ⟨hab, ?_⟩
      by_contra hc
      push Not at hc h1
      obtain ⟨hc1, hc2⟩ := hc
      rcases lt_or_eq_of_le (show 0 ≤ sideCross B X by linarith) with hy | hy
      · have hx : sideCross A X = 0 := le_antisymm hc1 (by linarith [h1 hy])
        rw [hx, zero_mul, add_zero] at D1
        nlinarith [mul_pos_of_neg_of_neg (hXA hx) hab, mul_pos hAA hy]
      · rw [← hy, zero_mul, add_zero] at D2
        nlinarith [mul_neg_of_neg_of_pos (hXB hy.symm) (neg_pos.2 hab),
          mul_nonneg hBB.le (neg_nonneg.2 hc1)]
  · -- straight
    have hL := side_lagrange A B
    have hd : sideDot A B < 0 := by
      rcases lt_trichotomy (sideDot A B) 0 with h | h | h
      · exact h
      · rw [hab, h] at hL; nlinarith [mul_pos hAA hBB]
      · exact absurd ⟨hab, h⟩ hns
    rw [hab, mul_zero] at D1
    rcases lt_trichotomy (sideCross A X) 0 with hx | hx | hx
    · right; right; right; left
      refine ⟨by linarith, by rwx [sideDot_comm], ?_⟩
      nlinarith [mul_pos_of_neg_of_neg hx hd]
    · exfalso
      rw [hx, zero_mul, add_zero] at D1
      have hy : sideCross B X = 0 := by
        have : sideDot A A * sideCross B X = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact h
      have DD := side_dotDot A X B
      rw [hx, zero_mul, add_zero] at DD
      have h5 := hXB hy
      rw [sideDot_comm] at h5
      nlinarith [mul_pos_of_neg_of_neg (hXA hx) hd, mul_neg_of_pos_of_neg hAA h5]
    · left; right; right; left
      exact ⟨hab, hd, hx⟩
  · -- `B` is counterclockwise from `A`: the arc from `A` to `B` is convex
    by_cases h1 : 0 < sideCross A X ∧ 0 < -sideCross B X
    · exact Or.inl (Or.inl ⟨hab, h1.1, h1.2⟩)
    · right; right; left
      refine ⟨by linarith, ?_⟩
      by_contra hc
      push Not at hc h1
      obtain ⟨hc1, hc2⟩ := hc
      rcases lt_or_eq_of_le (show 0 ≤ sideCross A X by linarith) with hx | hx
      · have hy : sideCross B X = 0 := le_antisymm hc1 (by linarith [h1 hx])
        rw [hy, zero_mul, add_zero] at D2
        nlinarith [mul_pos_of_neg_of_neg (hXB hy) (neg_neg_of_pos hab), mul_pos hBB hx]
      · rw [← hx, zero_mul, add_zero] at D1
        nlinarith [mul_neg_of_neg_of_pos (hXA hx.symm) hab,
          mul_nonneg hAA.le (neg_nonneg.2 hc1)]

theorem sideIdx_nbrs_true (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) :
    C.sideIdx true 1 = C.topIdx + 1 ∧ C.sideIdx true (2 * C.m - 1) = C.topIdx - 1 := by
  rw [C.sideIdx_one, C.sideIdx_last]
  have hs : C.sideS true % (2 * C.m) = C.topIdx := by
    unfold sideS; simp only [↓reduceIte]; exact Nat.mod_eq_of_lt (by omega)
  rw [hs]
  rcases side_mod_cases (show C.topIdx + (2 * C.m - 1) < 2 * (2 * C.m) by omega) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> unfold sideE <;> split_ifs <;> omega

theorem sideIdx_nbrs_false (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) :
    C.sideIdx false 1 = C.topIdx - 1 ∧ C.sideIdx false (2 * C.m - 1) = C.topIdx + 1 := by
  rw [C.sideIdx_one, C.sideIdx_last]
  have hs : C.sideS false % (2 * C.m) = 2 * C.m - C.topIdx := by
    unfold sideS; simp only [Bool.false_eq_true, ↓reduceIte]; exact Nat.mod_eq_of_lt (by omega)
  rw [hs]
  rcases side_mod_cases (show 2 * C.m - C.topIdx + (2 * C.m - 1) < 2 * (2 * C.m) by omega) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> unfold sideE <;> split_ifs <;> omega

open Classical in
/-- **The correct choice of the turn at the top vertex**: `true` (leave the top vertex towards
`v_{T+1}`, as `boundaryWalk` does) iff the slit direction lies strictly inside the
counterclockwise arc from `v_{T+1}` to `v_{T-1}` around the top vertex. -/
noncomputable def sideBeta : Bool :=
  decide (sideCcw (C.vertex (C.topIdx + 1) - C.top) (C.slitTop - C.top)
    (C.vertex (C.topIdx - 1) - C.top))

open Classical in
/-- Characterization of `sideBeta`. -/
theorem sideBeta_eq_true_iff : C.sideBeta = true ↔ sideCcw (C.vertex (C.topIdx + 1) - C.top)
    (C.slitTop - C.top) (C.vertex (C.topIdx - 1) - C.top) := by
  unfold sideBeta; exact decide_eq_true_iff

theorem sideVertex_sub_top_ne (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) (hkT : k ≠ C.topIdx) :
    C.vertex k - C.top ≠ 0 :=
  sub_ne_zero_of_ne' (fun h => hkT (C.sideVertex_inj hP hk C.topIdx_le h))

theorem sideUp_not_ray (k : ℕ) (hk : k ≤ C.m) (hne : C.vertex k - C.top ≠ 0) :
    ¬ (sideCross (C.vertex k - C.top) (C.slitTop - C.top) = 0 ∧
      0 ≤ sideDot (C.vertex k - C.top) (C.slitTop - C.top)) := by
  rintro ⟨hc, hd⟩
  have hy := C.vertex_snd_le_top hk
  have htop := C.top_snd_lt_radius
  apply hne
  unfold sideCross at hc
  unfold sideDot at hd
  simp only [Prod.fst_sub, Prod.snd_sub, slitTop, sub_self, mul_zero, sub_zero,
    zero_add] at hc hd
  have h1 : (C.vertex k).1 - C.top.1 = 0 := by
    rcases mul_eq_zero.1 hc with h | h
    · exact h
    · linarith
  have h2 : (C.vertex k).2 - C.top.2 = 0 := by nlinarith
  exact point_ext (by simp [h1]) (by simp [h2])

/-- **The corrected walk turns correctly at the top vertex**: `C.sideBeta` satisfies the order
condition `SideGood` needed by `side_lemma21`. -/
theorem sideGood_sideBeta (hP : C.P.Simple) : C.SideGood C.sideBeta := by
  unfold SideGood
  by_cases hT0 : C.topIdx = 0
  · exact Or.inl hT0
  by_cases hTm : C.topIdx = C.m
  · exact Or.inr (Or.inl hTm)
  have hT := C.topIdx_le
  have h0  := Nat.pos_of_ne_zero hT0
  have hm  := lt_of_le_of_ne hT hTm
  right; right
  have hA := C.sideVertex_sub_top_ne hP (k := C.topIdx + 1) (by omega) (by omega)
  have hB := C.sideVertex_sub_top_ne hP (k := C.topIdx - 1) (by omega) (by omega)
  have hns  := (C.sideChain_nonSpike hP h0 hm).1
  have hor := sideCcw_or hA hB hns (C.sideUp_not_ray _ (by omega) hA)
    (C.sideUp_not_ray _ (by omega) hB)
  cases hb : C.sideBeta with
  | true =>
    have h := C.sideBeta_eq_true_iff.1 hb
    obtain ⟨e1, e2⟩ := C.sideIdx_nbrs_true h0 hm
    unfold sideTour; rwx [e1, e2]
  | false =>
    have h : ¬ sideCcw (C.vertex (C.topIdx + 1) - C.top) (C.slitTop - C.top)
        (C.vertex (C.topIdx - 1) - C.top) := fun h' => by
      have := C.sideBeta_eq_true_iff.2 h'
      rw [hb] at this
      exact Bool.false_ne_true this
    obtain ⟨e1, e2⟩ := C.sideIdx_nbrs_false h0 hm
    unfold sideTour; rw [e1, e2]
    exact hor.resolve_left h

/-! ### Every chord endpoint is attached to the corrected walk -/

omit C in
/-- A segment leaving a point of a segment `[v, w]` along the line of `[v, w]` (forwards when
the point is `v`) starts inside `[v, w]`. -/
theorem side_overlap {v w e e' : Point} {s₀ : ℝ} (hvw : v ≠ w) (hs0 : 0 ≤ s₀) (hs1 : s₀ < 1)
    (he : e = lerp v w s₀) (hee : e' ≠ e) (hc : sideCross (w - v) (e' - e) = 0)
    (hd : s₀ = 0 → 0 ≤ sideDot (w - v) (e' - e)) :
    ∃ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ Chazelle.segment v w := by
  have hAA := sideDot_self_pos (sub_ne_zero_of_ne' hvw.symm)
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = sideDot (w - v) (e' - e) / sideDot (w - v) (w - v) := ⟨_, rfl⟩
  have hX1 : e'.1 - e.1 = μ * (w.1 - v.1) := by
    have key : sideDot (w - v) (w - v) * (e'.1 - e.1) =
        sideDot (w - v) (e' - e) * (w.1 - v.1) - sideCross (w - v) (e' - e) * (w.2 - v.2) := by
      unfold sideDot sideCross; sir only [Prod.fst_sub, Prod.snd_sub]
    rw [hc, zero_mul, sub_zero] at key
    rwli [hμ, div_mul_eq_mul_div, eq_div_iff hAA.ne']
  have hX2 : e'.2 - e.2 = μ * (w.2 - v.2) := by
    have key : sideDot (w - v) (w - v) * (e'.2 - e.2) =
        sideDot (w - v) (e' - e) * (w.2 - v.2) + sideCross (w - v) (e' - e) * (w.1 - v.1) := by
      unfold sideDot sideCross; sir only [Prod.fst_sub, Prod.snd_sub]
    rw [hc, zero_mul, add_zero] at key
    rwli [hμ, div_mul_eq_mul_div, eq_div_iff hAA.ne']
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hee
    rw [h0, zero_mul] at hX1 hX2
    exact point_ext (by linarith) (by linarith)
  obtain ⟨s, hs, hlo, hhi⟩ : ∃ s ∈ Ioo (0 : ℝ) 1, 0 ≤ s₀ + s * μ ∧ s₀ + s * μ ≤ 1 := by
    rcases lt_or_gt_of_ne hμ0 with hneg | hpos
    · have hs0' : 0 < s₀ := by
        rcases hs0.lt_or_eq with h | h
        · exact h
        · exfalso
          have h1 := hd h.symm
          have : 0 ≤ μ := by rw [hμ]; exact div_nonneg h1 hAA.le
          linarith
      have hpos' : 0 < min (1 / 2) (s₀ / -μ) := lt_min (by norm_num) (div_pos hs0' (by linarith))
      refine ⟨min (1 / 2) (s₀ / -μ), ⟨hpos', lt_of_le_of_lt (min_le_left _ _) (by norm_num)⟩,
        ?_, ?_⟩
      · have h1 : min (1 / 2) (s₀ / -μ) ≤ s₀ / -μ := min_le_right _ _
        have h2 : min (1 / 2) (s₀ / -μ) * -μ ≤ s₀ :=
          calc _ ≤ s₀ / -μ * -μ := mul_le_mul_of_nonneg_right h1 (by linarith)
            _ = s₀ := div_mul_cancel₀ _ (by linarith)
        linarith
      · nlinarith
    · have hpos' : 0 < min (1 / 2) ((1 - s₀) / μ) := lt_min (by norm_num) (div_pos (by linarith) hpos)
      refine ⟨min (1 / 2) ((1 - s₀) / μ), ⟨hpos', lt_of_le_of_lt (min_le_left _ _) (by norm_num)⟩,
        ?_, ?_⟩
      · nlinarith
      · have h1 : min (1 / 2) ((1 - s₀) / μ) ≤ (1 - s₀) / μ := min_le_right _ _
        have h2 : min (1 / 2) ((1 - s₀) / μ) * μ ≤ 1 - s₀ :=
          calc _ ≤ (1 - s₀) / μ * μ := mul_le_mul_of_nonneg_right h1 hpos.le
            _ = 1 - s₀ := div_mul_cancel₀ _ hpos.ne'
        linarith
  have he1 : e.1 = v.1 + s₀ * (w.1 - v.1) := by rw [he, lerp_fst]
  have he2 : e.2 = v.2 + s₀ * (w.2 - v.2) := by rw [he, lerp_snd]
  refine ⟨s, hs, s₀ + s * μ, hlo, hhi, ?_⟩
  apply point_ext
  · simp only [lerp_fst]; rwring [hX1, he1]
  · simp only [lerp_snd]; rwring [hX2, he2]

/-- **A chord leaves a chain vertex off the closed rays of its chain edges.** -/
theorem sideRay_free (hP : C.P.Simple) {j j' : ℕ} (hjj : j' = j + 1 ∨ j' + 1 = j) (hj : j ≤ C.m)
    (hj' : j' ≤ C.m) {e' : Point} (hee : e' ≠ C.vertex j)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (C.vertex j) e' s ∈ C.dom) :
    ¬ (sideCross (C.vertex j' - C.vertex j) (e' - C.vertex j) = 0 ∧
      0 ≤ sideDot (C.vertex j' - C.vertex j) (e' - C.vertex j)) := by
  rintro ⟨hc, hd⟩
  have hne : C.vertex j ≠ C.vertex j' := by
    rcases hjj with rfl | rfl
    · exact C.sideVertex_succ_ne hP j
    · exact (C.sideVertex_succ_ne hP j').symm
  obtain ⟨s, hs, hmem⟩ := side_overlap hne le_rfl zero_lt_one (lerp_zero _ _).symm hee hc
    (fun _ => hd)
  obtain ⟨t, ht0, ht1, ht⟩ := hmem
  have hset : lerp (C.vertex j) e' s ∈ C.set := by
    rw [ht]; exact C.sideLerp_mem_set hjj hj hj' ht0 ht1
  exact C.not_mem_set_of_mem_dom (hopen s hs) hset

omit C in
/-- The left sector of the walk at the top vertex coming down the slit and leaving along a chain
edge going down contains the direction east. -/
theorem sideCcw_east {A U X : Point} (hU1 : U.1 = 0) (hU2 : 0 < U.2) (hX2 : X.2 = 0)
    (hX1 : 0 < X.1) (hA2 : A.2 ≤ 0) (hA : A ≠ 0)
    (hray : ¬ (sideCross A X = 0 ∧ 0 ≤ sideDot A X)) : sideCcw A X U := by
  have hc1 : sideCross A U = A.1 * U.2 := by unfold sideCross; rwring [hU1]
  have hc2 : sideCross A X = -(A.2 * X.1) := by unfold sideCross; rwring [hX2]
  have hc3 : sideCross X U = X.1 * U.2 := by unfold sideCross; rwring [hU1, hX2]
  have hd1 : sideDot A U = A.2 * U.2 := by unfold sideDot; rwring [hU1]
  have hd2 : sideDot A X = A.1 * X.1 := by unfold sideDot; rwring [hX2]
  rw [hc2, hd2] at hray
  unfold sideCcw
  rw [hc1, hc2, hc3, hd1]
  rcases lt_trichotomy A.1 0 with h | h | h
  · right; left; exact ⟨by nlinarith, Or.inr (by positivity)⟩
  · have hA2' : A.2 < 0 := by
      rcases hA2.lt_or_eq with h' | h'
      · exact h'
      · exact absurd (point_ext h h') hA
    right; right; left
    exact ⟨by rwring [h], by nlinarith, by nlinarith⟩
  · have hA2' : A.2 < 0 := by
      rcases hA2.lt_or_eq with h' | h'
      · exact h'
      · exfalso; apply hray; rw [h']; exact ⟨by ring, by positivity⟩
    left; exact ⟨by positivity, by nlinarith, by positivity⟩

omit C in
/-- The left sector of the walk at the top vertex arriving along a chain edge from below and
going up the slit contains the direction west. -/
theorem sideCcw_west {B U X : Point} (hU1 : U.1 = 0) (hU2 : 0 < U.2) (hX2 : X.2 = 0)
    (hX1 : X.1 < 0) (hB2 : B.2 ≤ 0) (hB : B ≠ 0)
    (hray : ¬ (sideCross B X = 0 ∧ 0 ≤ sideDot B X)) : sideCcw U X B := by
  have hc1 : sideCross U B = -(U.2 * B.1) := by unfold sideCross; rwring [hU1]
  have hc2 : sideCross U X = -(U.2 * X.1) := by unfold sideCross; rwring [hU1, hX2]
  have hc3 : sideCross X B = X.1 * B.2 := by unfold sideCross; rwring [hX2]
  have hd1 : sideDot U B = U.2 * B.2 := by unfold sideDot; rwring [hU1]
  have hc4 : sideCross B X = -(B.2 * X.1) := by unfold sideCross; rwring [hX2]
  have hd2 : sideDot B X = B.1 * X.1 := by unfold sideDot; rwring [hX2]
  rw [hc4, hd2] at hray
  unfold sideCcw
  rw [hc1, hc2, hc3, hd1]
  rcases lt_trichotomy B.1 0 with h | h | h
  · have hB2' : B.2 < 0 := by
      rcases hB2.lt_or_eq with h' | h'
      · exact h'
      · exfalso; apply hray; rw [h']; exact ⟨by ring, by nlinarith⟩
    left; exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · have hB2' : B.2 < 0 := by
      rcases hB2.lt_or_eq with h' | h'
      · exact h'
      · exact absurd (point_ext h h') hB
    right; right; left
    exact ⟨by rwring [h], by nlinarith, by nlinarith⟩
  · right; left; exact ⟨by nlinarith, Or.inl (by nlinarith)⟩

omit C in
/-- A position whose open left sector contains `e'`, at the point `e`, attaches the segment
`[e, e']`. -/
theorem sideAttach_of_left {W : Polygon} {p : ℕ} {t : ℝ} {e e' : Point} (hp : p < W.n)
    (ht : 0 ≤ t) (ht1 : t < 1) (hpt : sidePt W p t = e) (hl : sideLeft W p t e') :
    SideAttach W (Chazelle.segment e e') p t := by
  refine ⟨hp, ht, ht1, hpt ▸ Geometry.left_mem_segment _ _, 1, one_pos, ?_⟩
  intro x hx hxe _
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  unfold sideLeft sideLeftOf at hl ⊢
  rw [hpt] at hl hxe ⊢
  have hs : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd (lerp_zero _ _) hxe
  have e1 : lerp e e' s - e = s • (e' - e) := by
    apply point_ext <;> simp [lerp]
  rwx [e1, sideCcw_smul hs]

/-- Some position of the walk `W` at the point `e` has `e'` in its open left sector. -/
def SideSees (W : Polygon) (e e' : Point) : Prop :=
  ∃ p t, p < W.n ∧ 0 ≤ t ∧ t < 1 ∧ sidePt W p t = e ∧ sideLeft W p t e'

/-- Every value of the double-tour index is visited by the tour. -/
theorem sideIdx_visit (β : Bool) {j : ℕ} (hj : j < 2 * C.m) :
    ∃ i, i < 2 * C.m ∧ C.sideIdx β i = sideE C.m j ∧ C.sideIdx β (i + 1) = sideE C.m (j + 1) ∧
      (i = 0 → sideE C.m j = C.topIdx) ∧
      (0 < i → C.sideIdx β (i - 1) = sideE C.m (if j = 0 then 2 * C.m - 1 else j - 1)) := by
  have hm2 := C.two_m_pos
  obtain ⟨S', hS'⟩ : ∃ S', S' = C.sideS β % (2 * C.m) := ⟨_, rfl⟩
  have hS := Nat.mod_lt (C.sideS β) hm2
  rw [← hS'] at hS
  have hmod : ∀ i, i < 2 * C.m → (C.sideS β + i) % (2 * C.m) = (S' + i) % (2 * C.m) := by
    intro i hi
    rw [Nat.add_mod, ← hS', Nat.mod_eq_of_lt hi]
  obtain ⟨i, hi, hij⟩ : ∃ i, i < 2 * C.m ∧ (C.sideS β + i) % (2 * C.m) = j := by
    by_cases h : S' ≤ j
    · refine ⟨j - S', by omega, ?_⟩
      rw [hmod _ (by omega), show S' + (j - S') = j by omega, Nat.mod_eq_of_lt hj]
    · refine ⟨j + 2 * C.m - S', by omega, ?_⟩
      rw [hmod _ (by omega), show S' + (j + 2 * C.m - S') = j + 2 * C.m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  refine ⟨i, hi, by rw [sideIdx_eq, hij], by rw [sideIdx_succ, hij], ?_, ?_⟩
  · intro h0
    subst h0
    rw [add_zero] at hij
    rw [← hij]; exact C.sideE_sideS β
  · intro hi0
    rw [sideIdx_eq]; congr 1
    have e := side_idx_succ hm2 (C.sideS β) (i - 1)
    rw [Nat.sub_add_cancel hi0, hij] at e
    have hr := Nat.mod_lt (C.sideS β + (i - 1)) hm2
    generalize (C.sideS β + (i - 1)) % (2 * C.m) = r at e hr ⊢
    rcases lt_or_eq_of_le (show r + 1 ≤ 2 * C.m by omega) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at e; splao
    · rw [h1, Nat.mod_self] at e; splao

/-- At the top vertex: east is seen by the first position of the tour, west by the last. -/
theorem sideSees_top (hP : C.P.Simple) (β : Bool) {e' : Point} (hee : C.top ≠ e')
    (hy : C.top.2 = e'.2) (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp C.top e' s ∈ C.dom) :
    SideSees (C.sideWalk β) C.top e' := by
  have hm := C.one_le
  have hT := C.topIdx_le
  have hU1 : (C.slitTop - C.top).1 = 0 := by simp [slitTop]
  have hU2 : 0 < (C.slitTop - C.top).2 := by simp [slitTop]; linarith [C.top_snd_lt_radius]
  have hX2 : (e' - C.top).2 = 0 := by simp [hy]
  have hX1 : (e' - C.top).1 ≠ 0 := by
    intro h; apply hee; exact point_ext (by sil at h) hy
  obtain ⟨-, -, hn1, hn2, -⟩ := C.sideTour_nbrs β
  rcases lt_or_gt_of_ne hX1 with hlt | hgt
  · -- west: the last position of the tour
    refine ⟨2 * C.m + 6, 0, by rwo [sideWalk_n], le_rfl, one_pos, ?_, ?_⟩
    · rw [sidePt_zero, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
    · rw [C.sideLeft_tour_last β]
      unfold sideLeftOf
      have hB2 : (C.sideTour β (2 * C.m - 1) - C.top).2 ≤ 0 := by
        simp only [Prod.snd_sub, sideTour]
        linarith [C.vertex_snd_le_top (C.sideIdx_le β (2 * C.m - 1))]
      refine sideCcw_west hU1 hU2 hX2 hlt hB2 (sub_ne_zero_of_ne' (C.sideTour_last_ne_top hP β)) ?_
      exact C.sideRay_free hP (j := C.topIdx) (j' := C.sideIdx β (2 * C.m - 1))
        (by rcases hn2 with h | h <;> omega) hT (C.sideIdx_le β _) (Ne.symm hee) hopen
  · -- east: the first position of the tour
    refine ⟨0 + 6, 0, by rwo [sideWalk_n], le_rfl, one_pos, ?_, ?_⟩
    · rw [sidePt_zero, C.sideWalk_vtx_tour β (by omega), sideTour_zero]
    · rw [C.sideLeft_tour_first β]
      unfold sideLeftOf
      have hA2 : (C.sideTour β 1 - C.top).2 ≤ 0 := by
        simp only [Prod.snd_sub, sideTour]; linarith [C.vertex_snd_le_top (C.sideIdx_le β 1)]
      refine sideCcw_east hU1 hU2 hX2 hgt hA2 (sub_ne_zero_of_ne' (C.sideTour_one_ne_top hP β)) ?_
      exact C.sideRay_free hP (j := C.topIdx) (j' := C.sideIdx β 1)
        (by rcases hn1 with h | h <;> omega) hT (C.sideIdx_le β _) (Ne.symm hee) hopen

omit C in
/-- The full-turn sector at a spike contains every direction off the ray of the spike. -/
theorem sideCcw_spike {A X : Point} (hA : A ≠ 0)
    (hray : ¬ (sideCross A X = 0 ∧ 0 ≤ sideDot A X)) : sideCcw A X A := by
  unfold sideCcw
  right; right; right
  refine ⟨sideCross_self A, sideDot_self_pos hA, ?_⟩
  by_contra h
  push Not at h
  exact hray ⟨h.1, h.2⟩

/-- At an inner chain vertex other than the top vertex: one of its two passages sees the
direction. -/
theorem sideSees_inner (hP : C.P.Simple) (β : Bool) {j : ℕ} (hj0 : 0 < j) (hjm : j < C.m)
    (hjT : j ≠ C.topIdx) {e' : Point} (hee : C.vertex j ≠ e')
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (C.vertex j) e' s ∈ C.dom) :
    SideSees (C.sideWalk β) (C.vertex j) e' := by
  have hm2 := C.two_m_pos
  have hA := sub_ne_zero_of_ne' (C.sideVertex_succ_ne hP j).symm
  have hB := sub_ne_zero_of_ne' (C.sideVertex_pred_ne hP hj0)
  have hns := (C.sideChain_nonSpike hP hj0 hjm).1
  have hXA := C.sideRay_free hP (j := j) (j' := j + 1) (Or.inl rfl) hjm.le hjm (Ne.symm hee) hopen
  have hXB := C.sideRay_free hP (j := j) (j' := j - 1) (Or.inr (by omega)) hjm.le (by omega)
    (Ne.symm hee) hopen
  rcases sideCcw_or hA hB hns hXA hXB with h | h
  · -- the forwards passage
    obtain ⟨i, hi, h1, h2, h3, h4⟩ := C.sideIdx_visit β (j := j) (by omega)
    have hi0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · exfalso; have := h3 h0; unfold sideE at this; split_ifs at this <;> omega
      · exact h0
    have k1 : C.sideIdx β i = j := by rw [h1]; unfold sideE; splao
    have k2 : C.sideIdx β (i + 1) = j + 1 := by rw [h2]; unfold sideE; splao
    have k3 : C.sideIdx β (i - 1) = j - 1 := by rw [h4 hi0]; unfold sideE; splao
    refine ⟨i + 6, 0, by rwo [sideWalk_n], le_rfl, one_pos, ?_, ?_⟩
    · rw [sidePt_zero, C.sideWalk_vtx_tour β hi.le]; unfold sideTour; rw [k1]
    · rw [C.sideLeft_tour_inner β hi0 hi]
      unfold sideTour; rw [k1, k2, k3]
      exact h
  · -- the backwards passage
    obtain ⟨i, hi, h1, h2, h3, h4⟩ := C.sideIdx_visit β (j := 2 * C.m - j) (by omega)
    have hi0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · exfalso; have := h3 h0; unfold sideE at this; split_ifs at this <;> omega
      · exact h0
    have k1 : C.sideIdx β i = j := by rw [h1]; unfold sideE; splao
    have k2 : C.sideIdx β (i + 1) = j - 1 := by rw [h2]; unfold sideE; splao
    have k3 : C.sideIdx β (i - 1) = j + 1 := by rw [h4 hi0]; unfold sideE; splao
    refine ⟨i + 6, 0, by rwo [sideWalk_n], le_rfl, one_pos, ?_, ?_⟩
    · rw [sidePt_zero, C.sideWalk_vtx_tour β hi.le]; unfold sideTour; rw [k1]
    · rw [C.sideLeft_tour_inner β hi0 hi]
      unfold sideTour; rw [k1, k2, k3]
      exact h

/-- At an endpoint of the chain other than the top vertex: the turnaround sees every direction
off the chain edge. -/
theorem sideSees_end (hP : C.P.Simple) (β : Bool) {j : ℕ} (hj : j = 0 ∨ j = C.m)
    (hjT : j ≠ C.topIdx) {e' : Point} (hee : C.vertex j ≠ e')
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (C.vertex j) e' s ∈ C.dom) :
    SideSees (C.sideWalk β) (C.vertex j) e' := by
  have hm := C.one_le
  have hm2 := C.two_m_pos
  obtain ⟨j', hj', hjj, hk2, hk3⟩ : ∃ j', j' ≤ C.m ∧ (j' = j + 1 ∨ j' + 1 = j) ∧
      (∀ i, sideE C.m (j + 1) = C.sideIdx β (i + 1) → C.sideIdx β (i + 1) = j') ∧
      (∀ i, sideE C.m (if j = 0 then 2 * C.m - 1 else j - 1) = C.sideIdx β (i - 1) →
        C.sideIdx β (i - 1) = j') := by
    rcases hj with rfl | rfl
    · refine ⟨1, hm, Or.inl rfl, fun i h => ?_, fun i h => ?_⟩ <;> rw [← h] <;> unfold sideE <;>
        split_ifs <;> omega
    · refine ⟨C.m - 1, by omega, Or.inr (by omega), fun i h => ?_, fun i h => ?_⟩ <;> rw [← h] <;>
        unfold sideE <;> split_ifs <;> omega
  obtain ⟨i, hi, h1, h2, h3, h4⟩ := C.sideIdx_visit β (j := j) (by omega)
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exfalso; have := h3 h0; unfold sideE at this; split_ifs at this <;> omega
    · exact h0
  have k1 : C.sideIdx β i = j := by rw [h1]; unfold sideE; splao
  have k2 := hk2 i h2.symm
  have k3 := hk3 i (h4 hi0).symm
  have hA := sub_ne_zero_of_ne' (show C.vertex j' ≠ C.vertex j by
    rcases hjj with rfl | rfl
    · exact (C.sideVertex_succ_ne hP j).symm
    · exact C.sideVertex_succ_ne hP j')
  have hX := C.sideRay_free hP hjj (by omega) hj' (Ne.symm hee) hopen
  refine ⟨i + 6, 0, by rwo [sideWalk_n], le_rfl, one_pos, ?_, ?_⟩
  · rw [sidePt_zero, C.sideWalk_vtx_tour β hi.le]; unfold sideTour; rw [k1]
  · rw [C.sideLeft_tour_inner β hi0 hi]
    unfold sideTour; rw [k1, k2, k3]
    exact sideCcw_spike hA hX

/-- A chain vertex sees every horizontal direction into the domain. -/
theorem sideSees_vertex (hP : C.P.Simple) (β : Bool) {j : ℕ} (hj : j ≤ C.m) {e' : Point}
    (hee : C.vertex j ≠ e') (hy : (C.vertex j).2 = e'.2)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (C.vertex j) e' s ∈ C.dom) :
    SideSees (C.sideWalk β) (C.vertex j) e' := by
  by_cases hjT : j = C.topIdx
  · subst hjT
    exact C.sideSees_top hP β hee hy hopen
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · exact C.sideSees_end hP β (Or.inl h0) hjT hee hopen
  rcases lt_or_eq_of_le hj with hjm | hjm
  · exact C.sideSees_inner hP β h0 hjm hjT hee hopen
  · exact C.sideSees_end hP β (Or.inr hjm) hjT hee hopen

/-- A point inside a chain edge: one of the two passages along the edge sees the direction. -/
theorem sideSees_open (hP : C.P.Simple) (β : Bool) {k : ℕ} (hk : k < C.m) {s₀ : ℝ}
    (hs : s₀ ∈ Ioo (0 : ℝ) 1) {e' : Point} (hee : lerp (C.vertex k) (C.vertex (k + 1)) s₀ ≠ e')
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (lerp (C.vertex k) (C.vertex (k + 1)) s₀) e' s ∈ C.dom) :
    SideSees (C.sideWalk β) (lerp (C.vertex k) (C.vertex (k + 1)) s₀) e' := by
  have hm2 := C.two_m_pos
  have hne := C.sideVertex_succ_ne hP k
  have hdet : det (C.vertex k) (C.vertex (k + 1)) e' ≠ 0 := by
    intro h0
    have hc : sideCross (C.vertex (k + 1) - C.vertex k)
        (e' - lerp (C.vertex k) (C.vertex (k + 1)) s₀) = 0 := by
      have e : sideCross (C.vertex (k + 1) - C.vertex k)
          (e' - lerp (C.vertex k) (C.vertex (k + 1)) s₀) = det (C.vertex k) (C.vertex (k + 1)) e' := by
        unfold sideCross det; sir only [Prod.fst_sub, Prod.snd_sub, lerp_fst, lerp_snd]
      rw [e, h0]
    obtain ⟨s, hs', t, ht0, ht1, ht⟩ := side_overlap hne hs.1.le hs.2 rfl (Ne.symm hee) hc
      (fun h => absurd h hs.1.ne')
    have hset : lerp (lerp (C.vertex k) (C.vertex (k + 1)) s₀) e' s ∈ C.set := by
      rw [ht]; exact C.sideLerp_mem_set (Or.inl rfl) hk.le hk ht0 ht1
    exact C.not_mem_set_of_mem_dom (hopen s hs') hset
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- the backwards passage
    obtain ⟨i, hi, h1, h2, -, -⟩ := C.sideIdx_visit β (j := 2 * C.m - 1 - k) (by omega)
    have k1 : C.sideIdx β i = k + 1 := by rw [h1]; unfold sideE; splao
    have k2 : C.sideIdx β (i + 1) = k := by rw [h2]; unfold sideE; splao
    have hv : (C.sideWalk β).vtx (i + 6) = C.vertex (k + 1) := by
      rw [C.sideWalk_vtx_tour β hi.le]; unfold sideTour; rw [k1]
    have hv' : (C.sideWalk β).vtx ((i + 6 + 1) % (C.sideWalk β).n) = C.vertex k := by
      rw [C.sideWalk_next_tour β hi, C.sideWalk_vtx_tour β (by omega)]; unfold sideTour; rw [k2]
    have ht : 1 - s₀ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    refine ⟨i + 6, 1 - s₀, by rwo [sideWalk_n], ht.1.le, ht.2, ?_, ?_⟩
    · unfold sidePt; rw [hv, hv']
      apply point_ext <;> simp only [lerp_fst, lerp_snd] <;> ring
    · rw [sideLeft_edge (by rw [hv, hv']; exact hne.symm) ht, hv, hv', Geometry.det_swap12]
      linarith
  · -- the forwards passage
    obtain ⟨i, hi, h1, h2, -, -⟩ := C.sideIdx_visit β (j := k) (by omega)
    have k1 : C.sideIdx β i = k := by rw [h1]; unfold sideE; splao
    have k2 : C.sideIdx β (i + 1) = k + 1 := by rw [h2]; unfold sideE; splao
    have hv : (C.sideWalk β).vtx (i + 6) = C.vertex k := by
      rw [C.sideWalk_vtx_tour β hi.le]; unfold sideTour; rw [k1]
    have hv' : (C.sideWalk β).vtx ((i + 6 + 1) % (C.sideWalk β).n) = C.vertex (k + 1) := by
      rw [C.sideWalk_next_tour β hi, C.sideWalk_vtx_tour β (by omega)]; unfold sideTour; rw [k2]
    refine ⟨i + 6, s₀, by rwo [sideWalk_n], hs.1.le, hs.2, ?_, ?_⟩
    · unfold sidePt; rw [hv, hv']
    · rw [sideLeft_edge (by rwx [hv, hv']) hs, hv, hv']
      exact hpos

/-- A point of an open vertical side of the box sees the horizontal direction into the box. -/
theorem sideSees_box (β : Bool) {e e' : Point}
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ C.dom) (he1 : |e.1| = C.radius)
    (he2 : |e.2| < C.radius) : SideSees (C.sideWalk β) e e' := by
  have hR := C.radius_pos
  have hmid := (hopen (1 / 2) ⟨by norm_num, by norm_num⟩).1
  have hmid1 := abs_lt.1 hmid.1
  simp only [lerp_fst] at hmid1
  have he2' := abs_lt.1 he2
  have hn := C.sideWalk_n β
  rcases (abs_eq hR.le).1 he1 with h | h
  · -- the right side, going up
    have hp : (3 + 1) % (C.sideWalk β).n = 4 := by rw [hn]; exact Nat.mod_eq_of_lt (by omega)
    have ht : (e.2 + C.radius) / (2 * C.radius) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · apply div_pos <;> linarith
      · rwli [div_lt_one (by linarith)]
    have he' : e'.1 < C.radius := by rw [h] at hmid1; linarith [hmid1.2]
    refine ⟨3, (e.2 + C.radius) / (2 * C.radius), by rwo [hn], ht.1.le, ht.2, ?_, ?_⟩
    · unfold sidePt; rw [hp, sideWalk_vtx_three, sideWalk_vtx_four]
      apply point_ext
      · simp only [lerp_fst]; rwring [h]
      · simp only [lerp_snd]
        rw [show C.radius - -C.radius = 2 * C.radius by ring,
          div_mul_cancel₀ _ (by positivity : (2 * C.radius) ≠ 0)]
        ring
    · have hne : (C.sideWalk β).vtx 3 ≠ (C.sideWalk β).vtx ((3 + 1) % (C.sideWalk β).n) := by
        rw [hp, sideWalk_vtx_three, sideWalk_vtx_four]
        intro h'; have := congrArg Prod.snd h'; sil only at this
      rw [sideLeft_edge hne ht, hp, sideWalk_vtx_three, sideWalk_vtx_four]
      unfold det; simp only
      nlinarith
  · -- the left side, going down
    have hp : (1 + 1) % (C.sideWalk β).n = 2 := by rw [hn]; exact Nat.mod_eq_of_lt (by omega)
    have ht : (C.radius - e.2) / (2 * C.radius) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · apply div_pos <;> linarith
      · rwli [div_lt_one (by linarith)]
    have he' : -C.radius < e'.1 := by rw [h] at hmid1; linarith [hmid1.1]
    refine ⟨1, (C.radius - e.2) / (2 * C.radius), by rwo [hn], ht.1.le, ht.2, ?_, ?_⟩
    · unfold sidePt; rw [hp, sideWalk_vtx_one, sideWalk_vtx_two]
      apply point_ext
      · simp only [lerp_fst]; rwring [h]
      · simp only [lerp_snd]
        rw [show -C.radius - C.radius = -(2 * C.radius) by ring, mul_neg,
          div_mul_cancel₀ _ (by positivity : (2 * C.radius) ≠ 0)]
        ring
    · have hne : (C.sideWalk β).vtx 1 ≠ (C.sideWalk β).vtx ((1 + 1) % (C.sideWalk β).n) := by
        rw [hp, sideWalk_vtx_one, sideWalk_vtx_two]
        intro h'; have := congrArg Prod.snd h'; sil only at this
      rw [sideLeft_edge hne ht, hp, sideWalk_vtx_one, sideWalk_vtx_two]
      unfold det; simp only
      nlinarith

/-- **Every endpoint of a chord is seen by some position of the corrected walk**: for a
horizontal segment `[e, e']` whose open part lies in the domain and whose endpoint `e` lies on
the chain or on an open vertical side of the box, some position of `C.sideWalk β` at `e` has `e'`
in its open left sector. -/
theorem sideSees_chordEnd (hP : C.P.Simple) (β : Bool) {e e' : Point} (hee : e ≠ e')
    (hy : e.2 = e'.2) (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ C.dom)
    (he : e ∈ C.set ∨ (|e.1| = C.radius ∧ |e.2| < C.radius)) : SideSees (C.sideWalk β) e e' := by
  rcases he with he | ⟨he1, he2⟩
  · obtain ⟨k, hk, hmem⟩ := he
    rw [C.chainEdge_eq] at hmem
    obtain ⟨s₀, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hmem
    rcases hs0.lt_or_eq with hs0 | hs0
    · rcases hs1.lt_or_eq with hs1 | hs1
      · exact C.sideSees_open hP β hk ⟨hs0, hs1⟩ hee hopen
      · subst hs1
        rw [lerp_one] at hee hy hopen ⊢
        exact C.sideSees_vertex hP β hk hee hy hopen
    · subst hs0
      rw [lerp_zero] at hee hy hopen ⊢
      exact C.sideSees_vertex hP β hk.le hee hy hopen
  · exact C.sideSees_box β hopen he1 he2

/-! ### The winding number of the corrected walk -/

/-! ### The split walks of the corrected walk at a chord -/

end

end Chazelle.Chain
