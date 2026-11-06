module

public import Chazelle.Core.BruteWeight
public import Chazelle.Core.FuseMathCut
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-K: the corners of the walk of a chain model and the orientation bit

The brute-force procedure decides, at each walk vertex of the double-boundary tour, which
horizontal directions leave the vertex into its left sector (the vertex chords attached there),
and it computes the orientation bit `sideBeta` of the chain descriptor.  Both reduce to sign tests
of the sign kernel:

* `sideCcw_horiz`: a horizontal direction `(σ, 0)` lies in the counterclockwise arc from `B` to
  `A` (both non-horizontal) iff, when `A` and `B` point to the same vertical side, the arc is not
  convex (`sideCross B A ≤ 0`, both horizontal directions), and otherwise iff `σ = 1 ↔ B.2 < 0`;
* `corner_iff`: at the tour position `i ≤ 2m` (walk vertex `i + 6`), the direction `σ` is in the
  left sector iff `emitR (prevPt i) v (nextPt i) σ` (heights of the two walk neighbours and one
  orientation);
* `sideBeta_iff`: the orientation bit as a combination of abscissa, height and orientation tests.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf sidePt SideAttach)
open Chazelle.Visibility (rayPt OpenEdgePt)

namespace Brute

/-! ## Horizontal directions in an arc of directions -/

theorem sideDot_key {A B : Point} (h : sideCross B A = 0) :
    sideDot B A * A.2 = B.2 * (A.1 ^ 2 + A.2 ^ 2) := by
  unfold sideCross at h; unfold sideDot
  have : B.1 * A.2 = B.2 * A.1 := by linarith
  linear_combination A.1 * this

theorem sideCcw_horiz_same {A B : Point} (hAB : 0 < A.2 * B.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    sideCcw B ((σ, 0) : Point) A ↔ sideCross B A ≤ 0 := by
  have eBX : sideCross B ((σ, 0) : Point) = -σ * B.2 := by ufring sideCross
  have eXA : sideCross ((σ, 0) : Point) A = σ * A.2 := by ufring sideCross
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hA0 : A.2 ≠ 0 := by rintro h; rw [h, zero_mul] at hAB; exact lt_irrefl _ hAB
  have hB0 : B.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hAB; exact lt_irrefl _ hAB
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  unfold sideCcw
  rw [eBX, eXA]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
    · exfalso
      have := mul_pos h2 h3
      nlinarith
    · exact h1.le
    · exact h1.le
    · exact h1.le
  · intro h
    rcases h.lt_or_eq with h | h
    · right; left
      refine ⟨h, ?_⟩
      by_contra hc
      push Not at hc
      have h1 : -σ * B.2 * (σ * A.2) = -(A.2 * B.2) := by nlinarith
      have h2  := mul_ne_zero (neg_ne_zero.2 hσ0) hB0
      have h3  := mul_ne_zero hσ0 hA0
      have h4  := lt_of_le_of_ne hc.1 h2
      have h5  := lt_of_le_of_ne hc.2 h3
      nlinarith [mul_pos_of_neg_of_neg h4 h5]
    · right; right; right
      have hk := sideDot_key h
      have hpos : 0 < A.1 ^ 2 + A.2 ^ 2 := by positivity
      refine ⟨h, ?_, Or.inl (mul_ne_zero (neg_ne_zero.2 hσ0) hB0)⟩
      by_contra hd
      push Not at hd
      have : sideDot B A * A.2 * A.2 ≤ 0 ∨ True := Or.inr trivial
      rcases lt_or_gt_of_ne hA0 with ha | ha
      · have hb : B.2 < 0 := by
          by_contra hb; push Not at hb
          have := hb.lt_or_eq; rcases this with hb | hb
          · nlinarith
          · exact hB0 hb.symm
        nlinarith [mul_neg_of_neg_of_pos hb hpos]
      · have hb : 0 < B.2 := by
          by_contra hb; push Not at hb
          rcases hb.lt_or_eq with hb | hb
          · nlinarith
          · exact hB0 hb
        nlinarith [mul_pos hb hpos]

theorem sideCcw_horiz_opp {A B : Point} (hAB : A.2 * B.2 < 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    sideCcw B ((σ, 0) : Point) A ↔ 0 < -σ * B.2 := by
  have eBX : sideCross B ((σ, 0) : Point) = -σ * B.2 := by ufring sideCross
  have eXA : sideCross ((σ, 0) : Point) A = σ * A.2 := by ufring sideCross
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hA0 : A.2 ≠ 0 := by rintro h; rw [h, zero_mul] at hAB; exact lt_irrefl _ hAB
  have hpos : 0 < A.1 ^ 2 + A.2 ^ 2 := by positivity
  have hsame : 0 < σ * A.2 → 0 < -σ * B.2 := by
    intro h
    have : σ * A.2 * (-σ * B.2) = -(A.2 * B.2) := by nlinarith
    by_contra hc; push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h.le hc]
  have hsame' : 0 < -σ * B.2 → 0 < σ * A.2 := by
    intro h
    have : σ * A.2 * (-σ * B.2) = -(A.2 * B.2) := by nlinarith
    by_contra hc; push Not at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h.le]
  unfold sideCcw
  rw [eBX, eXA]
  constructor
  · rintro (⟨-, h2, -⟩ | ⟨-, h2 | h2⟩ | ⟨-, -, h2⟩ | ⟨h1, h2, -⟩)
    · exact h2
    · exact h2
    · exact hsame h2
    · exact h2
    · exfalso
      have hk := sideDot_key h1
      rcases lt_or_gt_of_ne hA0 with ha | ha
      · have hb : 0 < B.2 := by nlinarith
        nlinarith [mul_pos hb hpos]
      · have hb : B.2 < 0 := by nlinarith
        nlinarith [mul_neg_of_neg_of_pos hb hpos]
  · intro h
    rcases lt_trichotomy (sideCross B A) 0 with h1 | h1 | h1
    · exact Or.inr (Or.inl ⟨h1, Or.inl h⟩)
    · right; right; left
      refine ⟨h1, ?_, h⟩
      have hk := sideDot_key h1
      rcases lt_or_gt_of_ne hA0 with ha | ha
      · have hb : 0 < B.2 := by nlinarith
        nlinarith [mul_pos hb hpos]
      · have hb : B.2 < 0 := by nlinarith
        nlinarith [mul_neg_of_neg_of_pos hb hpos]
    · exact Or.inl ⟨h1, h, hsame' h⟩

/-- The emission rule at a corner `a → v → b` for the horizontal direction `σ`. -/
def emitR (a v b : Point) (σ : ℝ) : Prop :=
  if (v.2 < a.2 ↔ v.2 < b.2) then ¬ 0 < det a v b else (σ = 1 ↔ b.2 < v.2)

/-- **The horizontal directions in the left sector of a corner** whose neighbours are at other
heights. -/
theorem sideLeftOf_horiz {a v b : Point} (ha : a.2 ≠ v.2) (hb : b.2 ≠ v.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : sideLeftOf a v b (rayPt v σ 1) ↔ emitR a v b σ := by
  unfold sideLeftOf emitR
  rw [FuseMath.rayPt_sub_one]
  have hA : (a - v).2 = a.2 - v.2 := rfl
  have hB : (b - v).2 = b.2 - v.2 := rfl
  have hA0 : a.2 - v.2 ≠ 0 := sub_ne_zero.2 ha
  have hB0 : b.2 - v.2 ≠ 0 := sub_ne_zero.2 hb
  by_cases hs : (v.2 < a.2 ↔ v.2 < b.2)
  · rw [ite_eq_left hs]
    have hAB : 0 < (a - v).2 * (b - v).2 := by
      rw [hA, hB]
      rcases lt_or_gt_of_ne hA0 with h1 | h1
      · have : b.2 - v.2 < 0 := by
          by_contra h; push Not at h
          rcases h.lt_or_eq with h | h
          · exact absurd (hs.2 (by linarith)) (by linarith)
          · exact hB0 h.symm
        exact mul_pos_of_neg_of_neg h1 this
      · have : 0 < b.2 - v.2 := by
          by_contra h; push Not at h
          rcases h.lt_or_eq with h | h
          · exact absurd (hs.1 (by linarith)) (by linarith)
          · exact hB0 h
        exact mul_pos h1 this
    rw [sideCcw_horiz_same hAB hσ, Chain.sideCross_corner]
    exact not_lt.symm
  · rw [ite_eq_right hs]
    have hAB : (a - v).2 * (b - v).2 < 0 := by
      rw [hA, hB]
      rcases lt_or_gt_of_ne hA0 with h1 | h1
      · have : 0 < b.2 - v.2 := by
          by_contra h; push Not at h
          rcases h.lt_or_eq with h | h
          · exact hs ⟨fun h' => by linarith, fun h' => by linarith⟩
          · exact hB0 h
        exact mul_neg_of_neg_of_pos h1 this
      · have : b.2 - v.2 < 0 := by
          by_contra h; push Not at h
          rcases h.lt_or_eq with h | h
          · exact hs ⟨fun _ => by linarith, fun _ => by linarith⟩
          · exact hB0 h.symm
        exact mul_neg_of_pos_of_neg h1 this
    rw [sideCcw_horiz_opp hAB hσ, hB]
    rcases hσ with rfl | rfl
    · constructor
      · intro h; exact ⟨fun _ => by linarith, fun _ => rfl⟩
      · intro h; linarith [h.1 rfl]
    · have hne : ((-1 : ℝ) = 1) ↔ False := by norm_num
      rw [hne]
      constructor
      · intro h; sil only [false_iff, not_lt]
      · intro h
        simp [false_iff, not_lt] at h
        rcases h.lt_or_eq with h' | h'
        · linarith
        · exact absurd h'.symm hb

/-! ## The corners of the walk of a chain model -/

variable {C : Chain}

/-- The chain vertex at tour position `i`. -/
noncomputable def vPt (C : Chain) (i : ℕ) : Point := C.vertex (C.sideIdx C.sideBeta i)

/-- The walk vertex before tour position `i` (the top of the slit before position `0`). -/
noncomputable def prevPt (C : Chain) (i : ℕ) : Point :=
  if i = 0 then C.slitTop else C.vertex (C.sideIdx C.sideBeta (i - 1))

/-- The walk vertex after tour position `i` (the top of the slit after position `2m`). -/
noncomputable def nextPt (C : Chain) (i : ℕ) : Point :=
  if i = 2 * C.m then C.slitTop else C.vertex (C.sideIdx C.sideBeta (i + 1))

theorem walk_vtx_tour {i : ℕ} (hi : i ≤ 2 * C.m) : (chainModel C).W.vtx (i + 6) = vPt C i :=
  C.sideWalk_vtx_tour C.sideBeta hi

theorem walk_n : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n C.sideBeta

theorem walk_prev {i : ℕ} (hi : i ≤ 2 * C.m) :
    (chainModel C).W.vtx ((i + 6 + (chainModel C).W.n - 1) % (chainModel C).W.n) = prevPt C i := by
  rw [walk_n, show i + 6 + (2 * C.m + 7) - 1 = (i + 5) + (2 * C.m + 7) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  unfold prevPt
  split_ifs with h
  · subst h; rfl
  · rw [show i + 5 = (i - 1) + 6 by omega]; exact C.sideWalk_vtx_tour _ (by omega)

theorem walk_next {i : ℕ} (hi : i ≤ 2 * C.m) :
    (chainModel C).W.vtx ((i + 6 + 1) % (chainModel C).W.n) = nextPt C i := by
  unfold nextPt
  split_ifs with h
  · subst h; exact C.sideWalk_vtx_wrap C.sideBeta
  · rw [walk_n, Nat.mod_eq_of_lt (by omega), show i + 6 + 1 = (i + 1) + 6 by ring]
    exact C.sideWalk_vtx_tour _ (by omega)

theorem vPt_zero : vPt C 0 = C.top := C.sideTour_zero _

theorem vPt_two_m : vPt C (2 * C.m) = C.top := C.sideTour_two_m _

/-- Consecutive tour vertices are at different heights. -/
theorem vPt_succ_ne (hDH : DistinctHeights C.P) (i : ℕ) : (vPt C (i + 1)).2 ≠ (vPt C i).2 := by
  have hl := C.sideIdx_le C.sideBeta i
  have hl' := C.sideIdx_le C.sideBeta (i + 1)
  have hs := C.sideTour_step C.sideBeta i
  exact ChainObs.vertex_snd_ne hDH hl' hl (by rcases hs with h | h <;> omega)

theorem prevPt_ne (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m) :
    (prevPt C i).2 ≠ (vPt C i).2 := by
  unfold prevPt
  split_ifs with h
  · subst h; rw [vPt_zero]; exact ne_of_gt C.top_snd_lt_radius
  · have := vPt_succ_ne hDH (i - 1)
    rw [show i - 1 + 1 = i by omega] at this
    exact this.symm

theorem nextPt_ne (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m) :
    (nextPt C i).2 ≠ (vPt C i).2 := by
  unfold nextPt
  split_ifs with h
  · subst h; rw [vPt_two_m]; exact ne_of_gt C.top_snd_lt_radius
  · exact vPt_succ_ne hDH i

/-- **The horizontal directions leaving the walk vertex `i + 6` into its left sector.** -/
theorem corner_iff (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    sideLeft (chainModel C).W (i + 6) 0 (rayPt (vPt C i) σ 1) ↔
      emitR (prevPt C i) (vPt C i) (nextPt C i) σ := by
  rw [Chain.sideLeft_zero, walk_prev hi, walk_vtx_tour hi, walk_next hi]
  exact sideLeftOf_horiz (prevPt_ne hDH hi) (nextPt_ne hDH hi) hσ

/-- At tour position `0` only the direction east is emitted. -/
theorem emitR_zero (hDH : DistinctHeights C.P) {σ : ℝ} :
    emitR (prevPt C 0) (vPt C 0) (nextPt C 0) σ ↔ σ = 1 := by
  have hn : (nextPt C 0).2 < (vPt C 0).2 := by
    have hne := nextPt_ne hDH (C := C) (i := 0) (by omega)
    have : (nextPt C 0).2 ≤ C.top.2 := by
      unfold nextPt; rw [ite_eq_right (by have := C.one_le; omega)]
      exact C.vertex_snd_le_top (C.sideIdx_le _ _)
    rw [vPt_zero] at hne ⊢
    exact lt_of_le_of_ne this hne
  have hp : (vPt C 0).2 < (prevPt C 0).2 := by
    rw [vPt_zero]; unfold prevPt; rw [ite_eq_left rfl]; exact C.top_snd_lt_radius
  unfold emitR
  rw [ite_eq_right (fun h => absurd (h.1 hp) (not_lt.2 hn.le))]
  exact ⟨fun h => h.2 hn, fun h => ⟨fun _ => hn, fun _ => h⟩⟩

/-- At tour position `2m` only the direction west is emitted. -/
theorem emitR_two_m (hDH : DistinctHeights C.P) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    emitR (prevPt C (2 * C.m)) (vPt C (2 * C.m)) (nextPt C (2 * C.m)) σ ↔ σ = -1 := by
  have hp : (prevPt C (2 * C.m)).2 < (vPt C (2 * C.m)).2 := by
    have hne := prevPt_ne hDH (C := C) (i := 2 * C.m) le_rfl
    have : (prevPt C (2 * C.m)).2 ≤ C.top.2 := by
      unfold prevPt; rw [ite_eq_right (by have := C.one_le; omega)]
      exact C.vertex_snd_le_top (C.sideIdx_le _ _)
    rw [vPt_two_m] at hne ⊢
    exact lt_of_le_of_ne this hne
  have hn : (vPt C (2 * C.m)).2 < (nextPt C (2 * C.m)).2 := by
    rw [vPt_two_m]; unfold nextPt; rw [ite_eq_left rfl]; exact C.top_snd_lt_radius
  unfold emitR
  rw [ite_eq_right (fun h => absurd (h.2 hn) (not_lt.2 hp.le))]
  rcases hσ with rfl | rfl
  · exact ⟨fun h => absurd (h.1 rfl) (not_lt.2 hn.le), fun h => by norm_num at h⟩
  · exact ⟨fun _ => rfl, fun _ => ⟨fun h => by norm_num at h, fun h => absurd h (not_lt.2 hn.le)⟩⟩

/-! ## Positions of the walk at a chain vertex -/

/-- **A position of the walk at a chain vertex is a tour vertex** (parameter `0`). -/
theorem pos_of_vertex (hP : C.P.Simple) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel C).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (hk : k ≤ C.m)
    (h : sidePt (chainModel C).W p t = C.vertex k) :
    t = 0 ∧ ∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ C.sideIdx C.sideBeta i = k := by
  have hn := walk_n (C := C)
  rw [hn] at hp
  have hbox := (Chain.mem_box_iff.1 (C.set_subset_box (C.vertex_mem_set hk)))
  have hR := C.radius_pos
  have htop := C.top_snd_lt_radius
  have hvt := C.vertex_snd_le_top hk
  have habs1 := abs_lt.1 hbox.1
  have habs2 := abs_lt.1 hbox.2
  unfold sidePt at h
  rw [hn] at h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp [Geometry.lerp_fst, Geometry.lerp_snd] at hx hy
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [hW] at hx hy h
  have hwrap := C.sideWalk_vtx_wrap C.sideBeta
  rw [C.sideWalk_n] at hwrap
  have h6 : (C.sideWalk C.sideBeta).vtx 6 = C.top := by
    rw [show (6 : ℕ) = 0 + 6 from rfl, C.sideWalk_vtx_tour _ (by omega), C.sideTour_zero]
  by_cases hp6 : p < 6
  · exfalso
    interval_cases p
    · rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_zero, C.sideWalk_vtx_one] at hy
      sil only [Chain.slitTop] at hy
    · rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_one, C.sideWalk_vtx_two] at hx
      sil only at hx
    · rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_two, C.sideWalk_vtx_three] at hy
      sil only at hy
    · rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hx
      sil only at hx
    · rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_four, C.sideWalk_vtx_five] at hy
      sil only [Chain.slitTop] at hy
    · rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 6 from rfl, h6] at hy
      simp [Chain.slitTop] at hy
      nlinarith
  by_cases hpl : p = 2 * C.m + 6
  · subst hpl
    rw [hwrap, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m] at hy
    simp [Chain.slitTop] at hy
    have ht : t = 0 := by
      by_contra hne
      have : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hne)
      nlinarith
    subst ht
    refine ⟨rfl, 2 * C.m, le_rfl, rfl, ?_⟩
    have e : C.top = C.vertex k := by
      have := h
      rw [C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m] at this
      simpa [Geometry.lerp] using this
    rw [C.sideIdx_two_m]
    exact C.sideVertex_inj hP C.topIdx_le hk e
  · set i := p - 6 with hi
    have hpi : p = i + 6 := by omega
    have hi2 : i < 2 * C.m := by omega
    rw [hpi] at h
    rw [Nat.mod_eq_of_lt (by omega), show i + 6 + 1 = (i + 1) + 6 by ring,
      C.sideWalk_vtx_tour _ (by omega), C.sideWalk_vtx_tour _ (by omega)] at h
    unfold Chain.sideTour at h
    set k₁ := C.sideIdx C.sideBeta i
    set k₂ := C.sideIdx C.sideBeta (i + 1)
    have hk₁ : k₁ ≤ C.m := C.sideIdx_le _ _
    have hk₂ : k₂ ≤ C.m := C.sideIdx_le _ _
    have ht : t = 0 := by
      by_contra hne
      have ht' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hne)
      -- the point is in the open part of a chain edge
      obtain ⟨kk, hkk, t', ht'0, ht'1, hlerp⟩ : ∃ kk, kk < C.m ∧ ∃ t', 0 < t' ∧ t' < 1 ∧
          Geometry.lerp (C.vertex k₁) (C.vertex k₂) t =
            Geometry.lerp (C.vertex kk) (C.vertex (kk + 1)) t' := by
        rcases C.sideTour_step C.sideBeta i with hs | hs
        · exact ⟨k₁, by omega, t, ht', ht1, by rw [show k₂ = k₁ + 1 from hs]⟩
        · refine ⟨k₂, by omega, 1 - t, by linarith, by linarith, ?_⟩
          rw [← Geometry.lerp_symm, show k₁ = k₂ + 1 by omega]
      have hopen : OpenEdgePt C.P (C.edgeIdx kk) (C.vertex k) := by
        refine ⟨t', ⟨ht'0, ht'1⟩, ?_⟩
        rw [← h, hlerp]
        unfold Chain.vertex
        rw [C.edgeIdx_succ]
      exact hopen.ne_vtx hP (C.edgeIdx_lt _) (C.edgeIdx_lt k) rfl
    subst ht
    refine ⟨rfl, i, hi2.le, hpi, ?_⟩
    have e : C.vertex k₁ = C.vertex k := by simpa [Geometry.lerp] using h
    exact C.sideVertex_inj hP hk₁ hk e

/-! ## The top index and the orientation bit -/

/-- The top index is the index of any topmost vertex (distinct heights). -/
theorem topIdx_eq_of_max (hDH : DistinctHeights C.P) {j : ℕ} (hj : j ≤ C.m)
    (htop : ∀ i, i ≤ C.m → (C.vertex i).2 ≤ (C.vertex j).2) : C.topIdx = j := by
  have h1 := C.topIdx_min hj htop
  have h2 := C.vertex_snd_le_top hj
  have h3 := htop C.topIdx C.topIdx_le
  by_contra hne
  exact ChainObs.vertex_snd_ne hDH C.topIdx_le hj hne (le_antisymm h3 h2)

/-- **The orientation bit** in terms of sign tests, for a top vertex that is not the first
vertex (`a` is the vertex before the top, `b` the one after; `b` may be outside the chain). -/
theorem sideCcw_up {a v b : Point} {h : ℝ} (hh : 0 < h) (ha : a.2 < v.2) (hb : b.2 ≠ v.2) :
    sideCcw (b - v) ((0 : ℝ), h) (a - v) ↔
      (0 < det a v b ∧ v.1 < b.1 ∧ a.1 < v.1) ∨ (det a v b < 0 ∧ (v.1 < b.1 ∨ a.1 < v.1)) ∨
      (det a v b = 0 ∧ v.2 < b.2 ∧ v.1 < b.1) ∨ (det a v b = 0 ∧ b.2 < v.2) := by
  have e1 : sideCross (b - v) (a - v) = det a v b := Chain.sideCross_corner a v b
  have e2 : sideCross (b - v) ((0 : ℝ), h) = h * (b.1 - v.1) := by
    unfold sideCross; sir only [Prod.fst_sub, Prod.snd_sub]
  have e3 : sideCross ((0 : ℝ), h) (a - v) = h * (v.1 - a.1) := by
    unfold sideCross; sir only [Prod.fst_sub, Prod.snd_sub]
  have e4 : sideDot (b - v) ((0 : ℝ), h) = h * (b.2 - v.2) := by
    unfold sideDot; sir only [Prod.fst_sub, Prod.snd_sub]
  have p2 : 0 < h * (b.1 - v.1) ↔ v.1 < b.1 := by
    constructor
    · intro hc; by_contra hc'; push Not at hc'; nlinarith
    · intro hc; exact mul_pos hh (by linarith)
  have p3 : 0 < h * (v.1 - a.1) ↔ a.1 < v.1 := by
    constructor
    · intro hc; by_contra hc'; push Not at hc'; nlinarith
    · intro hc; exact mul_pos hh (by linarith)
  have hA : (a - v).2 < 0 := by sil only [Prod.snd_sub]
  -- the dot product at a straight corner
  have hdot : det a v b = 0 → (sideDot (b - v) (a - v) < 0 ↔ v.2 < b.2) ∧
      (0 < sideDot (b - v) (a - v) ↔ b.2 < v.2) := by
    intro hd
    have hk := sideDot_key (A := a - v) (B := b - v) (by rwx [e1])
    have hpos : 0 < (a - v).1 ^ 2 + (a - v).2 ^ 2 := by nlinarith
    have hB : (b - v).2 = b.2 - v.2 := rfl
    rw [hB] at hk
    constructor
    · constructor
      · intro hc; by_contra hc'; push Not at hc'; nlinarith [mul_nonneg (sub_nonneg.2 hc') hpos.le]
      · intro hc; by_contra hc'; push Not at hc'
        nlinarith [mul_pos (sub_pos.2 hc) hpos, mul_nonpos_of_nonneg_of_nonpos hc' hA.le]
    · constructor
      · intro hc; by_contra hc'; push Not at hc'
        rcases hc'.lt_or_eq with hc' | hc'
        · nlinarith [mul_pos (sub_pos.2 hc') hpos]
        · exact hb hc'.symm
      · intro hc
        nlinarith [mul_neg_of_neg_of_pos (sub_neg.2 hc) hpos]
  unfold sideCcw
  rw [e1, e2, e3, e4, p2, p3]
  constructor
  · rintro (h1 | h1 | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, (hdot h1).1.1 h2, h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, (hdot h1).2.1 h2⟩))
  · rintro (h1 | h1 | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, (hdot h1).1.2 h2, h3⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨h1, (hdot h1).2.2 h2, Or.inr ?_⟩))
      nlinarith [mul_neg_of_pos_of_neg hh (sub_neg.2 h2)]

/-- The orientation bit is `false` when the top is the first vertex. -/
theorem sideBeta_of_top_zero (h0 : C.topIdx = 0) : C.sideBeta = false := by
  cases hb : C.sideBeta with
  | false => rfl
  | true =>
    have := C.sideBeta_eq_true_iff.1 hb
    rw [h0, show (0 : ℕ) - 1 = 0 from rfl] at this
    have e : C.vertex 0 - C.top = 0 := by unfold Chain.top; rw [h0, sub_self]
    rw [e] at this
    unfold sideCcw sideCross sideDot at this
    simp at this

/-- **The orientation bit** for a top vertex that is not the first vertex. -/
theorem sideBeta_iff (hDH : DistinctHeights C.P) (h0 : 0 < C.topIdx) :
    C.sideBeta = true ↔
      (0 < det (C.vertex (C.topIdx - 1)) C.top (C.vertex (C.topIdx + 1)) ∧
          C.top.1 < (C.vertex (C.topIdx + 1)).1 ∧ (C.vertex (C.topIdx - 1)).1 < C.top.1) ∨
        (det (C.vertex (C.topIdx - 1)) C.top (C.vertex (C.topIdx + 1)) < 0 ∧
          (C.top.1 < (C.vertex (C.topIdx + 1)).1 ∨ (C.vertex (C.topIdx - 1)).1 < C.top.1)) ∨
        (det (C.vertex (C.topIdx - 1)) C.top (C.vertex (C.topIdx + 1)) = 0 ∧
          C.top.2 < (C.vertex (C.topIdx + 1)).2 ∧ C.top.1 < (C.vertex (C.topIdx + 1)).1) ∨
        (det (C.vertex (C.topIdx - 1)) C.top (C.vertex (C.topIdx + 1)) = 0 ∧
          (C.vertex (C.topIdx + 1)).2 < C.top.2) := by
  rw [C.sideBeta_eq_true_iff]
  have hsl : C.slitTop - C.top = ((0 : ℝ), C.radius - C.top.2) := by
    unfold Chain.slitTop; ext <;> simp
  rw [hsl]
  have ha : (C.vertex (C.topIdx - 1)).2 < C.top.2 := by
    have hne := ChainObs.vertex_snd_ne hDH (j := C.topIdx - 1) (k := C.topIdx) (by
      have := C.topIdx_le; omega) C.topIdx_le (by omega)
    exact lt_of_le_of_ne (C.vertex_snd_le_top (by have := C.topIdx_le; omega)) hne
  have hb : (C.vertex (C.topIdx + 1)).2 ≠ C.top.2 := by
    intro e
    have hlt1 : C.edgeIdx (C.topIdx + 1) < C.P.n := C.edgeIdx_lt _
    have hlt2 : C.edgeIdx C.topIdx < C.P.n := C.edgeIdx_lt _
    refine hDH _ _ hlt1 hlt2 ?_ e
    intro e'
    have hs := C.edgeIdx_succ C.topIdx
    rw [e'] at hs
    have hx := C.edgeIdx_lt C.topIdx
    have hn : 2 ≤ C.P.n := by have := C.add_one_le; have := C.one_le; omega
    generalize C.edgeIdx C.topIdx = x at hs hx
    rcases Nat.lt_or_ge (x + 1) C.P.n with h1 | h1
    · rwo [Nat.mod_eq_of_lt h1] at hs
    · rwo [show x + 1 = C.P.n by omega, Nat.mod_self] at hs
  exact sideCcw_up (by linarith [C.top_snd_lt_radius]) ha hb

end Brute

end

end Chazelle.Core
