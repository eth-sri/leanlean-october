module

public import Chazelle.Golf

public import Chazelle.Core.WalkEmbedChain

/-!
# The glue points of the fusion are cuts (WP-D math, `design-merge-v2.md` §2.2–2.3)

Let `J` be a junction with union `C = J.whole`, shared vertex `v` and neighbours `u` (on `C₁`),
`w` (on `C₂`), and let `S' = J.fusion S₁ S₂ ∪ glueChords J`.  This file proves the *local* facts
about the walk `W` of the chain model of `C` on which the `γ + 1` bound rests.

* **Clean positions give free directions** (`freeAt_of_sideLeft`, `sideAttach_shoot`): if a
  horizontal direction leaves a position of the walk into its left sector, the ray is free and
  the chord shot along it is attached there.  All freeness facts below come from this.
* **The copies of the shared vertex** (`vkey_nbrs`): a walk vertex of `W` at `v` has its two
  walk neighbours among `u`, `w` and the top of the slit.
* **Every copy of `v` is a cut, except the inner copy of an extremum** (`vkey_cut_or_exc`,
  §2.2 (G1)): under `SharedGeneric` the left sector of a copy contains a horizontal direction —
  so a shared chord is attached there — unless the corner is `u → v → w` or `w → v → u`, turns
  left, and `v` is a local extremum.
* **The cap chord** (`exc_cap_cut`, §2.3): at such an inner copy the cap chord is attached on an
  adjacent walk edge, at a key within distance `1` of the copy.
* **There is at most one inner copy** (`exc_unique`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot SideClean)
open Chazelle.Visibility (rayPt)
open Chazelle.Geometry (lerp)

namespace FuseMath

/-! ## Free directions from the left sectors of the walk -/

theorem rayPt_sub (p : Point) (σ ε : ℝ) : rayPt p σ ε - p = ε • ((σ, 0) : Point) := by
  ext <;> simp [rayPt]; ring

theorem sideLeft_rayPt {W : Polygon} {p : ℕ} {t σ ε : ℝ} (hε : 0 < ε) :
    sideLeft W p t (rayPt (sidePt W p t) σ ε) ↔ sideLeft W p t (rayPt (sidePt W p t) σ 1) := by
  unfold sideLeft sideLeftOf
  Ξ rayPt_sub, rayPt_sub, one_smul, Chain.sideCcw_smul hε

theorem dist_rayPt (q : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {ε : ℝ} (hε : 0 ≤ ε) :
    dist (rayPt q σ ε) q = ε := by
  Ξ Prod.dist_eq
  ϴ rayPt, Real.dist_eq, sub_self, abs_zero
  rcases hσ with rfl | rfl
  · Θ abs_of_nonneg hε, hε
  · Θ abs_of_nonneg hε, hε

/-- **Clean positions give free directions**: if the horizontal direction `σ` leaves a position of
the walk of a chain model into its left sector, the ray from its point is free. -/
theorem freeAt_of_sideLeft {C : Chain} (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hl : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) σ 1)) :
    Merge.FreeAt C (sidePt (chainModel C).W p t) σ := by
  obtain ⟨r, hr, hcl⟩ := (walkAx_chainModel hP).clean p hp t ht ht1
  unfold Merge.FreeAt
  filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
  by_contra hnd
  refine hcl _ ?_ hnd ((sideLeft_rayPt hε.1).2 hl)
  Ξ mem_ball, dist_rayPt _ hσ hε.1.le
  exact hε.2

/-- **The chord shot along a free direction of a position is attached there.** -/
theorem sideAttach_shoot {C : Chain} (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hq : (sidePt (chainModel C).W p t).2 ≤ C.top.2)
    (hl : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) σ 1)) :
    Merge.FreeAt C (sidePt (chainModel C).W p t) σ ∧
      SideAttach (chainModel C).W (Merge.shoot C (sidePt (chainModel C).W p t) σ) p t := by
  have hfree := freeAt_of_sideLeft hP hp ht ht1 hσ hl
  refine ⟨hfree, ?_⟩
  obtain ⟨hpos, -, -⟩ := Merge.hit_of_freeAt C hq hσ hfree
  exact Chain.sideAttach_of_left hp ht ht1 rfl ((sideLeft_rayPt hpos).2 hl)

/-- The vertex-chord version: a horizontal direction in the left sector of a walk position at a
chain vertex is free, and the vertex chord is attached there. -/
theorem sideAttach_chordSet {C : Chain} (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n)
    {k : ℕ} (hk : k ≤ C.m) (hpt : sidePt (chainModel C).W p 0 = C.vertex k) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hl : sideLeft (chainModel C).W p 0 (rayPt (C.vertex k) σ 1)) :
    C.DirFree k σ ∧ SideAttach (chainModel C).W (C.chordSet k σ) p 0 := by
  Ξ' ← hpt at hl
  have h := sideAttach_shoot hP hp le_rfl zero_lt_one hσ
    (by rw [hpt]; exact C.vertex_snd_le_top hk) hl
  Ξ' hpt at h
  exact h

/-! ## Horizontal directions in a corner at the shared vertex -/

section Corner

variable {P N v : Point}

theorem det_rayPt_left (P v : Point) (σ : ℝ) : det P v (rayPt v σ 1) = σ * (P.2 - v.2) := by
  unfold det; simp only [rayPt]; ring

theorem det_rayPt_right (v N : Point) (σ : ℝ) : det v N (rayPt v σ 1) = -(σ * (N.2 - v.2)) := by
  unfold det; simp only [rayPt]; ring

theorem rayPt_sub_one (v : Point) (σ : ℝ) : rayPt v σ 1 - v = ((σ, 0) : Point) := by
  ext <;> Θ rayPt

/-- A full-turn corner contains the direction east when the neighbour is not at the same height. -/
theorem corner_full (h : P.2 ≠ v.2) : sideLeftOf P v P (rayPt v 1 1) := by
  unfold sideLeftOf sideCcw
  Ξ rayPt_sub_one
  right; right; right
  refine ⟨Chain.sideCross_self _, Chain.sideDot_self_pos (sub_ne_zero.2 fun e => h (e ▸ rfl)),
    Or.inl ?_⟩
  unfold sideCross
  ϴ Prod.fst_sub, Prod.snd_sub
  intro e
  apply h
  linarith

/-- Coming down the slit to a vertex whose next neighbour is lower: the sector contains east. -/
theorem corner_east {R : ℝ} (hR : v.2 < R) (hN : N.2 < v.2) :
    sideLeftOf ((v.1, R) : Point) v N (rayPt v 1 1) := by
  unfold sideLeftOf
  Ξ rayPt_sub_one
  refine Chain.sideCcw_east (✓) (by simp; linarith) rfl one_pos (by simp; linarith)
    (sub_ne_zero.2 fun e => by rw [e] at hN; exact lt_irrefl _ hN) ?_
  unfold sideCross
  ϴ Prod.fst_sub, Prod.snd_sub
  rintro ⟨h1, -⟩
  linarith

/-- Arriving at a vertex from a lower neighbour and going up the slit: the sector contains
west. -/
theorem corner_west {R : ℝ} (hR : v.2 < R) (hP : P.2 < v.2) :
    sideLeftOf P v ((v.1, R) : Point) (rayPt v (-1) 1) := by
  unfold sideLeftOf
  Ξ rayPt_sub_one
  refine Chain.sideCcw_west (✓) (by simp; linarith) rfl (⊛) (by simp; linarith)
    (sub_ne_zero.2 fun e => by rw [e] at hP; exact lt_irrefl _ hP) ?_
  unfold sideCross
  ϴ Prod.fst_sub, Prod.snd_sub
  rintro ⟨h1, -⟩
  linarith

/-- **A corner with neighbours off the horizontal line of the vertex** contains a horizontal
direction, unless it turns left with both neighbours on the same side (the inner corner of a
local extremum). -/
theorem corner_pair (hP : P.2 ≠ v.2) (hN : N.2 ≠ v.2) :
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ sideLeftOf P v N (rayPt v σ 1)) ∨
      (0 < det P v N ∧ 0 < (P.2 - v.2) * (N.2 - v.2)) := by
  rcases lt_trichotomy (det P v N) 0 with hneg | hzero | hpos
  · left
    rcases lt_or_gt_of_ne hN with hN' | hN'
    · refine ⟨1, Or.inl rfl, (Chain.sideLeftOf_iff_neg hneg).2 (Or.inl ?_)⟩
      rw [det_rayPt_left]; linarith
    · refine ⟨-1, Or.inr rfl, (Chain.sideLeftOf_iff_neg hneg).2 (Or.inl ?_)⟩
      rw [det_rayPt_left]; linarith
  · left
    have hB : N - v ≠ 0 := sub_ne_zero.2 fun e => hN (e ▸ rfl)
    have hA : P - v ≠ 0 := sub_ne_zero.2 fun e => hP (e ▸ rfl)
    have hcr : sideCross (N - v) (P - v) = 0 := by rw [Chain.sideCross_corner]; exact hzero
    have hdot : sideDot (N - v) (P - v) ≠ 0 := by
      intro hd
      have L := Chain.side_lagrange (N - v) (P - v)
      Ξ' hcr, hd at L
      have h1 := Chain.sideDot_self_pos hB
      have h2 := Chain.sideDot_self_pos hA
      nlinarith
    rcases lt_or_gt_of_ne hdot with hd | hd
    · rcases lt_or_gt_of_ne hN with hN' | hN'
      · refine ⟨1, Or.inl rfl, ?_⟩
        unfold sideLeftOf sideCcw
        Ξ rayPt_sub_one
        right; right; left
        refine ⟨hcr, hd, ?_⟩
        unfold sideCross; simp only [Prod.fst_sub, Prod.snd_sub]; linarith
      · refine ⟨-1, Or.inr rfl, ?_⟩
        unfold sideLeftOf sideCcw
        Ξ rayPt_sub_one
        right; right; left
        refine ⟨hcr, hd, ?_⟩
        unfold sideCross; simp only [Prod.fst_sub, Prod.snd_sub]; linarith
    · refine ⟨1, Or.inl rfl, ?_⟩
      unfold sideLeftOf sideCcw
      Ξ rayPt_sub_one
      right; right; right
      refine ⟨hcr, hd, Or.inl ?_⟩
      unfold sideCross; ϴ Prod.fst_sub, Prod.snd_sub
      intro e; apply hN; linarith
  · rcases lt_or_gt_of_ne hP with hP' | hP' <;> rcases lt_or_gt_of_ne hN with hN' | hN'
    · right; exact ⟨hpos, ⊞⟩
    · left
      refine ⟨-1, Or.inr rfl, (Chain.sideLeftOf_iff_pos hpos).2 ⟨?_, ?_⟩⟩
      · rw [det_rayPt_left]; linarith
      · rw [det_rayPt_right]; linarith
    · left
      refine ⟨1, Or.inl rfl, (Chain.sideLeftOf_iff_pos hpos).2 ⟨?_, ?_⟩⟩
      · rw [det_rayPt_left]; linarith
      · rw [det_rayPt_right]; linarith
    · right; exact ⟨hpos, ⊞⟩

/-- A full-turn corner at a vertex different from its neighbour contains a horizontal
direction. -/
theorem corner_full_ne (h : P ≠ v) : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ sideLeftOf P v P (rayPt v σ 1) := by
  by_cases h2 : P.2 = v.2
  · have h1 : P.1 ≠ v.1 := fun e => h (Prod.ext e h2)
    have hne := sub_ne_zero.2 h
    have hcr : ∀ σ : ℝ, sideCross (P - v) ((σ, 0) : Point) = 0 := by
      intro σ; unfold sideCross; simp only [Prod.fst_sub, Prod.snd_sub]; rw [h2]; ring
    rcases lt_or_gt_of_ne h1 with hl | hg
    · refine ⟨1, Or.inl rfl, ?_⟩
      unfold sideLeftOf sideCcw; Ξ rayPt_sub_one
      right; right; right
      refine ⟨Chain.sideCross_self _, Chain.sideDot_self_pos hne, Or.inr ?_⟩
      unfold sideDot; simp only [Prod.fst_sub, Prod.snd_sub]; linarith
    · refine ⟨-1, Or.inr rfl, ?_⟩
      unfold sideLeftOf sideCcw; Ξ rayPt_sub_one
      right; right; right
      refine ⟨Chain.sideCross_self _, Chain.sideDot_self_pos hne, Or.inr ?_⟩
      unfold sideDot; simp only [Prod.fst_sub, Prod.snd_sub]; linarith
  · exact ⟨1, Or.inl rfl, corner_full h2⟩

end Corner

/-! ## The copies of the shared vertex on the walk of `C` -/

section Shared

variable (J : Merge.Junction)

/-- The neighbours of a copy of the shared vertex on the walk of `C`: `u`, `w`, or the top of the
slit (then the shared vertex is the top of `C`). -/
theorem vkey_nbrs (hP : J.P.Simple) {k : ℕ} (hk : k < (chainModel J.whole).W.n)
    (hv : (chainModel J.whole).W.vtx k = sharedV J) :
    6 ≤ k ∧
    (sidePrev (chainModel J.whole).W k 0 = sharedU J ∨
      sidePrev (chainModel J.whole).W k 0 = sharedW J ∨
      (sidePrev (chainModel J.whole).W k 0 = J.whole.slitTop ∧ sharedV J = J.whole.top)) ∧
    (sideNext (chainModel J.whole).W k = sharedU J ∨ sideNext (chainModel J.whole).W k = sharedW J ∨
      (sideNext (chainModel J.whole).W k = J.whole.slitTop ∧ sharedV J = J.whole.top)) := by
  set C := J.whole with hC
  have hP' : C.P.Simple := hP
  have hm₁ : J.m₁ ≤ C.m := by rw [hC, Merge.Junction.whole_m]; omega
  have hvbox : sharedV J ∈ Chain.box C.radius := C.set_subset_box (C.vertex_mem_set hm₁)
  have hn := WalkEmbed.cm_n C
  Ξ' hn at hk
  have h6 : 6 ≤ k := by
    by_contra h
    Ξ' ← hv at hvbox
    Ξ' WalkEmbed.cm_W at hvbox
    interval_cases k
    · exact WalkEmbed.slitTop_not_mem_box C hvbox
    · exact WalkEmbed.corner_not_mem_box C (Or.inr rfl) hvbox
    · exact WalkEmbed.corner_not_mem_box C (Or.inr rfl) hvbox
    · exact WalkEmbed.corner_not_mem_box C (Or.inl rfl) hvbox
    · exact WalkEmbed.corner_not_mem_box C (Or.inl rfl) hvbox
    · exact WalkEmbed.slitTop_not_mem_box C hvbox
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 6 := ⟨k - 6, ⋄⟩
  have hi : i ≤ 2 * C.m := ⋄
  have hidx : C.sideIdx C.sideBeta i = J.m₁ := by
    Ξ' WalkEmbed.cm_W, C.sideWalk_vtx_tour _ hi at hv
    exact C.sideVertex_inj hP' (C.sideIdx_le _ _) hm₁ hv
  have hnb : ∀ j, (C.sideIdx C.sideBeta j = J.m₁ + 1 ∨ C.sideIdx C.sideBeta j + 1 = J.m₁) →
      C.vertex (C.sideIdx C.sideBeta j) = sharedU J ∨ C.vertex (C.sideIdx C.sideBeta j) = sharedW J := by
    intro j hj
    rcases hj with hj | hj
    · right; rw [hj]; rfl
    · left; rw [show C.sideIdx C.sideBeta j = J.m₁ - 1 by omega]; rfl
  refine ⟨⋄, ?_, ?_⟩
  · unfold sidePrev
    Ξ ite_eq_left rfl, WalkEmbed.cm_W
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · right; right
      Ξ C.sideWalk_prev_six, C.sideWalk_vtx_five
      refine ⟨rfl, ?_⟩
      Ξ ← hv, WalkEmbed.cm_W, zero_add, C.sideWalk_vtx_six
    · Ξ C.sideWalk_prev_tour _ hi0 hi, C.sideWalk_vtx_tour _ (⋄)
      have hs := C.sideTour_step C.sideBeta (i - 1)
      Ξ' Nat.sub_add_cancel hi0, hidx at hs
      rcases hnb (i - 1) (⋄) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · unfold sideNext
    Ξ WalkEmbed.cm_W
    rcases lt_or_eq_of_le hi with hi' | rfl
    · Ξ C.sideWalk_next_tour _ hi', C.sideWalk_vtx_tour _ (⋄)
      have hs := C.sideTour_step C.sideBeta i
      Ξ' hidx at hs
      rcases hnb (i + 1) (⋄) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · right; right
      Ξ C.sideWalk_next_last
      refine ⟨rfl, ?_⟩
      Ξ ← hv, WalkEmbed.cm_W, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m

/-- The inner-corner condition at a copy `k` of the shared vertex: the corner is `u → v → w` or
`w → v → u`, it turns left, and `v` is a local extremum. -/
def InnerCopy (k : ℕ) : Prop :=
  ((sidePrev (chainModel J.whole).W k 0 = sharedU J ∧ sideNext (chainModel J.whole).W k = sharedW J) ∨
    (sidePrev (chainModel J.whole).W k 0 = sharedW J ∧ sideNext (chainModel J.whole).W k = sharedU J)) ∧
  0 < det (sidePrev (chainModel J.whole).W k 0) (sharedV J) (sideNext (chainModel J.whole).W k) ∧
  SharedExtremum J

/-- **Every copy of the shared vertex is a cut of the revised fusion, except an inner copy**
(design doc §2.2 (G1)). -/
theorem vkey_cut_or_inner (hP : J.P.Simple) (hgen : SharedGeneric J) (S₁ S₂ : Set (Set Point))
    {k : ℕ} (hk : k < (chainModel J.whole).W.n) (hv : (chainModel J.whole).W.vtx k = sharedV J) :
    (chainModel J.whole).IsCut (J.fusion S₁ S₂ ∪ glueChords J) k ∨ InnerCopy J k := by
  set C := J.whole with hC
  have hP' : C.P.Simple := hP
  obtain ⟨-, hPr, hNx⟩ := vkey_nbrs J hP hk hv
  set W := (chainModel C).W with hW
  set Pr := sidePrev W k 0 with hPr_def
  set Nx := sideNext W k with hNx_def
  have hm₁ : J.m₁ ≤ C.m := by rw [hC, Merge.Junction.whole_m]; omega
  have hu := hgen.1
  have hw := hgen.2.1
  have hut : (sharedU J).2 ≤ C.top.2 := C.vertex_snd_le_top (j := J.m₁ - 1) (⋄)
  have hwt : (sharedW J).2 ≤ C.top.2 :=
    C.vertex_snd_le_top (j := J.m₁ + 1) (by rw [hC, Merge.Junction.whole_m]; have := J.one_le_m₂; omega)
  have hvt : (sharedV J).2 ≤ C.top.2 := C.vertex_snd_le_top hm₁
  have hR := C.top_snd_lt_radius
  -- the height of each neighbour differs from that of `v`
  have hne : ∀ X, (X = sharedU J ∨ X = sharedW J ∨ (X = C.slitTop ∧ sharedV J = C.top)) →
      X.2 ≠ (sharedV J).2 := by
    rintro X (rfl | rfl | ⟨rfl, -⟩)
    · exact hu
    · exact hw
    · show C.radius ≠ _; intro e; linarith
  -- a horizontal direction in the sector gives a cut
  have hcut : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → sideLeftOf Pr (sharedV J) Nx (rayPt (sharedV J) σ 1) →
      (chainModel C).IsCut (J.fusion S₁ S₂ ∪ glueChords J) k := by
    intro σ hσ hl
    have hpt : sidePt W k 0 = C.vertex J.m₁ := by rw [Chain.sidePt_zero]; exact hv
    have hl' : sideLeft W k 0 (rayPt (C.vertex J.m₁) σ 1) := by
      unfold sideLeft; rw [hpt]; exact hl
    obtain ⟨hfree, hA⟩ := sideAttach_chordSet hP' hk hm₁ hpt hσ hl'
    refine ⟨C.chordSet J.m₁ σ, Or.inl (Merge.Junction.sharedChords_subset_fusion J S₁ S₂
      ⟨σ, hσ, hfree, rfl⟩), k, 0, hA, ✓⟩
  by_cases hPN : Pr = Nx
  · left
    refine hcut 1 (Or.inl rfl) ?_
    Ξ ← hPN
    exact corner_full (hne _ hPr)
  rcases hPr with hPu | hPw | ⟨hPs, hvT⟩
  · rcases hNx with hNu | hNw | ⟨hNs, hvT⟩
    · exact absurd (hPu.trans hNu.symm) hPN
    · rcases corner_pair (hne _ (Or.inl hPu)) (hne _ (Or.inr (Or.inl hNw))) with ⟨σ, hσ, hl⟩ | hexc
      · exact Or.inl (hcut σ hσ hl)
      · right
        refine ⟨Or.inl ⟨hPu, hNw⟩, hexc.1, ?_⟩
        unfold SharedExtremum; rw [← hPu, ← hNw]; exact hexc.2
    · left
      refine hcut (-1) (Or.inr rfl) ?_
      Ξ hNs, show C.slitTop = ((sharedV J).1, C.radius) by rw [hvT]; rfl
      exact corner_west (by rw [hvT]; exact hR) (lt_of_le_of_ne (hvT ▸ hPu ▸ hut) (hne _ (Or.inl hPu)))
  · rcases hNx with hNu | hNw | ⟨hNs, hvT⟩
    · rcases corner_pair (hne _ (Or.inr (Or.inl hPw))) (hne _ (Or.inl hNu)) with ⟨σ, hσ, hl⟩ | hexc
      · exact Or.inl (hcut σ hσ hl)
      · right
        refine ⟨Or.inr ⟨hPw, hNu⟩, hexc.1, ?_⟩
        unfold SharedExtremum; rw [← hPw, ← hNu, mul_comm]; exact hexc.2
    · exact absurd (hPw.trans hNw.symm) hPN
    · left
      refine hcut (-1) (Or.inr rfl) ?_
      Ξ hNs, show C.slitTop = ((sharedV J).1, C.radius) by rw [hvT]; rfl
      exact corner_west (by rw [hvT]; exact hR) (lt_of_le_of_ne (hvT ▸ hPw ▸ hwt) (hne _ (Or.inr (Or.inl hPw))))
  · left
    have hN' : Nx.2 < (sharedV J).2 := by
      rcases hNx with hNu | hNw | ⟨hNs, -⟩
      · exact lt_of_le_of_ne (hvT ▸ hNu ▸ hut) (hne _ (Or.inl hNu))
      · exact lt_of_le_of_ne (hvT ▸ hNw ▸ hwt) (hne _ (Or.inr (Or.inl hNw)))
      · exact absurd (hPs.trans hNs.symm) hPN
    refine hcut 1 (Or.inl rfl) ?_
    Ξ hPs, show C.slitTop = ((sharedV J).1, C.radius) by rw [hvT]; rfl
    exact corner_east (by rw [hvT]; exact hR) hN'

/-- **There is at most one inner copy**: two inner copies have the same corner, hence overlapping
left sectors at the same point, so they are the same walk position (`Chain.sideWalk_disj`). -/
theorem inner_unique (hP : J.P.Simple) {k k' : ℕ} (hk : k < (chainModel J.whole).W.n)
    (hk' : k' < (chainModel J.whole).W.n) (hv : (chainModel J.whole).W.vtx k = sharedV J)
    (hv' : (chainModel J.whole).W.vtx k' = sharedV J) (h : InnerCopy J k) (h' : InnerCopy J k') :
    k = k' := by
  set C := J.whole with hC
  have hP' : C.P.Simple := hP
  set W := (chainModel C).W with hW
  obtain ⟨hc, hdet, -⟩ := h
  obtain ⟨hc', hdet', -⟩ := h'
  -- the same corner
  have hsame : sidePrev W k 0 = sidePrev W k' 0 ∧ sideNext W k = sideNext W k' := by
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hc' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
    · exfalso; Ξ' h1, h2 at hdet; Ξ' h3, h4 at hdet'
      Ξ' Geometry.det_swap13 at hdet'; linarith
    · exfalso; Ξ' h1, h2 at hdet; Ξ' h3, h4 at hdet'
      Ξ' Geometry.det_swap13 at hdet'; linarith
    · exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  by_contra hne
  set Pr := sidePrev W k 0
  set Nx := sideNext W k
  set v := sharedV J
  have hpt : sidePt W k 0 = v := by rw [Chain.sidePt_zero]; exact hv
  have hpt' : sidePt W k' 0 = v := by rw [Chain.sidePt_zero]; exact hv'
  have hleft : ∀ j, sidePt W j 0 = v → sidePrev W j 0 = Pr → sideNext W j = Nx →
      sideLeft W j 0 (Pr + Nx - v) := by
    intro j hj hp hn
    unfold sideLeft
    Ξ hj, hp, hn, Chain.sideLeftOf_iff_pos hdet
    constructor
    · have : det Pr v (Pr + Nx - v) = det Pr v Nx := by
        unfold det; simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
      rw [one_mul, this]; exact hdet
    · have : det v Nx (Pr + Nx - v) = det Pr v Nx := by
        unfold det; simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
      rw [one_mul, this]; exact hdet
  have hm₁ : J.m₁ ≤ C.m := by rw [hC, Merge.Junction.whole_m]; omega
  exact C.sideWalk_disj hP' (C.sideGood_sideBeta hP') hk le_rfl zero_lt_one hk' le_rfl zero_lt_one
    (fun e => absurd e.symm hne) (by show sidePt W k' 0 = sidePt W k 0; rw [hpt, hpt'])
    (Or.inl (by show sidePt W k 0 ∈ C.set; rw [hpt]; exact C.vertex_mem_set hm₁)) (Pr + Nx - v)
    ⟨hleft k hpt rfl rfl, hleft k' hpt' hsame.1.symm hsame.2.symm⟩

/-! ### The cap chord -/

omit J in
/-- The sign computation of the cap chord shot from the arm after the corner. -/
theorem cap_left_next {v N P : Point} {τ : ℝ} (hPc : P.2 = v.2 + τ * (N.2 - v.2))
    (hdet : 0 < det P v N) :
    0 < det v N (rayPt (lerp v N τ) (if P.1 < (lerp v N τ).1 then -1 else 1) 1) := by
  have key : det P v N = -(P.1 - (lerp v N τ).1) * (N.2 - v.2) := by
    unfold det; simp only [lerp]; rw [hPc]; ring
  have e : ∀ σ : ℝ, det v N (rayPt (lerp v N τ) σ 1) = -(σ * (N.2 - v.2)) := by
    intro σ; unfold det; simp only [lerp, rayPt]; ring
  Ξ e
  Ξ' key at hdet
  split_ifs with hlt
  · nlinarith
  · push Not at hlt
    rcases hlt.lt_or_eq with h1 | h1
    · nlinarith
    · Ξ' h1, sub_self at hdet; simp at hdet

omit J in
/-- The sign computation of the cap chord shot from the arm before the corner. -/
theorem cap_left_prev {v N P : Point} {τ : ℝ} (hNc : N.2 = v.2 + τ * (P.2 - v.2))
    (hdet : 0 < det P v N) :
    0 < det P v (rayPt (lerp v P τ) (if N.1 < (lerp v P τ).1 then -1 else 1) 1) := by
  have key : det P v N = (P.2 - v.2) * (N.1 - (lerp v P τ).1) := by
    unfold det; simp only [lerp]; rw [hNc]; ring
  have e : ∀ σ : ℝ, det P v (rayPt (lerp v P τ) σ 1) = σ * (P.2 - v.2) := by
    intro σ; unfold det; simp only [lerp, rayPt]; ring
  Ξ e
  Ξ' key at hdet
  split_ifs with hlt
  · nlinarith
  · push Not at hlt
    rcases hlt.lt_or_eq with h1 | h1
    · nlinarith
    · Ξ' h1, sub_self at hdet; simp at hdet

/-- The parameter of the cap origin on the far arm lies in `(0, 1)`, and the cap origin is at the
height of the near neighbour. -/
theorem cap_param (hgen : SharedGeneric J) (hext : SharedExtremum J) :
    let τ := ((capNear J).2 - (sharedV J).2) / ((capFar J).2 - (sharedV J).2)
    0 < τ ∧ τ < 1 ∧ (capNear J).2 = (sharedV J).2 + τ * ((capFar J).2 - (sharedV J).2) ∧
      ((capNear J = sharedU J ∧ capFar J = sharedW J) ∨
        (capNear J = sharedW J ∧ capFar J = sharedU J)) := by
  obtain ⟨hu, hw, huw⟩ := hgen
  unfold SharedExtremum at hext
  unfold capNear capFar
  set du := (sharedU J).2 - (sharedV J).2
  set dw := (sharedW J).2 - (sharedV J).2
  have hdu := sub_ne_zero.2 hu
  have hdw := sub_ne_zero.2 hw
  have hduw : du ≠ dw := fun e => huw (by simpa [du, dw] using e)
  split_ifs with h
  · intro τ
    refine ⟨?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · rcases lt_or_gt_of_ne hdw with hn | hp
      · exact div_pos_of_neg_of_neg (⊞) hn
      · exact div_pos (⊞) hp
    · rcases lt_or_gt_of_ne hdw with hn | hp
      · have hdu' : du < 0 := ⊞
        Ξ' abs_of_neg hdu', abs_of_neg hn at h
        exact (div_lt_one_of_neg hn).2 (⟡)
      · have hdu' : 0 < du := ⊞
        Ξ' abs_of_pos hdu', abs_of_pos hp at h
        exact (div_lt_one hp).2 h
    · show (sharedU J).2 = (sharedV J).2 + du / dw * dw
      rw [div_mul_cancel₀ _ hdw]; ring
  · intro τ
    refine ⟨?_, ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
    · rcases lt_or_gt_of_ne hdu with hn | hp
      · exact div_pos_of_neg_of_neg (⊞) hn
      · exact div_pos (⊞) hp
    · rcases lt_or_gt_of_ne hdu with hn | hp
      · have hdw' : dw < 0 := ⊞
        Ξ' abs_of_neg hdw', abs_of_neg hn at h
        exact (div_lt_one_of_neg hn).2 (lt_of_le_of_ne (⟡) hduw)
      · have hdw' : 0 < dw := ⊞
        Ξ' abs_of_pos hdw', abs_of_pos hp at h
        exact (div_lt_one hp).2 (lt_of_le_of_ne (⟡) (Ne.symm hduw))
    · show (sharedW J).2 = (sharedV J).2 + dw / du * du
      rw [div_mul_cancel₀ _ hdu]; ring

/-- **The cap chord is a cut next to the inner copy** (design doc §2.3): at the inner copy `k`
of the shared vertex, the cap chord is attached on the walk edge after `k` (key in `(k, k + 1)`)
or on the walk edge before `k` (key in `(k - 1, k)`). -/
theorem inner_cap_cut (hP : J.P.Simple) (hgen : SharedGeneric J) (S₁ S₂ : Set (Set Point))
    {k : ℕ} (hk : k < (chainModel J.whole).W.n) (hv : (chainModel J.whole).W.vtx k = sharedV J)
    (h : InnerCopy J k) :
    ∃ q : ℝ, (chainModel J.whole).IsCut (J.fusion S₁ S₂ ∪ glueChords J) q ∧
      (((k : ℝ) < q ∧ q < k + 1) ∨ ((k : ℝ) - 1 < q ∧ q < k)) := by
  set C := J.whole with hC
  have hP' : C.P.Simple := hP
  set W := (chainModel C).W with hW
  obtain ⟨hc, hdet, hext⟩ := h
  obtain ⟨hτ0, hτ1, hnear, hnf⟩ := cap_param J hgen hext
  set τ := ((capNear J).2 - (sharedV J).2) / ((capFar J).2 - (sharedV J).2) with hτ
  have hk6 := (vkey_nbrs J hP hk hv).1
  set v := sharedV J with hv_def
  have hm₁ : J.m₁ ≤ C.m := by rw [hC, Merge.Junction.whole_m]; omega
  have hut : (sharedU J).2 ≤ C.top.2 := C.vertex_snd_le_top (j := J.m₁ - 1) (⋄)
  have hwt : (sharedW J).2 ≤ C.top.2 :=
    C.vertex_snd_le_top (j := J.m₁ + 1) (by rw [hC, Merge.Junction.whole_m]; have := J.one_le_m₂; omega)
  have hnt : (capNear J).2 ≤ C.top.2 := by
    rcases hnf with ⟨h1, -⟩ | ⟨h1, -⟩ <;> Ξ h1
    · exact hut
    · exact hwt
  have hfv : (capFar J).2 ≠ v.2 := by
    rcases hnf with ⟨-, h1⟩ | ⟨-, h1⟩ <;> Ξ h1
    · exact hgen.2.1
    · exact hgen.1
  have hcap : ∀ (p : ℕ) (t : ℝ), p < W.n → 0 ≤ t → t < 1 → sidePt W p t = capOrigin J →
      sideLeft W p t (rayPt (capOrigin J) (capDir J) 1) →
      (chainModel C).IsCut (J.fusion S₁ S₂ ∪ glueChords J) (p + t) := by
    intro p t hp ht ht1 hpt hl
    have hσ : capDir J = 1 ∨ capDir J = -1 := by
      unfold capDir; split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    have hq : (sidePt W p t).2 ≤ C.top.2 := by
      Ξ hpt, show capOrigin J = lerp v (capFar J) τ from rfl
      show v.2 + τ * ((capFar J).2 - v.2) ≤ _
      rw [← hnear]; exact hnt
    Ξ' ← hpt at hl
    obtain ⟨hfree, hA⟩ := sideAttach_shoot hP' hp ht ht1 hσ hq hl
    Ξ' hpt at hfree hA
    exact ⟨_, Or.inr (Or.inr ⟨hext, hfree, rfl⟩), p, t, hA, rfl⟩
  -- the two cases: the far neighbour is next or previous
  have hcase : (sideNext W k = capFar J ∧ sidePrev W k 0 = capNear J) ∨
      (sidePrev W k 0 = capFar J ∧ sideNext W k = capNear J) := by
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hnf with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨h2.trans h4.symm, h1.trans h3.symm⟩
    · exact Or.inr ⟨h1.trans h4.symm, h2.trans h3.symm⟩
    · exact Or.inr ⟨h1.trans h4.symm, h2.trans h3.symm⟩
    · exact Or.inl ⟨h2.trans h4.symm, h1.trans h3.symm⟩
  have hnear' := hnear
  rcases hcase with ⟨hN, hPr⟩ | ⟨hPr, hN⟩
  · -- the cap chord is attached on the walk edge after `k`
    set N := sideNext W k
    set Pp := sidePrev W k 0
    have hNv : v ≠ N := fun e => hfv (Ρ ← hN, ← e)
    have hvk := hv
    have hN' : W.vtx ((k + 1) % W.n) = N := rfl
    have hO : capOrigin J = lerp v N τ := by
      Ξ show capOrigin J = lerp v (capFar J) τ from rfl, ← hN
    have hD : capDir J = if Pp.1 < (lerp v N τ).1 then -1 else 1 := by
      Ξ show capDir J = if (capNear J).1 < (capOrigin J).1 then -1 else 1 from rfl, hO, hPr
    have hpt : sidePt W k τ = capOrigin J := by
      unfold sidePt; Ξ hvk, hN', hO
    have hl : sideLeft W k τ (rayPt (capOrigin J) (capDir J) 1) := by
      Ξ Chain.sideLeft_edge (by rw [hvk, hN']; exact hNv) ⟨hτ0, hτ1⟩, hvk, hN', hO, hD
      refine cap_left_next ?_ ?_
      · rw [hPr, hN]; exact hnear'
      · exact hdet
    exact ⟨_, hcap k τ hk hτ0.le hτ1 hpt hl, Or.inl ⟨⟡, ⟡⟩⟩
  · -- the cap chord is attached on the walk edge before `k`
    set N := sideNext W k
    set Pp := sidePrev W k 0
    have hPv : Pp ≠ v := fun e => hfv (Ρ ← hPr, e)
    have hvk := hv
    have hk1 : (k - 1 + 1) % W.n = k := Ρ Nat.sub_add_cancel (⋄), Nat.mod_eq_of_lt hk
    have hPk : W.vtx (k - 1) = Pp := by
      show _ = sidePrev W k 0
      unfold sidePrev
      rw [ite_eq_left rfl, show k + W.n - 1 = (k - 1) + W.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (⋄)]
    have hO : capOrigin J = lerp v Pp τ := by
      Ξ show capOrigin J = lerp v (capFar J) τ from rfl, ← hPr
    have hD : capDir J = if N.1 < (lerp v Pp τ).1 then -1 else 1 := by
      Ξ show capDir J = if (capNear J).1 < (capOrigin J).1 then -1 else 1 from rfl, hO, hN
    have hpt : sidePt W (k - 1) (1 - τ) = capOrigin J := by
      unfold sidePt; Ξ hk1, hPk, hvk, hO, Geometry.lerp_symm, sub_sub_cancel
    have hl : sideLeft W (k - 1) (1 - τ) (rayPt (capOrigin J) (capDir J) 1) := by
      rw [Chain.sideLeft_edge (by rw [hk1, hPk, hvk]; exact hPv) ⟨⟡, ⟡⟩,
        hk1, hPk, hvk, hO, hD]
      refine cap_left_prev ?_ ?_
      · rw [hPr, hN]; exact hnear'
      · exact hdet
    refine ⟨_, hcap (k - 1) (1 - τ) (⋄) (⟡) (⟡) hpt hl, Or.inr ?_⟩
    have : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub (⋄)]; simp
    Ξ this
    constructor <;> linarith

end Shared



/-! ## The copy of a top vertex that carried a slit -/

/-- **The walk corner at the top vertex contains a free horizontal direction**: at the corner
`tour(2m-1) → top → tour(1)` of a chain (the copy of the top vertex that carries the slit, seen
without the slit), some horizontal direction lies in the left sector. -/
theorem top_sector (C' : Chain) (hP' : C'.P.Simple) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ sideLeftOf (C'.sideTour C'.sideBeta (2 * C'.m - 1)) C'.top
      (C'.sideTour C'.sideBeta 1) (rayPt C'.top σ 1) := by
  set β := C'.sideBeta
  by_cases hT : C'.topIdx = 0 ∨ C'.topIdx = C'.m
  · Ξ C'.sideTour_one_eq_last β hT
    exact corner_full_ne (C'.sideTour_last_ne_top hP' β)
  push Not at hT
  have hT0 : 0 < C'.topIdx := Nat.pos_of_ne_zero hT.1
  have hTm : C'.topIdx < C'.m := lt_of_le_of_ne C'.topIdx_le hT.2
  have hgood := C'.sideGood_sideBeta hP'
  rcases hgood with h | h | hmain
  · exact absurd h hT.1
  · exact absurd h hT.2
  -- the neighbours
  have hlow : (C'.vertex (C'.topIdx - 1)).2 < C'.top.2 := by
    by_contra hc
    push Not at hc
    have := C'.topIdx_min (j := C'.topIdx - 1) (⋄) fun i hi =>
      (C'.vertex_snd_le_top hi).trans hc
    omega
  have hhigh : (C'.vertex (C'.topIdx + 1)).2 ≤ C'.top.2 := C'.vertex_snd_le_top (⋄)
  have hnb : (C'.sideTour β 1 = C'.vertex (C'.topIdx + 1) ∧
      C'.sideTour β (2 * C'.m - 1) = C'.vertex (C'.topIdx - 1)) ∨
      (C'.sideTour β 1 = C'.vertex (C'.topIdx - 1) ∧
        C'.sideTour β (2 * C'.m - 1) = C'.vertex (C'.topIdx + 1)) := by
    unfold Chain.sideTour
    cases hb : β
    · obtain ⟨h1, h2⟩ := C'.sideIdx_nbrs_false hT0 hTm
      right; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := C'.sideIdx_nbrs_true hT0 hTm
      left; rw [h1, h2]; exact ⟨rfl, rfl⟩
  set N := C'.sideTour β 1
  set P := C'.sideTour β (2 * C'.m - 1)
  set t := C'.top
  have hN2 : N.2 ≤ t.2 := by rcases hnb with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> linarith
  have hP2 : P.2 ≤ t.2 := by rcases hnb with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> linarith
  have hNt : N ≠ t := C'.sideTour_one_ne_top hP' β
  have hPt : P ≠ t := C'.sideTour_last_ne_top hP' β
  have hU1 : (C'.slitTop - t).1 = 0 := ⊚ Chain.slitTop, t
  have hU2 : 0 < (C'.slitTop - t).2 := by
    simp only [Chain.slitTop, Prod.snd_sub, t]; linarith [C'.top_snd_lt_radius]
  have hB : N - t ≠ 0 := sub_ne_zero.2 hNt
  have hA : P - t ≠ 0 := sub_ne_zero.2 hPt
  have hU : C'.slitTop - t ≠ 0 := fun e => by rw [e] at hU2; simp at hU2
  by_cases hE : (N - t).2 = 0 ∧ 0 ≤ (N - t).1
  · -- the next neighbour is level to the east: the sector contains west
    have hN' : N = C'.vertex (C'.topIdx + 1) := by
      rcases hnb with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exfalso; have := hE.1; ϴ' Prod.snd_sub at this; Ξ' h1 at this; linarith
    have hPl : P.2 < t.2 := by
      rcases hnb with ⟨-, h1⟩ | ⟨h1, -⟩
      · rw [h1]; exact hlow
      · exfalso; exact absurd (h1.symm.trans hN') (by
          intro e; have := C'.sideVertex_inj hP' (⋄) (⋄) e; omega)
    refine ⟨-1, Or.inr rfl, ?_⟩
    unfold sideLeftOf; Ξ rayPt_sub_one
    have hw := Chain.sideCcw_west (B := P - t) (X := ((-1 : ℝ), (0 : ℝ))) hU1 hU2 rfl (⊛)
      (by simp only [Prod.snd_sub]; linarith) hA (by
        unfold sideCross; simp only [Prod.fst_sub, Prod.snd_sub]; rintro ⟨h1, -⟩; linarith)
    exact Chain.sideCcw_sub_right hB hU hA hmain hw
  · refine ⟨1, Or.inl rfl, ?_⟩
    unfold sideLeftOf; Ξ rayPt_sub_one
    have he := Chain.sideCcw_east (A := N - t) (X := ((1 : ℝ), (0 : ℝ))) hU1 hU2 rfl one_pos
      (by simp only [Prod.snd_sub]; linarith) hB (by
        unfold sideCross sideDot; ϴ Prod.fst_sub, Prod.snd_sub
        rintro ⟨h1, h2⟩; apply hE; ϴ Prod.fst_sub, Prod.snd_sub
        constructor <;> linarith)
    exact Chain.sideCcw_sub_left hB hmain he

/-- **The copy of a top vertex of `C₁` or `C₂` that carried a slit is a cut** (§2.2 (G2)/(G3)):
at a walk vertex of `C` whose corner is the slit corner `tour(2m'-1) → top' → tour(1)` of the
side chain `C'`, a top chord of `C` is attached. -/
theorem topglue_cut (J : Merge.Junction) (hP : J.P.Simple) (S₁ S₂ : Set (Set Point)) {C' : Chain}
    (hP' : C'.P.Simple) {kt : ℕ} (hkt : kt ∈ topIdxs J) (hktm : kt ≤ J.whole.m)
    (hvert : J.whole.vertex kt = C'.top) {k : ℕ} (hk : k < (chainModel J.whole).W.n)
    (hprev : sidePrev (chainModel J.whole).W k 0 = C'.sideTour C'.sideBeta (2 * C'.m - 1))
    (hpt : (chainModel J.whole).W.vtx k = C'.top)
    (hnext : sideNext (chainModel J.whole).W k = C'.sideTour C'.sideBeta 1) :
    (chainModel J.whole).IsCut (J.fusion S₁ S₂ ∪ glueChords J) k := by
  obtain ⟨σ, hσ, hl⟩ := top_sector C' hP'
  have hpt' : sidePt (chainModel J.whole).W k 0 = J.whole.vertex kt := by
    Ξ Chain.sidePt_zero, hpt, hvert
  have hl' : sideLeft (chainModel J.whole).W k 0 (rayPt (J.whole.vertex kt) σ 1) := by
    unfold sideLeft; rw [hprev, hnext, hpt', hvert]; exact hl
  obtain ⟨hfree, hA⟩ := sideAttach_chordSet hP hk hktm hpt' hσ hl'
  exact ⟨_, Or.inr (Or.inl ⟨kt, hkt, σ, hσ, hfree, rfl⟩), k, 0, hA, ✓⟩

/-! ## Cuts transfer from a side walk to the walk of `C` -/

/-- **Cut transfer along an agreement** (the walk embedding preserves cuts): a cut of `Sᵢ` at a
position of an agreeing stretch of the walk of the side chain `C'` gives a cut of the revised
fusion at the same offset of the walk of `C` — through the fused chord contained in the old
chord at its endpoint (`Merge.end_mem_fusion`), or through a shared chord if the endpoint is the
shared vertex. -/
theorem cut_transfer (J : Merge.Junction) (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple)
    {Si S' : Set (Set Point)} (hsub : Si ⊆ Merge.augChords C')
    (hend : ∀ c ∈ Si, (Merge.lend c ≠ J.shared → ∃ e ∈ S', Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared → ∃ e ∈ S', Merge.rend c ∈ e ∧ e ⊆ c))
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hA : WalkEmbed.Agree (chainModel J.whole).W (chainModel C').W g g' L)
    {d : ℕ} (hd : d < L) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hdt : 0 < (d : ℝ) + t)
    (hc : (chainModel C').IsCut Si (((g' + d) % (chainModel C').W.n : ℕ) + t)) :
    (chainModel J.whole).IsCut S' (((g + d) % (chainModel J.whole).W.n : ℕ) + t) := by
  set W := (chainModel J.whole).W with hW
  set W' := (chainModel C').W with hW'
  have hn : 0 < W.n := by rw [hW, WalkEmbed.cm_n]; omega
  have hn' : 0 < W'.n := by rw [hW', WalkEmbed.cm_n]; omega
  have hdt' : t = 0 → 1 ≤ d := fun h => by
    Ξ' h, add_zero at hdt; exact_mod_cast hdt
  obtain ⟨c, hcS, p, t', hA', hkey⟩ := hc
  obtain ⟨hpe, hte⟩ := Chain.sideKey_inj ht ht1 hA'.2.1 hA'.2.2.1 hkey
  subst hpe hte
  set p' := (g' + d) % W'.n
  set q := sidePt W' p' t
  have hq := hA'.2.2.2.1
  have hqd : q ∉ C'.dom := (walkAx_chainModel hP').trace _ hA'.1 t ht ht1.le
  obtain ⟨y, a, b, hH, hy, rfl, hl, hr⟩ := Merge.augChords_spec (hsub hcS)
  have hqe : q = (a, y) ∨ q = (b, y) := by
    obtain ⟨hq2, hqa, hqb⟩ := hq
    rcases hqa.lt_or_eq with h1 | h1
    · rcases hqb.lt_or_eq with h2 | h2
      · exact absurd (by rw [show q = (q.1, y) from Prod.ext rfl hq2]; exact hH.open_mem q.1 h1 h2)
          hqd
      · right; exact Prod.ext h2 hq2
    · left; exact Prod.ext h1.symm hq2
  have hpt : sidePt W ((g + d) % W.n) t = q := hA.sidePt_eq hd t
  have hleft := hA.sideLeft_eq hn hn' hd hdt'
  by_cases hv : q = J.shared
  · -- the endpoint is the shared vertex: a shared chord is attached here
    obtain ⟨r, hr0, hsec⟩ := hA'.2.2.2.2
    have hab := hH.lt
    obtain ⟨σ, hσ, hdir⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        sideLeft W' p' t (rayPt q σ 1) := by
      set ε := min (r / 2) ((b - a) / 2) with hε
      have hε0 : 0 < ε := lt_min (⟡) (⟡)
      have hεr : ε < r := lt_of_le_of_lt (min_le_left _ _) (⟡)
      have hεb : ε ≤ (b - a) / 2 := min_le_right _ _
      rcases hqe with hqa | hqb
      · refine ⟨1, Or.inl rfl, (sideLeft_rayPt hε0).1 (hsec _ ?_ ?_ ?_)⟩
        · show rayPt q 1 ε ∈ _
          rw [hqa]; refine ⟨rfl, ?_, ?_⟩ <;> simp only [rayPt] <;> linarith
        · intro e; have := congrArg Prod.fst e; ϴ' rayPt at this; linarith
        · rw [dist_rayPt _ (Or.inl rfl) hε0.le]; exact hεr
      · refine ⟨-1, Or.inr rfl, (sideLeft_rayPt hε0).1 (hsec _ ?_ ?_ ?_)⟩
        · show rayPt q (-1) ε ∈ _
          rw [hqb]; refine ⟨rfl, ?_, ?_⟩ <;> simp only [rayPt] <;> linarith
        · intro e; have := congrArg Prod.fst e; ϴ' rayPt at this; linarith
        · rw [dist_rayPt _ (Or.inr rfl) hε0.le]; exact hεr
    have hl2 : sideLeft W ((g + d) % W.n) t (rayPt (sidePt W ((g + d) % W.n) t) σ 1) := by
      rw [hleft, hpt]; exact hdir
    have hm₁ : J.m₁ ≤ J.whole.m := by rw [Merge.Junction.whole_m]; omega
    have hvq : sidePt W ((g + d) % W.n) t = J.whole.vertex J.m₁ := hpt.trans hv
    obtain ⟨hfree, hAt⟩ := sideAttach_shoot hP (Nat.mod_lt _ hn) ht ht1 hσ
      (by rw [hvq]; exact J.whole.vertex_snd_le_top hm₁) hl2
    Ξ' hvq at hfree hAt
    exact ⟨_, hshared ⟨σ, hσ, hfree, rfl⟩, _, t, hAt, rfl⟩
  · obtain ⟨hL, hR⟩ := hend _ hcS
    rcases hqe with hqa | hqb
    · obtain ⟨e, he, hqe, hec⟩ := hL (by rw [hl, ← hqa]; exact hv)
      Ξ' hl, ← hqa at hqe
      exact ⟨e, he, _, t, hA.sideAttach_subset hn hn' hd hdt' hA' hec hqe, rfl⟩
    · obtain ⟨e, he, hqe, hec⟩ := hR (by rw [hr, ← hqb]; exact hv)
      Ξ' hr, ← hqb at hqe
      exact ⟨e, he, _, t, hA.sideAttach_subset hn hn' hd hdt' hA' hec hqe, rfl⟩

end FuseMath

end

end Chazelle.Core
