module

public import Chazelle.MacT
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.ClusterLabelStage

section
set_option hygiene false
local macro "zqbac" : tactic => `(tactic| (left
                                           refine hcut _ ztbt ?_
                                           rw [hNs, show C.slitTop = ztmzq by rw [hvT]; rfl]
                                           exact corner_west by_simp_all by_grind))
local macro "zqbad" : tactic => `(tactic| (unfold sideLeftOf sideCcw; zuoyf
                                           right; right; right
                                           refine ⟨Chain.sideCross_self _, Chain.sideDot_self_pos hne, Or.inr ?_⟩
                                           unfold sideDot; simp_all))
local macro "zqbae" : tactic => `(tactic| (set C := J.whole with hC
                                           have hP' := hP))
local macro "zqbaf" : tactic => `(tactic| refine ⟨1, Or.inl rfl, ?_⟩)
local macro "zqbag" : tactic => `(tactic| (exfalso; zvmza at hdet; rw [h3, h4] at hdet'
                                           rw [Geometry.det_swap13] at hdet'; linarith))
local macro "zqbah" : tactic => `(tactic| (unfold sideLeftOf sideCcw
                                           zuoyf
                                           zurx
                                           refine ⟨hcr, hd, ?_⟩
                                           unfold sideCross; simp_all))
local macro "zqbai" : tactic => `(tactic| exact ⟨e, he, _, t, hA.sideAttach_subset hn hn' hd hdt' hA' hec hqe, rfl⟩)
local macro "zqbaj" : tactic => `(tactic| refine ⟨-1, Or.inr rfl, ?_⟩)
local macro "zqbak" : tactic => `(tactic| set W := (chainModel C).W with hW)
local macro "zqbal" : tactic => `(tactic| (unfold sideCross
                                           zvnhb
                                           grind))
local macro "zqbam" : tactic => `(tactic| have hm₁ : J.m₁ ≤ C.m := by_simp_all)
local macro "zqban" : tactic => `(tactic| have hut : (sharedU J).2 ≤ C.top.2 := C.vertex_snd_le_top by_omega)
local macro "zqbao" : tactic => `(tactic| (intro e; have := congrArg Prod.fst e; zvnap at this; linarith))
set_option hygiene true

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
theorem rayPt_sub (p : Point) (σ ε : ℝ) : rayPt p σ ε - p = ε • (ztwn : Point) := by
  ext <;> zvmxf; ring
theorem sideLeft_rayPt {W : Polygon} {p : ℕ} {t σ ε : ℝ} (hε : 0 < ε) :
    sideLeft W p t (rayPt ztia σ ε) ↔ sideLeft W p t ztxoo := by
  zuhrd
  rw [rayPt_sub, rayPt_sub, one_smul, Chain.sideCcw_smul hε]
theorem dist_rayPt (q : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {ε : ℝ} (hε : 0 ≤ ε) :
    dist (rayPt q σ ε) q = ε := by
  zugtz
  simp only [rayPt, Real.dist_eq, sub_self, abs_zero]
  zur
  · simp_all
  simp_all
variable {C : Chain}
/-- **Clean positions give free directions**: if the horizontal direction `σ` leaves a position of
the walk of a chain model into its left sector, the ray from its point is free. -/
theorem freeAt_of_sideLeft (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hl : sideLeft (chainModel C).W p t ztznt) :
    Merge.FreeAt C ztic σ := by
  obtain ⟨r, hr, hcl⟩ := (walkAx_chainModel hP).clean p hp t ht ht1
  unfold Merge.FreeAt
  filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
  zuhtn
  refine hcl _ ?_ hnd ((sideLeft_rayPt hε.1).2 hl)
  rw [mem_ball, dist_rayPt _ hσ hε.1.le]
  simp_all

/-- **The chord shot along a free direction of a position is attached there.** -/
theorem sideAttach_shoot (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hq : (sidePt (chainModel C).W p t).2 ≤ C.top.2)
    (hl : sideLeft (chainModel C).W p t ztznt) :
    Merge.FreeAt C ztic σ ∧
      SideAttach (chainModel C).W (Merge.shoot C ztic σ) p t := by
  have hfree := freeAt_of_sideLeft hP hp ht ht1 hσ hl
  zuknu
  obtain ⟨hpos, -, -⟩ := Merge.hit_of_freeAt C hq hσ hfree
  exact Chain.sideAttach_of_left hp ht ht1 rfl ((sideLeft_rayPt hpos).2 hl)

/-- The vertex-chord version: a horizontal direction in the left sector of a walk position at a
chain vertex is free, and the vertex chord is attached there. -/
theorem sideAttach_chordSet (hP : C.P.Simple) {p : ℕ} (hp : p < (chainModel C).W.n)
    {k : ℕ} (hk : k ≤ C.m) (hpt : sidePt (chainModel C).W p 0 = C.vertex k) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hl : sideLeft (chainModel C).W p 0 (rayPt ztib σ 1)) :
    C.DirFree k σ ∧ SideAttach (chainModel C).W ztjhg p 0 := by
  zujmf
  have h := sideAttach_shoot hP hp le_rfl zero_lt_one hσ
    (by zvmxe; exact C.vertex_snd_le_top hk) hl
  zukvs
  zubh

/-! ## Horizontal directions in a corner at the shared vertex -/
section Corner
variable {P N v : Point}
theorem det_rayPt_left (P v : Point) (σ : ℝ) : det P v ztczx = σ * zthbw := by
  unfold det; zvnap; ring
theorem det_rayPt_right (v N : Point) (σ : ℝ) : det v N ztczx = -ztbabj := by
  unfold det; simp
theorem rayPt_sub_one (v : Point) (σ : ℝ) : rayPt v σ 1 - v = (ztwn : Point) := by
  ext <;> zvmxf

/-- A full-turn corner contains the direction east when the neighbour is not at the same height. -/
theorem corner_full (h : P.2 ≠ v.2) : sideLeftOf P v P ztrva := by
  zueez
  zugxa
  zubef
  refine ⟨Chain.sideCross_self _, Chain.sideDot_self_pos by_grind,
    Or.inl ?_⟩
  zqbal
variable {R : ℝ}
/-- Coming down the slit to a vertex whose next neighbour is lower: the sector contains east. -/
theorem corner_east (hR : v.2 < R) (hN : N.2 < v.2) :
    sideLeftOf (ztucu : Point) v N ztrva := by
  zucfg
  zugxa
  refine Chain.sideCcw_east by_simp by_simp_all rfl one_pos ztrky
    by_grind ?_
  zqbal

/-- Arriving at a vertex from a lower neighbour and going up the slit: the sector contains
west. -/
theorem corner_west (hR : v.2 < R) (hP : P.2 < v.2) :
    sideLeftOf P v (ztucu : Point) (rayPt v (-1) 1) := by
  zucfg
  zugxa
  refine Chain.sideCcw_west by_simp by_simp_all rfl by_norm_num ztrky
    by_grind ?_
  zqbal

/-- **A corner with neighbours off the horizontal line of the vertex** contains a horizontal
direction, unless it turns left with both neighbours on the same side (the inner corner of a
local extremum). -/
theorem corner_pair (hP : P.2 ≠ v.2) (hN : N.2 ≠ v.2) :
    (∃ σ : ℝ, ztdd ∧ sideLeftOf P v N ztczx) ∨
      (0 < det P v N ∧ 0 < zthbw * zthbm) := by
  rcases lt_trichotomy (det P v N) 0 with hneg | hzero | hpos
  · left
    zujea
    · refine ⟨1, Or.inl rfl, (Chain.sideLeftOf_iff_neg hneg).2 ztenp⟩
      zudtq
    · refine ⟨-1, Or.inr rfl, (Chain.sideLeftOf_iff_neg hneg).2 ztenp⟩
      zudtq
  · left
    have hB : N - v ≠ 0 := by_grind
    have hA : P - v ≠ 0 := by_grind
    have hcr : sideCross ztnnb ztjkw = 0 := by rw [Chain.sideCross_corner]; omega
    have hdot : sideDot ztnnb ztjkw ≠ 0 := by
      zudqe
      have L := Chain.side_lagrange ztnnb ztjkw
      rw [hcr, hd] at L
      have h1 := Chain.sideDot_self_pos hB
      have h2 := Chain.sideDot_self_pos hA
      nlinarith
    rcases lt_or_gt_of_ne hdot with hd | hd
    · zujea
      · zqbaf
        zqbah
      · zqbaj
        zqbah
    · zqbaf
      zueez
      zugxa
      zubef
      refine ⟨hcr, hd, Or.inl ?_⟩
      unfold sideCross; zvnhb
      grind
  · rcases lt_or_gt_of_ne hP with hP' | hP' <;> rcases lt_or_gt_of_ne hN with hN' | hN'
    · right; exact ⟨hpos, by_nlinarith⟩
    · left
      refine ⟨-1, Or.inr rfl, (Chain.sideLeftOf_iff_pos hpos).2 ztcp⟩
      · zudtq
      · zukqp
    · left
      refine ⟨1, Or.inl rfl, (Chain.sideLeftOf_iff_pos hpos).2 ztcp⟩
      · zudtq
      · zukqp
    simp_all

/-- A full-turn corner at a vertex different from its neighbour contains a horizontal
direction. -/
theorem corner_full_ne (h : P ≠ v) : ∃ σ : ℝ, ztdd ∧ sideLeftOf P v P ztczx := by
  by_cases h2 : P.2 = v.2
  · have h1 : P.1 ≠ v.1 := by_grind
    have hne := sub_ne_zero.2 h
    have hcr : ∀ σ : ℝ, sideCross ztjkw (ztwn : Point) = 0 := by
      intro σ; unfold sideCross; simp_all
    rcases lt_or_gt_of_ne h1 with hl | hg
    · zqbaf
      zqbad
    · zqbaj
      zqbad
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
  zqbae
  zqbam
  have hvbox : sharedV J ∈ Chain.box C.radius := C.set_subset_box (C.vertex_mem_set hm₁)
  have hn := WalkEmbed.cm_n C
  zugeh
  have h6 : 6 ≤ k := by
    zumv
    rw [← hv] at hvbox
    rw [WalkEmbed.cm_W] at hvbox
    interval_cases k
    · zulxj
    · zuleq
    · zuleq
    · zuler
    · zuler
    · zulxj
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 6 := ⟨k - 6, by_omega⟩
  zukcn
  have hidx : C.sideIdx C.sideBeta i = J.m₁ := by
    rw [WalkEmbed.cm_W, C.sideWalk_vtx_tour _ hi] at hv
    exact C.sideVertex_inj hP' ztbdw hm₁ hv
  have hnb : ∀ j, (C.sideIdx C.sideBeta j = J.m₁ + 1 ∨ C.sideIdx C.sideBeta j + 1 = J.m₁) →
      C.vertex ztsvz = sharedU J ∨ C.vertex ztsvz = sharedW J := by
    zun
    rcases hj with hj | hj
    · tauto
    · left; rw [show C.sideIdx C.sideBeta j = J.m₁ - 1 by omega]; rfl
  zujfy
  · zulcf
    rw [ite_eq_left rfl, WalkEmbed.cm_W]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · zulw
      rw [C.sideWalk_prev_six, C.sideWalk_vtx_five]
      zubee
      rw [← hv, WalkEmbed.cm_W, zero_add, C.sideWalk_vtx_six]
    · rw [C.sideWalk_prev_tour _ hi0 hi, C.sideWalk_vtx_tour _ by_omega]
      have hs := C.sideTour_step C.sideBeta ztei
      rw [Nat.sub_add_cancel hi0, hidx] at hs
      rcases hnb ztei by_omega with h | h
      · tauto
      · exact Or.inr zteg
  · zumuu
    rw [WalkEmbed.cm_W]
    rcases lt_or_eq_of_le hi with hi' | rfl
    · rw [C.sideWalk_next_tour _ hi', C.sideWalk_vtx_tour _ by_omega]
      zukfk
      rw [hidx] at hs
      rcases hnb _ by_omega with h | h
      · tauto
      · exact Or.inr zteg
    · zulw
      rw [C.sideWalk_next_last]
      zubee
      rw [← hv, WalkEmbed.cm_W, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m]

/-- The inner-corner condition at a copy `k` of the shared vertex: the corner is `u → v → w` or
`w → v → u`, it turns left, and `v` is a local extremum. -/
def InnerCopy (k : ℕ) : Prop :=
  ((sidePrev (chainModel J.whole).W k 0 = sharedU J ∧ sideNext (chainModel J.whole).W k = sharedW J) ∨
    (sidePrev (chainModel J.whole).W k 0 = sharedW J ∧ sideNext (chainModel J.whole).W k = sharedU J)) ∧
  0 < det (sidePrev (chainModel J.whole).W k 0) ztiar (sideNext (chainModel J.whole).W k) ∧
  SharedExtremum J

/-- **Every copy of the shared vertex is a cut of the revised fusion, except an inner copy**
(design doc §2.2 (G1)). -/
theorem vkey_cut_or_inner (hP : J.P.Simple) (hgen : SharedGeneric J) (S₁ S₂ : Set ztf)
    {k : ℕ} (hk : k < (chainModel J.whole).W.n) (hv : (chainModel J.whole).W.vtx k = sharedV J) :
    (chainModel J.whole).IsCut ztqu k ∨ InnerCopy J k := by
  zqbae
  obtain ⟨-, hPr, hNx⟩ := vkey_nbrs J hP hk hv
  zqbak
  set Pr := sidePrev W k 0 with hPr_def
  set Nx := sideNext W k with hNx_def
  zqbam
  have hu := hgen.1
  have hw := hgen.2.1
  zqban
  have hwt : ztphg :=
    C.vertex_snd_le_top (by zunoz; have := J.one_le_m₂; omega)
  have hvt : (sharedV J).2 ≤ C.top.2 := C.vertex_snd_le_top hm₁
  zueqq
  -- the height of each neighbour differs from that of `v`
  have hne : ∀ X, (X = sharedU J ∨ X = sharedW J ∨ (X = C.slitTop ∧ sharedV J = C.top)) →
      X.2 ≠ (sharedV J).2 := by
    rintro X (rfl | rfl | ⟨rfl, -⟩)
    · exact hu
    · zulzb
    · show C.radius ≠ _; grind
  -- a horizontal direction in the sector gives a cut
  have hcut : ∀ σ : ℝ, ztdd → sideLeftOf Pr ztiar Nx (rayPt ztiar σ 1) →
      (chainModel C).IsCut ztqu k := by
    intro σ hσ hl
    have hpt : sidePt W k 0 = C.vertex J.m₁ := by zuofc; exact hv
    have hl' : sideLeft W k 0 (rayPt (C.vertex J.m₁) σ 1) := by
      unfold sideLeft; zvmxe; exact hl
    obtain ⟨hfree, hA⟩ := sideAttach_chordSet hP' hk hm₁ hpt hσ hl'
    refine ⟨C.chordSet J.m₁ σ, Or.inl (Merge.Junction.sharedChords_subset_fusion J S₁ S₂
      ⟨σ, hσ, hfree, rfl⟩), k, 0, hA, by_simp⟩
  by_cases hPN : Pr = Nx
  · left
    zuloi
    rw [← hPN]
    exact corner_full by_grind
  rcases hPr with hPu | hPw | ⟨hPs, hvT⟩
  · zuflk
    · simp_all
    · rcases corner_pair (hne _ (Or.inl hPu)) (hne _ (Or.inr (Or.inl hNw))) with ⟨σ, hσ, hl⟩ | hexc
      · grind
      · right
        refine ztraw
        unfold SharedExtremum; simp_all
    · zqbac
  · zuflk
    · rcases corner_pair (hne _ (Or.inr (Or.inl hPw))) (hne _ (Or.inl hNu)) with ⟨σ, hσ, hl⟩ | hexc
      · grind
      · right
        refine ztraw
        unfold SharedExtremum; rw [← hPw, ← hNu, mul_comm]; simp_all
    · simp_all
    · zqbac
  · left
    have hN' : Nx.2 < (sharedV J).2 := by
      grind
    zuloi
    rw [hPs, show C.slitTop = ztmzq by rw [hvT]; rfl]
    exact corner_east by_simp_all hN'

/-- **There is at most one inner copy**: two inner copies have the same corner, hence overlapping
left sectors at the same point, so they are the same walk position (`Chain.sideWalk_disj`). -/
theorem inner_unique (hP : J.P.Simple) {k k' : ℕ} (hk : k < (chainModel J.whole).W.n)
    (hk' : k' < (chainModel J.whole).W.n) (hv : (chainModel J.whole).W.vtx k = sharedV J)
    (hv' : (chainModel J.whole).W.vtx k' = sharedV J) (h : InnerCopy J k) (h' : InnerCopy J k') :
    k = k' := by
  zqbae
  zqbak
  obtain ⟨hc, hdet, -⟩ := h
  obtain ⟨hc', hdet', -⟩ := h'
  -- the same corner
  have hsame : sidePrev W k 0 = sidePrev W k' 0 ∧ sideNext W k = sideNext W k' := by
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hc' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · simp_all
    · zqbag
    · zqbag
    simp_all
  zuct
  set Pr := sidePrev W k 0
  set Nx := sideNext W k
  set v := sharedV J
  have hpt : sidePt W k 0 = v := by zuofc; exact hv
  have hpt' : sidePt W k' 0 = v := by zuofc; omega
  have hleft : ∀ j, sidePt W j 0 = v → sidePrev W j 0 = Pr → sideNext W j = Nx →
      sideLeft W j 0 ztjlh := by
    intro j hj hp hn
    zuluz
    rw [hj, hp, hn, Chain.sideLeftOf_iff_pos hdet]
    constructor
    · have : det Pr v ztjlh = det Pr v Nx := by
        zudwf
      simp_all
    · have : det v Nx ztjlh = det Pr v Nx := by
        zudwf
      simp_all
  zqbam
  exact C.sideWalk_disj hP' (C.sideGood_sideBeta hP') hk le_rfl zero_lt_one hk' le_rfl zero_lt_one
    by_omega (by show sidePt W k' 0 = sidePt W k 0; simp_all)
    (Or.inl (by show sidePt W k 0 ∈ C.set; zvmxe; exact C.vertex_mem_set hm₁)) _
    ⟨hleft k hpt rfl rfl, hleft k' hpt' hsame.1.symm hsame.2.symm⟩

/-! ### The cap chord -/
omit J in
/-- The sign computation of the cap chord shot from the arm after the corner. -/
theorem cap_left_next {v N P : Point} {τ : ℝ} (hPc : P.2 = v.2 + τ * zthbm)
    (hdet : 0 < det P v N) :
    0 < det v N (rayPt ztrtl (if P.1 < (lerp v N τ).1 then -1 else 1) 1) := by
  have key : det P v N = -(P.1 - (lerp v N τ).1) * zthbm := by
    zuhak
  have e : ∀ σ : ℝ, det v N (rayPt ztrtl σ 1) = -ztbabj := by
    zuead
  zui
  zuhmx

  · nlinarith
  · zugri

    · nlinarith
    simp_all
omit J in
/-- The sign computation of the cap chord shot from the arm before the corner. -/
theorem cap_left_prev {v N P : Point} {τ : ℝ} (hNc : N.2 = v.2 + τ * zthbw)
    (hdet : 0 < det P v N) :
    0 < det P v (rayPt ztrtm (if N.1 < (lerp v P τ).1 then -1 else 1) 1) := by
  have key : det P v N = zthbw * (N.1 - (lerp v P τ).1) := by
    zuhak
  have e : ∀ σ : ℝ, det P v (rayPt ztrtm σ 1) = σ * zthbw := by
    zuead
  zui
  zuhmx

  · nlinarith
  · zugri

    · nlinarith
    simp_all

/-- The parameter of the cap origin on the far arm lies in `(0, 1)`, and the cap origin is at the
height of the near neighbour. -/
theorem cap_param (hgen : SharedGeneric J) (hext : SharedExtremum J) :
    let τ := ztcrt / ztbxj
    0 < τ ∧ τ < 1 ∧ (capNear J).2 = (sharedV J).2 + τ * ztbxj ∧
      ((capNear J = sharedU J ∧ capFar J = sharedW J) ∨
        (capNear J = sharedW J ∧ capFar J = sharedU J)) := by
  obtain ⟨hu, hw, huw⟩ := hgen
  unfold SharedExtremum at hext
  unfold capNear capFar
  set du := (sharedU J).2 - (sharedV J).2
  set dw := (sharedW J).2 - (sharedV J).2
  have hdu := sub_ne_zero.2 hu
  have hdw := sub_ne_zero.2 hw
  have hduw : du ≠ dw := by_grind
  zus
  · zumhv

    · zujef
      · zulyh
      · zulyg
    · zujef
      · have hdu' : du < 0 := by_nlinarith
        rw [abs_of_neg hdu', abs_of_neg hn] at h
        exact (div_lt_one_of_neg hn).2 by_linarith
      · have hdu' : 0 < du := by_nlinarith
        rw [abs_of_pos hdu', abs_of_pos hp] at h
        exact (div_lt_one hp).2 h
    grind
  · zumhv

    · zujee
      · zulyh
      · zulyg
    · zujee
      · have hdw' : dw < 0 := by_nlinarith
        rw [abs_of_neg hdw', abs_of_neg hn] at h
        exact (div_lt_one_of_neg hn).2 by_grind
      · have hdw' : 0 < dw := by_nlinarith
        rw [abs_of_pos hdw', abs_of_pos hp] at h
        exact (div_lt_one hp).2 by_grind
    grind

/-- **The cap chord is a cut next to the inner copy** (design doc §2.3): at the inner copy `k`
of the shared vertex, the cap chord is attached on the walk edge after `k` (key in `(k, k + 1)`)
or on the walk edge before `k` (key in `(k - 1, k)`). -/
theorem inner_cap_cut (hP : J.P.Simple) (hgen : SharedGeneric J) (S₁ S₂ : Set ztf)
    {k : ℕ} (hk : k < (chainModel J.whole).W.n) (hv : (chainModel J.whole).W.vtx k = sharedV J)
    (h : InnerCopy J k) :
    ∃ q : ℝ, (chainModel J.whole).IsCut ztqu q ∧
      (((k : ℝ) < q ∧ q < k + 1) ∨ ((k : ℝ) - 1 < q ∧ q < k)) := by
  zqbae
  zqbak
  obtain ⟨hc, hdet, hext⟩ := h
  zuebf
  set τ := ztcrt / ztbxj with hτ
  zufvd
  set v := sharedV J with hv_def
  have hm₁ : J.m₁ ≤ C.m := by zunoz; omega
  zqban
  have hwt : ztphg :=
    C.vertex_snd_le_top (by zunoz; have := J.one_le_m₂; omega)
  have hnt : (capNear J).2 ≤ C.top.2 := by
    grind
  have hfv : (capFar J).2 ≠ v.2 := by
    grind
  have hcap : ∀ (p : ℕ) (t : ℝ), p < W.n → 0 ≤ t → t < 1 → sidePt W p t = capOrigin J →
      sideLeft W p t ztyfl →
      (chainModel C).IsCut ztqu ztk := by
    intro p t hp ht ht1 hpt hl
    have hσ : ztlxv := by
      zumsc
    have hq : (sidePt W p t).2 ≤ C.top.2 := by
      rw [hpt, show capOrigin J = lerp v _ τ from rfl]
      show v.2 + τ * ((capFar J).2 - v.2) ≤ _
      grind
    zujmf
    obtain ⟨hfree, hA⟩ := sideAttach_shoot hP' hp ht ht1 hσ hq hl
    zvmxe at hfree hA
    exact ⟨_, Or.inr (Or.inr ⟨hext, hfree, rfl⟩), p, t, hA, rfl⟩
  -- the two cases: the far neighbour is next or previous
  have hcase : (sideNext W k = capFar J ∧ sidePrev W k 0 = capNear J) ∨
      (sidePrev W k 0 = capFar J ∧ sideNext W k = capNear J) := by
    grind
  have hnear' := hnear
  rcases hcase with ⟨hN, hPr⟩ | ⟨hPr, hN⟩
  · -- the cap chord is attached on the walk edge after `k`
    zufag

    have hNv : v ≠ N := by_grind
    zumez
    have hN' : W.vtx _ = N := rfl
    have hO : capOrigin J = lerp v N τ := by
      rw [show capOrigin J = lerp v _ τ from rfl, ← hN]
    have hD : capDir J = if Pp.1 < (lerp v N τ).1 then -1 else 1 := by
      rw [show capDir J = if (capNear J).1 < (capOrigin J).1 then -1 else 1 from rfl, hO, hPr]
    have hpt : sidePt W k τ = capOrigin J := by
      zuhbc
    have hl : sideLeft W k τ ztyfl := by
      rw [Chain.sideLeft_edge by_grind ⟨hτ0, hτ1⟩, hvk, hN', hO, hD]
      refine cap_left_next ?_ ?_
      · grind
      omega
    exact ⟨_, hcap k τ hk hτ0.le hτ1 hpt hl, by_grind⟩
  · -- the cap chord is attached on the walk edge before `k`
    zufag

    have hPv : Pp ≠ v := by_grind
    zumez
    have hk1 : (k - 1 + 1) % W.n = k := by rw [Nat.sub_add_cancel by_omega, Nat.mod_eq_of_lt hk]
    have hPk : W.vtx ztie = Pp := by
      show _ = sidePrev W k 0
      zulcf
      rw [ite_eq_left rfl, show k + W.n - 1 = ztie + W.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt by_omega]
    have hO : capOrigin J = lerp v Pp τ := by
      rw [show capOrigin J = lerp v _ τ from rfl, ← hPr]
    have hD : capDir J = if N.1 < (lerp v Pp τ).1 then -1 else 1 := by
      rw [show capDir J = if (capNear J).1 < (capOrigin J).1 then -1 else 1 from rfl, hO, hN]
    have hpt : sidePt W ztie ztcsf = capOrigin J := by
      unfold sidePt; rw [hk1, hPk, hvk, hO, Geometry.lerp_symm, sub_sub_cancel]
    have hl : sideLeft W ztie ztcsf ztyfl := by
      rw [Chain.sideLeft_edge by_grind ztbcx,
        hk1, hPk, hvk, hO, hD]
      refine cap_left_prev ?_ ?_
      · grind
      omega
    refine ⟨_, hcap _ _ by_omega by_linarith by_linarith hpt hl, Or.inr ?_⟩
    have : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub by_omega]; simp
    zubk
    grind
end Shared

/-! ## The copy of a top vertex that carried a slit -/

/-- **The walk corner at the top vertex contains a free horizontal direction**: at the corner
`tour(2m-1) → top → tour(1)` of a chain (the copy of the top vertex that carries the slit, seen
without the slit), some horizontal direction lies in the left sector. -/
theorem top_sector (C' : Chain) (hP' : C'.P.Simple) :
    ∃ σ : ℝ, ztdd ∧ sideLeftOf (C'.sideTour C'.sideBeta ztcsg) C'.top
      (C'.sideTour C'.sideBeta 1) (rayPt C'.top σ 1) := by
  set β := C'.sideBeta
  by_cases hT : C'.topIdx = 0 ∨ C'.topIdx = C'.m
  · rw [C'.sideTour_one_eq_last β hT]
    exact corner_full_ne (C'.sideTour_last_ne_top hP' β)
  zumih
  have hT0 := Nat.pos_of_ne_zero hT.1
  have hTm := lt_of_le_of_ne C'.topIdx_le hT.2
  have hgood := C'.sideGood_sideBeta hP'
  rcases hgood with h | h | hmain
  · omega
  · omega
  -- the neighbours
  have hlow : (C'.vertex ztnjt).2 < C'.top.2 := by
    zux

    have := C'.topIdx_min by_omega fun i hi =>
      (C'.vertex_snd_le_top hi).trans hc
    omega
  have hhigh : (C'.vertex ztjhf).2 ≤ C'.top.2 := C'.vertex_snd_le_top by_omega
  have hnb : (C'.sideTour β 1 = C'.vertex ztjhf ∧
      C'.sideTour β ztcsg = C'.vertex ztnjt) ∨
      (C'.sideTour β 1 = C'.vertex ztnjt ∧
        C'.sideTour β ztcsg = C'.vertex ztjhf) := by
    zueev
    cases hb : β
    · obtain ⟨h1, h2⟩ := C'.sideIdx_nbrs_false hT0 hTm
      simp_all
    · obtain ⟨h1, h2⟩ := C'.sideIdx_nbrs_true hT0 hTm
      simp_all
  set N := C'.sideTour β 1
  set P := C'.sideTour β ztcsg
  set t := C'.top
  have hN2 : N.2 ≤ t.2 := by_grind
  have hP2 : P.2 ≤ t.2 := by_grind
  have hNt := C'.sideTour_one_ne_top hP' β
  have hPt := C'.sideTour_last_ne_top hP' β
  have hU1 : (C'.slitTop - t).1 = 0 := by simp [Chain.slitTop, t]
  have hU2 : 0 < (C'.slitTop - t).2 := by
    simp only [Chain.slitTop, Prod.snd_sub, t]; linarith [C'.top_snd_lt_radius]
  have hB := sub_ne_zero.2 hNt
  have hA := sub_ne_zero.2 hPt
  have hU : C'.slitTop - t ≠ 0 := fun e => by_simp_all
  by_cases hE : (N - t).2 = 0 ∧ 0 ≤ (N - t).1
  · -- the next neighbour is level to the east: the sector contains west
    have hN' : N = C'.vertex ztjhf := by
      rcases hnb with ⟨h1, -⟩ | ⟨h1, -⟩
      · zubvv
      · exfalso; have := hE.1; simp only [Prod.snd_sub] at this; grind
    have hPl : P.2 < t.2 := by
      grind
    zqbaj
    zujra
    have hw := Chain.sideCcw_west (B := P - t) (X := ((-1 : ℝ), (0 : ℝ))) hU1 hU2 rfl by_norm_num
      by_simp_all hA (by
        unfold sideCross; zvnhb; grind)
    exact Chain.sideCcw_sub_right hB hU hA hmain hw
  · zqbaf
    zujra
    have he := Chain.sideCcw_east (A := N - t) (X := ((1 : ℝ), (0 : ℝ))) hU1 hU2 rfl one_pos
      by_simp_all hB (by
        unfold sideCross sideDot; grind)
    exact Chain.sideCcw_sub_left hB hmain he

/-- **The copy of a top vertex of `C₁` or `C₂` that carried a slit is a cut** (§2.2 (G2)/(G3)):
at a walk vertex of `C` whose corner is the slit corner `tour(2m'-1) → top' → tour(1)` of the
side chain `C'`, a top chord of `C` is attached. -/
theorem topglue_cut (J : Merge.Junction) (hP : J.P.Simple) (S₁ S₂ : Set ztf) {C' : Chain}
    (hP' : C'.P.Simple) {kt : ℕ} (hkt : kt ∈ topIdxs J) (hktm : kt ≤ J.whole.m)
    (hvert : J.whole.vertex kt = C'.top) {k : ℕ} (hk : k < (chainModel J.whole).W.n)
    (hprev : sidePrev (chainModel J.whole).W k 0 = C'.sideTour C'.sideBeta ztcsg)
    (hpt : (chainModel J.whole).W.vtx k = C'.top)
    (hnext : sideNext (chainModel J.whole).W k = C'.sideTour C'.sideBeta 1) :
    (chainModel J.whole).IsCut ztqu k := by
  obtain ⟨σ, hσ, hl⟩ := top_sector C' hP'
  have hpt' : sidePt (chainModel J.whole).W k 0 = J.whole.vertex kt := by
    rw [Chain.sidePt_zero, hpt, hvert]
  have hl' : sideLeft (chainModel J.whole).W k 0 (rayPt (J.whole.vertex kt) σ 1) := by
    unfold sideLeft; simp_all
  obtain ⟨hfree, hA⟩ := sideAttach_chordSet hP hk hktm hpt' hσ hl'
  exact ⟨_, Or.inr (Or.inl ⟨kt, hkt, σ, hσ, hfree, rfl⟩), k, 0, hA, by_simp⟩

/-! ## Cuts transfer from a side walk to the walk of `C` -/

/-- **Cut transfer along an agreement** (the walk embedding preserves cuts): a cut of `Sᵢ` at a
position of an agreeing stretch of the walk of the side chain `C'` gives a cut of the revised
fusion at the same offset of the walk of `C` — through the fused chord contained in the old
chord at its endpoint (`Merge.end_mem_fusion`), or through a shared chord if the endpoint is the
shared vertex. -/
theorem cut_transfer (J : Merge.Junction) (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple)
    {Si S' : Set ztf} (hsub : Si ⊆ Merge.augChords C')
    (hend : ∀ c ∈ Si, ztqh ∧
      ztqi)
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hA : WalkEmbed.Agree (chainModel J.whole).W (chainModel C').W g g' L)
    {d : ℕ} (hd : d < L) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hdt : 0 < (d : ℝ) + t)
    (hc : (chainModel C').IsCut Si ztxqk) :
    (chainModel J.whole).IsCut S' ztwvv := by
  zuog

  have hdt' : ztgaz := fun h => by
    zucpr
  obtain ⟨c, hcS, p, t', hA', hkey⟩ := hc
  obtain ⟨hpe, hte⟩ := Chain.sideKey_inj ht ht1 hA'.2.1 hA'.2.2.1 hkey
  subst hpe hte
  zufal

  have hq := hA'.2.2.2.1
  have hqd : ztslh := (walkAx_chainModel hP').trace _ hA'.1 t ht ht1.le
  obtain ⟨y, a, b, hH, hy, rfl, hl, hr⟩ := Merge.augChords_spec ztvwj
  have hqe : ztyza := by
    zubhe

    · zubui
      · exact absurd ztwl
          hqd
      grind
    grind
  zucgw

  · -- the endpoint is the shared vertex: a shared chord is attached here
    obtain ⟨r, hr0, hsec⟩ := hA'.2.2.2.2
    zudoh
    obtain ⟨σ, hσ, hdir⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        sideLeft W' p' t ztruz := by
      zuioq
      zusv
      zuchb

      · refine ⟨1, Or.inl rfl, (sideLeft_rayPt hε0).1 ztgke⟩
        · show rayPt q 1 ε ∈ _
          rw [hqa]; refine ztkw <;> zvnap <;> linarith
        · zqbao
        · zuhkz
      · refine ⟨-1, Or.inr rfl, (sideLeft_rayPt hε0).1 ztgke⟩
        · show rayPt q _ ε ∈ _
          rw [hqb]; refine ztkw <;> zvnap <;> linarith
        · zqbao
        · zuhky
    have hl2 : ztbalp := by
      zuika
    zuerm

    obtain ⟨hfree, hAt⟩ := sideAttach_shoot hP zthp ht ht1 hσ
      ztlid hl2
    zujjw
    exact ⟨_, hshared ztbkb, _, t, hAt, rfl⟩
  · zudrf

    · zuchs

      zqbai
    · zucht

      zqbai
end FuseMath
end
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqxi" : tactic => `(tactic| (have hn0 : ztbiy := by_omega
                                          have hwv : ztbrq := Chazelle.Chain.sidePt_zero _ _
                                          set v := M.W.vtx p with hv
                                          set a := M.W.vtx ztcm with ha))
local macro "zqxj" : tactic => `(tactic| (unfold sideDot; zumzm
                                          zunqe))
local macro "zqxk" : tactic => `(tactic| (intro x hx hxl
                                          obtain ⟨hxD, hxc⟩ := hsf x hx hxl
                                          zugsz

                                          exact hcut ztexz))
local macro "zqxl" : tactic => `(tactic| (have hwv : ztbrq := Chazelle.Chain.sidePt_zero _ _
                                          filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hsr
                                          zugvp
                                          exact hsub ztrsb))
local macro "zqxm" : tactic => `(tactic| (refine hchord x hx.1 hxs ?_
                                          intro hxF
                                          zuxo

                                          rw [hxs'] at h5))
local macro "zqxn" : tactic => `(tactic| (set s₂ := min ztcmw ztohc with hs₂
                                          have hs₂0 : ztrzm := lt_min by_linarith by_linarith))
local macro "zqxo" : tactic => `(tactic| (apply hxF
                                          refine ⟨by_grind, fun hxU => ?_⟩
                                          obtain ⟨s', hs'0, hxs'⟩ := hray x hx hxl hxU
                                          rw [hxs'] at hxs))
local macro "zqxp" : tactic => `(tactic| have hne : F.Nonempty := ⟨c, hc⟩)
local macro "zqxq" : tactic => `(tactic| obtain ⟨δ, hδU, hδ⟩ := (hf.and hs1).exists)
local macro "zqxr" : tactic => `(tactic| (rw [show p + n - 1 = ztoq + n by omega, Nat.add_mod_right]
                                          exact Nat.mod_eq_of_lt by_omega))
local macro "zqxs" : tactic => `(tactic| (rintro x hx hxl ⟨c', hc', hxc'⟩
                                          have hA'' := (hsf x by_grind hxl).2 c' hc' hxc'))
local macro "zqxt" : tactic => `(tactic| (filter_upwards [hoff] with s hs
                                          filter_upwards [hs] with δ hδ))
local macro "zqxu" : tactic => `(tactic| (zvmyh at hwc
                                          obtain ⟨s, hs0, hs1, he⟩ := Geometry.mem_segment_iff_lerp.1 hwc
                                          rcases hs0.lt_or_eq with hs0 | hs0))
local macro "zqxv" : tactic => `(tactic| (set b := M.W.vtx ztwjk with hb
                                          have hbv : ztpln := by_grind))
local macro "zqxw" : tactic => `(tactic| refine ⟨⟨hS1, hHc, hoff⟩, fun s hs hsr => ⟨?_, ?_⟩⟩)
local macro "zqxx" : tactic => `(tactic| obtain ⟨X, hX, l, r, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hFam hpos hcut)
local macro "zqxy" : tactic => `(tactic| rwa [prev_succ_mod hp] at this)
local macro "zqxz" : tactic => `(tactic| have hne := hM.nd p hp)
local macro "zqya" : tactic => `(tactic| obtain ⟨r, hr, hsf⟩ := sector_free hM hF hfin hp ht ht1)
set_option hygiene true

/-!
# The sweep (WP-D), part 2: local shooting

**Local shooting** (p. 502): a point `z` whose horizontal ray starts inside a region `U` of a
submap sees a point of one of the arcs of `U`.  So the first hit of the ray on the boundary of the
domain is the earliest of the first hits on the arcs of `U`, each of which one call of the ray
shooter (`ShooterOK`) answers: this is how the sweep answers every query, in the model of `C₁`
and in the model of `C₂` (tests (i), (ii) and the local shooting of pp. 502–507).

## Generic part (any good model)

* `sector_free`: near a walk position, the points of its open left sector are in the domain, and
  the only chords of a finite admissible family through them are attached at that position.
* `hit_mem_arcSet`: if the points of a horizontal ray approaching a walk position from inside its
  left sector lie in the region `U`, then the point of the position lies on (the closure of) an
  arc of `U` (`Model.arcSet`).  Four cases: inside a walk edge or at a walk vertex, with or
  without a chord of the family attached at the position (then the key is the end of an arc).
* `ray_mem_region_of_arc`, `ray_mem_region_after`, `ray_mem_region_before` (with `sub_sector`):
  conversely, the ray *leaving* a walk position into its left sector starts in the region of the
  arc around the position's key (non-cut key), or, at a cut walk vertex whose chords avoid the
  ray, in the region of the arc beginning (the ray turns counterclockwise from the next walk edge)
  or ending (clockwise from the previous walk edge) there.  This is what double identification
  (`LocateSpec`) gives a query in its own chain.

## Chain models

* `ray_subset_region`: in the chain model, a ray whose initial part is in a region `U` stays in
  `U` up to its first hit (regions are closed under visibility).
* `local_shoot`: the first-hit point of such a ray lies on an arc of `U`
  (coverage of the hit point by a walk position: `Chain.sideSees_chordEnd`).
* `arcSet_subset_compl_dom`: arcs are outside the domain.
* `firstHit_arcs`: **the first hit on the union of the arcs of `U` is the first hit of the
  chain** — the correctness of local shooting through the ray shooter.
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn sideLeft_edge sideLeft_zero sideLeft_not_self sideKey_inj
  sideCcw_smul)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset SectorSide)
namespace Sweep
theorem rayPt_sub (w : Point) (τ s : ℝ) : rayPt w τ s - w = s • (ztkn : Point) := by
  zuhbh

/-- A left sector is a cone: if one point of a horizontal ray from the point of a position is in
it, every point of the ray is. -/
theorem sideLeft_rayPt_iff (W : Polygon) (p : ℕ) (t : ℝ) (τ : ℝ) {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') :
    sideLeft W p t (rayPt ztia τ s) ↔ sideLeft W p t (rayPt ztia τ s') := by
  zuhrd
  rw [rayPt_sub, rayPt_sub, sideCcw_smul hs, sideCcw_smul hs']

/-! ## The sector near a position -/
section Generic
variable {M : Model}

/-- **The sector near a position is free except for the chords attached there.**  Near the point
of a walk position, the points of its open left sector are in the domain, and a chord of a finite
admissible family through such a point is attached at that position. -/
theorem sector_free (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    ∃ r > 0, ∀ x ∈ ball ztbp r, sideLeft M.W p t x →
      x ∈ M.D ∧ ∀ c ∈ F, x ∈ c → SideAttach M.W c p t := by
  obtain ⟨r₀, hr₀, hcl⟩ := hM.clean p hp t ht ht1
  zubzh
  zqxz
  have hwD := hM.trace p hp t ht ht1.le
  have hc : ∀ c ∈ F, ∀ᶠ x in 𝓝 w, sideLeft M.W p t x → x ∈ c → SideAttach M.W c p t := by
    intro c hcF
    obtain ⟨a, b, hab, hcab, hy, hopen, ha, hb⟩ := hM.ends c ztgjz
    by_cases hwc : w ∈ c
    · have hwab : w = a ∨ w = b := by
        zqxu
        · zuji
          · grind
          simp_all
        · left; zunfe
      have hWE : WalkEnd M.W c w := by
        grind
      obtain ⟨⟨p', t', hA', hpt'⟩, hdisj⟩ := hWE
      by_cases hsame : p' = p ∧ t' = t
      · obtain ⟨rfl, rfl⟩ := hsame
        exact Eventually.of_forall by_grind
      · have hne' : p' = p → t' ≠ t := by_grind
        obtain ⟨r₁, hr₁, h₁⟩ := hdisj p' p t' t hA'.1 hA'.2.1 hA'.2.2.1 hp ht ht1 hne' hpt' rfl
        obtain ⟨r₂, hr₂, h₂⟩ := hA'.2.2.2.2
        filter_upwards [ball_mem_nhds w ztftb] with x hx hxl hxc
        exfalso
        have hxw : x ≠ sidePt M.W p' t' := by
          zuogy
          zunq
          exact sideLeft_not_self hne ht1 hxl
        have hx2 : dist x ztrww < r₂ := by
          zuogy; exact lt_of_lt_of_le hx ztgh
        exact h₁ x ztzve (h₂ x hxc hxw hx2) hxl
    · have hcl' : IsClosed c := by zvmyh; exact Geometry.isClosed_segment _ _
      filter_upwards [hcl'.isOpen_compl.mem_nhds hwc] with x hx _ hxc
      simp_all
  have hall := (hfin.eventually_all).2 hc
  obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff.1 (hall.and (ball_mem_nhds w hr₀))
  refine ⟨r, hr, fun x hx hxl => ⟨?_, fun c hc hxc => (hsub hx).1 c hc hxl hxc⟩⟩
  zujuk
  exact hcl x (hsub hx).2 hxD hxl
end Generic

/-- A preconnected free set meeting a region lies in it. -/
theorem subset_region {D : Set Point} {F : Set ztf} {U : Set Point}
    (hU : U ∈ regionsIn D F) {H : Set Point} (hH : IsPreconnected H) (hHf : H ⊆ freeIn D F)
    {x : Point} (hxH : x ∈ H) (hxU : x ∈ U) : H ⊆ U := by
  rw [Chazelle.Chain.regionsIn_eq_component hU hxU]
  exact hH.subset_connectedComponentIn hxH hHf

/-- A walk position whose key is in the closed arc `[a, b]` has its point in `arcSet a b`. -/
theorem mem_arcSet_of_key {M : Model} {a b : ℝ} {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (h : sideInArc a b ztk ∨ (p : ℝ) + t = a ∨ (p : ℝ) + t = b) :
    sidePt M.W p t ∈ M.arcSet a b :=
  ⟨p, t, hp, ht, ht1, h, rfl⟩

/-- Keys just after a key inside an open cyclic interval are inside it. -/
theorem sideInArc_eventually_add {a b x : ℝ} (h : sideInArc a b x) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc a b ztkgy := by
  zusg
  zudwd
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT zthki]
      with s hs hs'
    grind
  · zuy
    · zusq
      grind
    · filter_upwards [Ioo_mem_nhdsGT ztitg] with s hs
      grind

/-- The keys just before the end of an interval are inside it. -/
theorem sideInArc_before_end {l r : ℝ} (_hlr : l ≠ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc l r zttxh := by
  zufdq
  zus
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ztto]
      with ε hε hε'
    grind
  · zulg
    simp_all
section Generic2
variable {M : Model}

/-- **A chord attached at the point of a ray's approach goes the other way.**  If a chord of an
admissible family is attached at a walk position `w` and the points of the horizontal ray from
`w` in direction `τ` eventually avoid it, then the chord is the segment from `w` of some length
`d > 0` in direction `-τ`, and its open part is in the domain. -/
theorem attached_opposite (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hav : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∉ c) :
    ∃ d > (0 : ℝ), (∀ x ∈ c, ∃ s, 0 ≤ s ∧ s ≤ d ∧ x = rayPt ztbp (-τ) s) ∧
      (∀ s, 0 < s → s < d → rayPt ztbp (-τ) s ∈ M.D) ∧
      (∀ s, 0 < s → s < d → rayPt ztbp (-τ) s ∈ c) := by
  zubzh
  have hwD := hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
  obtain ⟨a₀, b₀, hab, hcab, hy, hopen, -, -⟩ := hM.ends c hc
  have hwc : ztsmv := hA.2.2.2.1
  -- the chord is the segment from `w` to its other end `e`
  obtain ⟨e, hce, hey, hwe, hopen'⟩ : ∃ e : Point, c = Chazelle.segment w e ∧ e.2 = w.2 ∧
      w ≠ e ∧ ∀ s ∈ Ioo (0 : ℝ) 1, lerp w e s ∈ M.D := by
    zqxu
    · zuji
      · grind
      · have hwb : w = b₀ := by_simp_all
        refine ⟨a₀, by rw [hcab, hwb, Geometry.segment_comm], by_simp_all, by
          grind, ?_⟩
        rw [hwb]; exact WalkAx.open_rev hopen
    · have hwa : w = a₀ := by zunfe
      grind
  have hδ : e.1 - w.1 ≠ 0 := by
    grind
  have hττ : ztgux := by_grind
  have hlerp : ∀ u : ℝ, lerp w e u = ((w.1 + u * ztjun, w.2) : Point) := by
    intro u; apply point_ext <;> simp [lerp, hey]
  -- the chord does not go in direction `τ`
  have hneg : τ * ztjun < 0 := by
    zujuj

    have hpos' := lt_of_le_of_ne hpos (by
      grind)
    obtain ⟨s, hs1, hs2⟩ := (hav.and (Ioo_mem_nhdsGT hpos')).exists
    apply hs1
    zujir
    have e1 : rayPt w τ s = lerp w e (s / ztbabk) := by
      zugva
      zubjw
      · zudlo
        grind
      · simp
    zukd
    exact Geometry.lerp_mem_segment _ _ (div_nonneg hs2.1.le hpos'.le)
      ((div_le_one hpos').2 hs2.2.le)
  set d := -ztbabk with hd
  have hdpos : ztphr := by_linarith
  have hrel : ∀ u : ℝ, lerp w e u = rayPt w (-τ) (u * d) := by
    zulnl
    zugva
    zubjw
    · simp only [rayPt_fst, hd]
      grind
    · simp
  refine ⟨d, hdpos, ?_, ?_, ?_⟩
  · zuh
    zvnme at hx
    obtain ⟨u, hl0, hl1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
    exact ⟨u * d, by_positivity, by_nlinarith, hrel u⟩
  · zuetg
    have := hopen' _ ⟨by_simp_all, (div_lt_one hdpos).2 hs1⟩
    grind
  · zuetg
    zujir
    have := Geometry.lerp_mem_segment w e (div_pos hs0 hdpos).le ((div_le_one hdpos).2 hs1.le)
    grind
end Generic2

/-! ## Arcs through a position -/
section Arcs
variable {M : Model}
variable {n p : ℕ}
/-- The walk vertex before `p`, followed by one step, is `p`. -/
theorem prev_succ_mod (hp : p < n) : ztxhn % n = p := by
  zucym
  · have h1 : ztblb := by
      simp
    rw [h1, Nat.sub_add_cancel by_omega, Nat.mod_self]
  · have h1 : ztxfl := by
      zqxr
    rw [h1, Nat.sub_add_cancel hp0]
    exact Nat.mod_eq_of_lt hp

/-- For `1 ≤ p`, the walk vertex before `p` is `p - 1`. -/
theorem prev_mod (hp : p < n) (hp0 : 1 ≤ p) : ztzp % n = p - 1 := by
  zqxr

/-- **A non-cut position inside an edge facing `U`** has its point on an arc of `U`. -/
theorem arc_of_faces_edge (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F ztk) (hf : M.Faces p t U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p t ∈ M.arcSet a b := by
  zukep
  zqxx
  zuddd

  zulsx
  exact ⟨l, r, harc, mem_arcSet_of_key hp ht.1.le ht.2.le (Or.inl hin)⟩

/-- **A non-cut walk vertex whose next positions face `U`** is on an arc of `U`. -/
theorem arc_of_faces_after (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    (hp0 : 0 < p) (hcut : ¬ M.IsCut F p) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p 0 ∈ M.arcSet a b := by
  zukeq
  zqxx
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and ztkfe).and ztctd).exists
  zuddc

  zulsx
  exact ⟨l, r, harc, mem_arcSet_of_key hp le_rfl zero_le_one by_simp_all⟩

/-- **A cut walk vertex whose next positions face `U`** starts an arc of `U`. -/
theorem arc_of_attach_after (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hA : SideAttach M.W c p 0)
    {U : Set Point} (hU : U ∈ M.regions F) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p 0 ∈ M.arcSet a b := by
  zubot
  zqxp
  zufij
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and ztqdf).and ztctd).exists
  zucaq

  subst hUU
  exact ⟨_, r, harcU, mem_arcSet_of_key hA.1 le_rfl zero_le_one by_simp_all⟩

/-- **A cut walk vertex whose previous positions face `U`** ends an arc of `U`. -/
theorem arc_of_attach_before (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hp0 : 1 ≤ p)
    (hA : SideAttach M.W c p 0) {U : Set Point} (hU : U ∈ M.regions F)
    (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ztoq zteb U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p 0 ∈ M.arcSet a b := by
  zubop
  zqxp
  zufik
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and (sideInArc_before_end hlk)).and ztctd).exists
  have hcast : ztxbb := by
    simp_all
  have hin : sideInArc l ztmm ((p - 1 : ℕ) + zteb) := by_simp_all
  have hp1 : p - 1 < M.W.n := by have := hA.1; omega
  have hfV' := harcV.2.2.2.2.2.2 _ _ hp1 by_simp_all by_simp_all
    hin
  zuhxs
  subst hVV
  exact ⟨l, _, harcV, mem_arcSet_of_key hA.1 le_rfl zero_le_one by_simp_all⟩
end Arcs

/-! ## The hit point lies on an arc of the region -/
section Hit
variable {M : Model}

/-- The distance from `w` of a point of a horizontal ray from `w`. -/
theorem dist_rayPt (w : Point) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) {s : ℝ} (hs : 0 ≤ s) :
    dist (rayPt w τ s) w = s := by
  zutq
  simp only [rayPt_fst, rayPt_snd, add_sub_cancel_left, sub_self, abs_zero]
  zujj
  · simp_all
  simp_all

/-- Unfolding a corner sector. -/
theorem sideLeftOf_iff (a v b x : Point) :
    sideLeftOf a v b x ↔ sideCcw ztfd ztsq ztgg := Iff.rfl
variable (B : Point) (τ : ℝ)
/-- The opposite horizontal direction reverses cross and dot products. -/
theorem sideCross_neg_dir :
    sideCross B (ztdx : Point) = -sideCross B (ztkn : Point) := by
  zujqx
theorem sideDot_neg_dir :
    sideDot B (ztdx : Point) = -sideDot B (ztkn : Point) := by
  unfold sideDot; ring

/-- A horizontal direction strictly counterclockwise from `B` (less than a half turn) lies in the
sector from `B` to the opposite direction. -/
theorem ccw_half_left {B : Point} {τ : ℝ} (h : 0 < sideCross B (ztkn : Point)) :
    sideCcw B (ztkn : Point) (ztdx : Point) := by
  zuhl
  refine ⟨?_, Or.inl h⟩
  rw [sideCross_neg_dir]; linarith

/-- A horizontal direction strictly clockwise from `A` (less than a half turn) lies in the sector
from the opposite direction to `A`. -/
theorem ccw_half_right {A : Point} {τ : ℝ} (h : 0 < sideCross (ztkn : Point) A) :
    sideCcw (ztdx : Point) (ztkn : Point) A := by
  zuhl
  refine ⟨?_, Or.inr h⟩
  have e : sideCross (ztdx : Point) A = -sideCross (ztkn : Point) A := by
    zujqx
  simp_all

/-- The full-turn degenerate case of the dichotomy. -/
theorem cross_dir_aux {B A : Point} {τ : ℝ} (h1 : sideCross B A = 0) (h2 : 0 < sideDot B A)
    (h3 : sideCross B (ztkn : Point) < 0) : 0 < sideCross (ztkn : Point) A := by
  unfold sideCross sideDot at *
  simp only at *
  have e : τ * A.2 * ztdfh = ztufi * ztely := by
    grind
  have hb : 0 < τ * B.2 := by_linarith
  have hS : 0 < B.1 ^ 2 + B.2 ^ 2 := by
    have : ztsan := by rintro h; simp_all
    positivity
  have hP : 0 < ztufi * ztely := by_simp_all
  zvmyr at hP
  nlinarith [hP, hS]

/-- **The first-hit point lies on an arc of the region** (generic good model).  Let the points
of the horizontal ray from the point `w` of a walk position `(p, t)` in direction `τ` lie in the
left sector of the position and, near `w`, in the region `U` of an admissible family.  Then `w`
lies on the closure of an arc of `U`.  (Proof: near `w` the sector is free except for the chords
attached at the position; such a chord goes in direction `-τ`, which forces `t = 0` and splits the
sector at the chord; the part containing the ray lies in `U` and contains the offsets of the
positions just after or just before the position, whose arcs then belong to `U`.) -/
theorem hit_mem_arcSet (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hkey : 0 < (p : ℝ) + t) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : ∀ s > 0, sideLeft M.W p t ztxon)
    (happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p t ∈ M.arcSet a b := by
  zubm
  zubl

  zqya
  zubdr
  zqxz
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ ball ztbp r := by
    zuclm
    zudak

  zubud

  -- the chords through the ray near `w` avoid it
  have havoid : ∀ c ∈ F, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∉ c := by
    zung
    zudxn

  zujtd
  · -- a chord is attached at the position
    zuhb

    -- a point of the chord near `w`
    zqxn
    have hs₂d : ztsml := lt_of_le_of_lt ztff by_linarith
    zuial
    have hx₂ : ztwyk := by
      zudsr
      · zuq
        have := congrArg Prod.fst h
        zudv
        zubll
      · zuczr
    -- the position is a walk vertex
    have ht0 : ztbhh := by
      zubiy

      have hw0 : ztycn :=
        Geometry.det_lerp_self _ _ _
      zuqc

    zudlw
    have hp1 : 1 ≤ p := by
      have : ztfzn := by_grind
      zufc
    zqxi
    zqxv
    have hav : ztiyw := by
      have := hM.nd _ ztwwc
      zqxy
    zuyp

    have hsecv : ztjbo :=
      fun x => sideLeft_zero _ _ _
    zuwk
    have hdm0 : ztxfe := by
      zuqm
      grind
    have hvdm : ztwyl := by
      grind
    have hdp : ztxby := by
      have := (hsecv _).1 ztfsl
      zurl
    have hdm : ztxbx := by
      have := (hsecv _).1 hx₂
      zubin
    -- the edge after the vertex does not go along the chord
    have hBdm : ¬ (sideCross ztfd (ztdx : Point) = 0 ∧
        0 < sideDot ztfd (ztdx : Point)) := by
      zubf
      zuxa
      have hb2 : ztplo := by
        grind
      zuhn

      zufvo
      zudpf
      zuck

      have e : ztccd := by
        zucky
        zubjw
        · zudcf
          have h3 : ztwwu := by
            zubyn
            zujcd
          linarith
        · zuqb

      zubuu
    -- the ray is on one side of the chord
    have hdich : ztwre := by
      zudl
      · grind
      · zucvi
      · grind
      · zucyt
        · zuist
        · zugkk
          zujh
          · grind
          · zubyz

        grind
    -- chord points through the sector are on the chord's ray
    have hchord : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∉ ⋃₀ F →
        x ∈ freeIn M.D F := by
      zuetk

    have hray : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∈ ⋃₀ F →
        ∃ s' : ℝ, 0 ≤ s' ∧ x - v = s' • (ztdx : Point) := by
      zqxs
      zueh

    zubfa

    · -- the ray is between the edge after the vertex and the chord
      obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hvdm hbv (S := ∅) hr
        ztbqd
      have hHsec : ∀ x ∈ ball v r ∩ {x | sideLeftOf ztwji v b x},
          sideCcw ztfd ztsq (ztdx : Point) := by
        zuh
        zuhdj
        zuof
      have hHfree : ball v r ∩ {x | sideLeftOf ztwji v b x} ⊆
          freeIn M.D F := by
        zuh
        have hxs :=
          (hsecv x).2 ztgdj
        zqxm
        zugan
        · zubag
        · zqxj
      have hs₁H : ztbajs := by
        zujfx
        show sideLeftOf _ v b _
        zuns
        zuisw
      zubwe
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U := by
        zqxt
        have := hHU hδ.2
        zubvd
      exact arc_of_attach_after hM hF hfin hcF hA' hU hf
    · -- the ray is between the chord and the edge before the vertex
      obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hvdm (S := ∅) hr
        ztbqd
      have hHsec : ∀ x ∈ ball v r ∩ {x | sideLeftOf a v ztwji x},
          sideCcw (ztdx : Point) ztsq ztgg := by
        zuh
        zueph
        zuof
      have hHfree : ball v r ∩ {x | sideLeftOf a v ztwji x} ⊆
          freeIn M.D F := by
        zuh
        have hxs :=
          (hsecv x).2 ztfba
        zqxm
        zugam
        · zubag
        · zqxj
      have hs₁H : ztbajr := by
        zujfx
        show sideLeftOf a v _ _
        zuns
        zuisx
      zubwe
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ztoq zteb U := by
        zqxt
        have := hHU hδ.1
        zucqb
        show Jordan.offset ztffo ztffo _ δ ∈ U
        zubsi

      exact arc_of_attach_before hM hF hfin hcF hp1 hA' hU hf
  · -- no chord is attached at the position
    have hfreeS : ztwnw := by
      zqxk
    zubhu
    · -- inside a walk edge
      zufwm
      have hHc : IsPreconnected (ball ztbp r ∩
          {x : Point | 0 < 1 * det ztoy ztbakv x}) :=
        ((convex_ball _ r).inter zthqu).isPreconnected
      have hHfree : ball _ r ∩
          {x : Point | 0 < 1 * det _ _ x} ⊆
          freeIn M.D F := fun x hx =>
        hfreeS x hx.1 ztyhc
      have hs₁H : rayPt _ τ s₁ ∈ ball _ r ∩
          {x : Point | 0 < 1 * det _ _ x} :=
        ⟨hs₁B, by simpa using (sideLeft_edge hne ht' _).1 by_grind⟩
      zudhg
      have hf : ztuln := by
        zuepc

      exact arc_of_faces_edge hGM hFam hU hp ht' hcut hf
    · -- at a walk vertex
      zudlw
      have hp0 : 0 < p := by
        simp_all
      zqxi
      zqxv
      have hav : ztiyw := by
        have := hM.nd _ ztwwc
        zqxy
      zuzf
      have hHfree : ztddz := fun x hx =>
        hfreeS x ztdyx ztdxy
      have hs₁H : ztdar := by
        zuevy
        have := hsec s₁ hs₁pos'
        zubmc

      zuhed
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U := by
        zqxt
        have := hHU hδ.2
        zubvd
      exact arc_of_faces_after hGM hFam hU hp hp0 by_grind hf
end Hit

/-! ## The region of a ray leaving a walk position -/
section Leave
variable {M : Model}

/-- **The ray leaving a position inside an arc** starts in the region of the arc: if the key of
the walk position `(p, t)` is inside an arc of `U` and the direction `τ` points into the left
sector of the position, the initial part of the ray is in `U`.  (Used after double
identification, `LocateSpec`, for the local shooting of a query in its own chain.) -/
theorem ray_mem_region_of_arc (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {a b : ℝ} (harc : M.IsArc F U a b)
    (hin : sideInArc a b ztk) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p t ztznq) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ U := by
  zubm
  zubl

  zqxz
  have hcut : ztpqv := harc.2.2.2.2.2.1 _ hin
  zqya
  have hfreeS : ztwnw := by
    zqxk
  have hsec' : ∀ s > 0, sideLeft M.W p t (rayPt _ τ s) :=
    fun s hs => (sideLeft_rayPt_iff _ p t τ one_pos hs).1 hsec
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ ball ztbp r ∧
      0 < s := by
    zuclm
    refine ⟨?_, hs⟩
    zudak

  -- the sector near the position is a preconnected free set containing faced points
  obtain ⟨H, hHc, hHfree, hHsec, hHU⟩ : ∃ H : Set Point, IsPreconnected H ∧ H ⊆ freeIn M.D F ∧
      (∀ x ∈ ball ztbp r, sideLeft M.W p t x → x ∈ H) ∧ (∃ x ∈ H, x ∈ U) := by
    zubhu
    · zufwm
      refine ⟨ball _ r ∩
          {x : Point | 0 < 1 * det ztoy ztbakv x},
        ((convex_ball _ r).inter zthqu).isPreconnected,
        fun x hx => hfreeS x hx.1 ((sideLeft_edge hne ht' x).2 by_simp_all),
        fun x hx hxl => ⟨hx, by simpa using (sideLeft_edge hne ht' x).1 hxl⟩, ?_⟩
      have hf := harc.2.2.2.2.2.2 p t hp ht0 ht1 hin
      obtain ⟨δ, hδU, hδ⟩ := (hf.and (hM.eventually_offset_left hp ht' hr)).exists
      exact ⟨_, ztdxj, hδU⟩
    · zudlw
      zudou
      zuiav
      have hbv : M.W.vtx _ ≠ M.W.vtx p := fun h => hne h.symm
      have hav : M.W.vtx ztcm ≠ M.W.vtx p := by
        have := hM.nd _ ztwwc
        zqxy
      obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hbv (S := ∅) hr by_simp_all
      refine ⟨_, hHc, fun x hx => hfreeS x ztdyx
        ztdxy, fun x hx hxl => ⟨by_grind,
        (sideLeft_zero _ _ _).1 hxl⟩, ?_⟩
      obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
        ((hoff.and ztkfe).and ztctd).exists
      have hf := harc.2.2.2.2.2.2 p s hp hs3.1 hs3.2 (by
        grind)
      zqxq
      refine ⟨_, hδ.2, ?_⟩
      zvohi; tauto
  obtain ⟨x₀, hx₀H, hx₀U⟩ := hHU
  have hsub := subset_region hU hHc hHfree hx₀H hx₀U
  filter_upwards [hball] with s hs
  tauto

/-- **The two sides of the chords at a walk vertex.**  At a walk vertex `(p, 0)` where the chords
of `F` attached there avoid the ray from its point in direction `τ` (which lies in the left
sector), and some chord of `F` is attached there, the part of the sector after the chords (the
side of the next walk edge, if `τ` turns counterclockwise from it) or before them (the side of the
previous walk edge) is a preconnected free set containing the ray. -/
theorem sub_sector (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hnot : ∀ c ∈ F, SideAttach M.W c p 0 → ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∉ c)
    {c : Set Point} (hc : c ∈ F) (hA : SideAttach M.W c p 0) :
    ∃ r > 0,
      (0 < sideCross ztbajf (ztkn : Point) →
        SectorSide (freeIn M.D F)ᶜ
          (ball ztoy r ∩ {x | sideLeftOf ztwpa ztoy
            ztbakv x})
          ztwpa ztoy ztbakv 1 ∧
        ∀ s > 0, s < r → rayPt ztoy τ s ∈ ball ztoy r ∩
          {x | sideLeftOf ztwpa ztoy
            ztbakv x}) ∧
      (0 < sideCross (ztkn : Point) ztwll →
        SectorSide (freeIn M.D F)ᶜ
          (ball ztoy r ∩ {x | sideLeftOf ztxvg ztoy
            ztwpa x})
          ztxvg ztoy ztwpa 1 ∧
        ∀ s > 0, s < r → rayPt ztoy τ s ∈ ball ztoy r ∩
          {x | sideLeftOf ztxvg ztoy
            ztwpa x}) := by
  zuqu
  zqxz
  zqxi
  zufah

  have hav : ztiyw := by
    have := hM.nd _ ztwwc
    zqxy
  zuyp

  have hsecv : ztwyo :=
    fun x => sideLeft_zero _ _ _
  have hdm0 : ztxfe := by
    zuqm
    rcases hτ with rfl | rfl <;> norm_num at this
  have hvdm : ztwyl := by
    grind
  -- the chord is along `-τ`, so `-τ` is in the sector
  obtain ⟨d, hd, -, -, hcmem⟩ := attached_opposite hM ztlz hA hτ (hnot c hc hA)
  obtain ⟨r₃, hr₃, hcl⟩ := hA.2.2.2.2
  zqxn
  have hx₂ : ztxtj := by
    refine hcl _ (hcmem s₂ hs₂0 ztyrj) ?_ ?_
    · zuq
      have := congrArg Prod.fst h
      zudv
      zubll
    · zunfp
      exact lt_of_le_of_lt ztgh by_linarith
  have hdm : ztxbx := by
    have := (hsecv _).1 hx₂
    zubin
  have hray : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∈ ⋃₀ F →
      ∃ s' : ℝ, 0 ≤ s' ∧ x - v = s' • (ztdx : Point) := by
    zqxs
    obtain ⟨d', -, hpts, -, -⟩ := attached_opposite hM ztesy hA'' hτ (hnot c' hc' hA'')
    obtain ⟨s', hs'0, -, hxs'⟩ := hpts x hxc'
    exact ⟨s', hs'0, by rw [hxs', hwv, rayPt_sub]⟩
  have hsecr : ∀ s > 0, sideLeft M.W p 0 (rayPt v τ s) := by
    zugg
    have := (sideLeft_rayPt_iff _ p 0 τ one_pos hs).1 hsec
    grind
  refine ⟨r, hr, ?_, ?_⟩
  · zuq
    have hS : ∀ x ∈ ball v r, x ∈ (freeIn M.D F)ᶜ →
        ¬ sideLeftOf ztwji v b x := by
      zueti

      have hxl := (hsecv x).2 (Chazelle.Chain.sideCcw_sub_left hB0 hdm hxs)
      zqxo
      refine Chazelle.Chain.sideCcw_not_ray_right hdm0 ?_ ?_ hxs
      · zubag
      · zqxj
    obtain ⟨hS1, hHc, hoff⟩ := Chazelle.Chain.sideSector hvdm hbv hr hS
    zqxw
    · zugez
    · show sideLeftOf _ v b _
      zugfj
      zuisw
  · zuq
    have hS : ∀ x ∈ ball v r, x ∈ (freeIn M.D F)ᶜ →
        ¬ sideLeftOf a v ztwji x := by
      zueti

      have hxl :=
        (hsecv x).2 (Chazelle.Chain.sideCcw_sub_right hB0 hdm0 hA0 hdm hxs)
      zqxo
      refine Chazelle.Chain.sideCcw_not_ray_left hdm0 ?_ ?_ hxs
      · zubag
      · zqxj
    obtain ⟨hS1, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hvdm hr hS
    zqxw
    · zugez
    · show sideLeftOf a v _ _
      zugfj
      zuisx

/-- **The ray leaving a cut vertex on the side of the next edge** starts in the region of the arc
beginning at the vertex (the chords attached there avoid the ray). -/
theorem ray_mem_region_after (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {b : ℝ} (harc : M.IsArc F U ztcfa b) {c : Set Point} (hc : c ∈ F)
    (hA : SideAttach M.W c p 0) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hnot : ∀ c ∈ F, SideAttach M.W c p 0 → ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∉ c)
    (hcross : 0 < sideCross ztbajf (ztkn : Point)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∈ U := by
  zubm
  obtain ⟨r, hr, hafter, -⟩ := sub_sector hM hFam.2.1 hFam.1 hp hτ hsec hnot hc hA
  obtain ⟨⟨hS1, hHc, hoff⟩, hrayH⟩ := hafter hcross
  zqxp
  obtain ⟨-, -, hkb⟩ := WalkAx.arc_cuts hne harc
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and ztved).and ztctd).exists
  have hf := harc.2.2.2.2.2.2 p s hp hs3.1 hs3.2 (by
    grind)
  zqxq
  have hfree : ball _ r ∩ {x | sideLeftOf _ _
      _ x} ⊆ freeIn M.D F := fun x hx => by
    zujpj
  have hsub := subset_region hU hHc hfree hδ.2 ztnui
  zqxl

/-- **The ray leaving a cut vertex on the side of the previous edge** starts in the region of the
arc ending at the vertex. -/
theorem ray_mem_region_before (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    (hp1 : 1 ≤ p) {a : ℝ} (harc : M.IsArc F U a ztcfa) {c : Set Point} (hc : c ∈ F)
    (hA : SideAttach M.W c p 0) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 ztwph)
    (hnot : ∀ c ∈ F, SideAttach M.W c p 0 → ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∉ c)
    (hcross : 0 < sideCross (ztkn : Point) ztwll) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs τ s ∈ U := by
  zubm
  zubay

  zqxp
  zufii
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and (sideInArc_before_end hak)).and ztctd).exists
  have hcast : ztxbb := by
    rw [Nat.cast_sub hp1]; simp
  have hf : ztpko := harc.2.2.2.2.2.2 ztoq zteb by_omega
    by_grind by_grind by_grind
  zqxq
  have hfree : ball _ r ∩ {x | sideLeftOf _
      _ _ x} ⊆ freeIn M.D F := fun x hx => by
    zujpj
  have hδU' : Jordan.offset ztxvg ztoy zteb ztckn ∈ U := by
    rw [one_mul, prev_mod hp hp1]
    have e : M.W.vtx p = M.W.vtx ((p - 1 + 1) % M.W.n) := by
      rw [Nat.sub_add_cancel hp1, Nat.mod_eq_of_lt hp]
    zudtv
  zuhfq
  zqxl
end Leave

/-! ## Chain models -/
section ChainModel
variable (C : Chain)
/-- **Regions are closed under visibility, along a ray.**  If the open stretch `(0, T)` of a
horizontal ray is in the domain of a chain and its initial part is in the region `U` of an
augmented family, the whole stretch is in `U`. -/
theorem ray_subset_region {F : Set ztf} (hF : F ⊆ Merge.augChords C)
    {U : Set Point} (hU : U ∈ regionsIn C.dom F) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {T : ℝ} (hT : 0 < T) (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ C.dom)
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) :
    ∀ t, 0 < t → t < T → rayPt z σ t ∈ U := by
  zubdr
  have hIc : ztlxh :=
    isPreconnected_Ioo.image _ (Chazelle.Visibility.continuous_rayPt z σ).continuousOn
  have hIfree : rayPt z σ '' Ioo 0 T ⊆ freeIn C.dom F := by
    zucze

    obtain ⟨y, a, b, h, -, rfl, -, -⟩ := Merge.augChords_spec ztgjz
    zucnx

    -- every point of the ray before `t₀` is on the chord
    have hall : ztfxm := by
      zufib

      · zur
        · zube

          apply h.left_not
          have := hdom ztten by_linarith by_grind
          zuckt
        grind
      · zur
        · linarith
        · zube

          apply h.right_not
          have := hdom ztuev by_linarith by_grind
          zuckt
    zucoi

  zucbp

/-- The walk of a chain model lies outside its domain, so every arc does. -/
theorem arcSet_subset_compl_dom (hP : C.P.Simple) (a b : ℝ) :
    (chainModel C).arcSet a b ⊆ C.domᶜ := by
  rintro x ⟨p, t, hp, ht0, ht1, -, rfl⟩
  exact (FactsChain.walkAx C hP).trace p hp t ht0 ht1

/-- **Local shooting in a chain model.**  If the initial part of the horizontal ray from `z`
(at a height not above the top of the chain) lies in the region `U` of an admissible family, then
the first-hit point of the ray lies on an arc of `U`. -/
theorem local_shoot (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {U : Set Point} (hU : U ∈ (chainModel C).regions F)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) :
    ∃ a b, (chainModel C).IsArc F U a b ∧
      rayPt z σ ztbtm ∈ (chainModel C).arcSet a b := by
  zuixf
  have hUfree := Chazelle.Chain.regionsIn_subset hU'
  have hfree := hini.mono fun t ht => (hUfree ht).1
  obtain ⟨hT, hwD, hdom⟩ := Merge.hit_of_freeAt C hz hσ hfree
  zuckj
  zuhom
  have hray := ray_subset_region C hFam.2.1 hU' hσ hT hdom hini
  zukv
  have hback : ztxpz := by
    intro s; apply point_ext <;> simp [rayPt, hw]; ring
  -- the height is inside the box
  have hzR : ztmxi := by
    have := C.dom_subset_box ztxoe
    zugie
  -- the hit point is on the chain or on a vertical side of the box
  have he : ztdea := by
    rcases (Merge.not_mem_dom_iff C by_simp_all).1 hwD with h | h
    · zulpb

      · zuum

        zueek
        zucmx
        have hεT : ztmxk := by_grind
        have hbox := C.dom_subset_box ztyfb
        have h1 : |(rayPt z σ _).1| < C.radius := hbox.1
        have h2 : ztxpx := by
          zuega
          zui
          zuxs

        grind
      · zube

        exact h ⟨hlt, by_simp_all⟩
    simp_all
  -- a walk position at the hit point whose sector contains the backward ray
  zufua
  have hee : ztwym := by
    grind
  have hopen : ztbajt := by
    zugg
    have e : ztbann := by
      zubvk
    zui
    zuhct
  obtain ⟨p, t, hp, ht, ht1, hpt, hl⟩ :=
    C.sideSees_chordEnd hP C.sideBeta hee by_simp hopen he
  zuiv
  zukeu
  have hsec : ∀ s > 0, sideLeft (chainModel C).W p t (rayPt ztic (-σ) s) := by
    zugg
    have hl' : ztxja := by
      zuogy; exact hl
    exact (sideLeft_rayPt_iff _ p t _ hT2 hs).1 hl'
  have happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztic (-σ) s ∈ U := by
    zunv
    grind
  have hkey : ztmsh := by
    zuks

    have hp0 : ztidy := by
      zuhdi
      exact_mod_cast le_antisymm ztjps (Nat.zero_le p)
    have ht0 : ztbhh := by
      grind
    zultd
    have h0 : ztdxs := by
      zudtj
    have := congrArg Prod.snd ztqqn
    zufpr

  obtain ⟨a, b, harc, hmem⟩ := hit_mem_arcSet hGM hFam hU hp ht ht1 hkey hnσ hsec happ
  grind

/-- **The correctness of local shooting through the ray shooter.**  With `z` and `U` as in
`local_shoot`, the first hit of the ray on the union of the arcs of `U` is the first hit of the
chain (`C.hitParam z σ`).  The list `L` must contain every arc of `U`; it may contain any further
pairs (the arcs of other regions, for instance): arcs lie outside the domain, so they are never
hit before the first hit (**safety of extra candidates**). -/
theorem firstHit_arcs (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {U : Set Point} (hU : U ∈ (chainModel C).regions F)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) (L : List (ℝ × ℝ))
    (hL' : ∀ a b, (chainModel C).IsArc F U a b → ztvk ∈ L) :
    FirstHit (⋃ ab ∈ L, (chainModel C).arcSet ab.1 ab.2) z σ ztbtm := by
  zuixf
  have hfree :=
    hini.mono fun t ht => (Chazelle.Chain.regionsIn_subset hU' ht).1
  obtain ⟨a, b, harc, hmem⟩ := local_shoot C hP hFam hU hz hσ hini
  refine firstHit_of_compl_dom C hz hσ hfree ?_ ?_
  · zuh
    simp only [mem_iUnion] at hx
    obtain ⟨ab, -, hx⟩ := hx
    exact arcSet_subset_compl_dom C hP _ _ hx
  · zughs
end ChainModel
end Sweep
end
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbcs" : tactic => `(tactic| (subst ht0
                                           have hn0 : ztbiy := by_omega
                                           zuee

                                           zujmv
                                           have hbv : ztpln := by_grind))
local macro "zqbct" : tactic => `(tactic| (refine hchord x hx.1 hxs ?_
                                           intro hxF
                                           zuxo

                                           rw [hxs'] at h5))
local macro "zqbcu" : tactic => `(tactic| (filter_upwards [hoff] with s hs
                                           filter_upwards [hs] with δ hδ))
local macro "zqbcv" : tactic => `(tactic| (unfold sideDot; zumzm
                                           zunqe))
local macro "zqbcw" : tactic => `(tactic| rcases hGM with ⟨C, -, rfl⟩ | ⟨Q, -, rfl⟩)
local macro "zqbcx" : tactic => `(tactic| rcases hσ with rfl | rfl)
set_option hygiene true

/-!
# WP-E, Lemma 3.2 part 2: local shooting in any good model

The search of Lemma 3.2 shoots horizontal rays from points of the walk of a good model `M` (a
chain model or the interior model of `Q`) into a region `R` of a chord family, and must know
that the first hit of the ray on the (sub)arcs of `R` is the first point where the ray leaves the
domain.  The sweep (`Sweep.local_shoot`) proves this for chain models; here it is proved for any
good model, from the walk axioms.

* `hit_mem_arcSet'`: `Sweep.hit_mem_arcSet` without the restriction to positive keys (the walk
  vertex `0` of an interior model can be hit), with `arc_of_attach_before'` and
  `arc_of_faces_after'` for the wrap-around at key `0`.
* `adm_hchord`, `hchord_adm`: the admissible chords of a good model are its horizontal chords
  (below the top of the chain, for a chain model).
* `ray_open_subset`: a ray whose initial part is in a region stays in it while it is in the
  domain (`Sweep.ray_subset_region` for any good model).
* `exit_exists`: a ray that starts in the domain and reaches a point outside has a first exit.
* `chordOf`, `mem_chordOf`, `attach_start`, `attach_end`: the segment from the origin to the exit
  and its attachments.
* `local_exit`: **local shooting** — the exit point lies on an arc of the region, and the segment
  is an admissible chord inside the region.
-/
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn sideLeft_edge sideLeft_zero sideLeft_not_self sideKey_inj
  sideCcw_smul IsHChordIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset SectorSide)
open Sweep
section Wrap
variable {M : Model}

/-- Keys just before the key `p` (read on the previous walk edge, wrapping around at `p = 0`)
are inside every cyclic interval ending at `p`. -/
theorem before_eventually {n p : ℕ} (hp : p < n) {l : ℝ} (hl0 : 0 ≤ l) (hln : l < n)
    (hlp : l ≠ (p : ℝ) + 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc l ztmm ztxqb := by
  zucym
  · have hq : ztblb := by
      simp
    zugvl
    have hcast : ztfzm := by
      simp_all
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < n - l by linarith)]
      with s hs hs'
    zuesg
    zuiq

  · have hq := prev_mod hp by_grind
    zugvl
    have hcast : ((p - 1 : ℕ) : ℝ) + ztsqq = (p : ℝ) + 0 := by
      simp_all
    filter_upwards [sideInArc_before_end hlp] with s hs
    simp_all

/-- **A cut walk vertex whose previous positions face `U`** ends an arc of `U` (any key; the
previous walk edge of vertex `0` is the last one). -/
theorem arc_of_attach_before' (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hA : SideAttach M.W c p 0)
    {U : Set Point} (hU : U ∈ M.regions F)
    (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ztcm zteb U) :
    ∃ a b, M.IsArc F U a b ∧ ztwoe := by
  zubop
  zubar
  zufik
  have hn : ztbiy := by have := hA.1; omega
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and (before_eventually hA.1 harcV.1 harcV.2.1 hlk)).and ztctd).exists
  zuiaa
  have hfV' := harcV.2.2.2.2.2.2 _ _ hq by_simp_all by_simp_all hs2
  zuhxs
  grind

/-- A non-cut walk vertex lies in the closure of an arc whose interior contains the keys just
after it (any key: for the empty family, the arc of the whole walk starts at key `0`). -/
theorem arc_after_key (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {p : ℕ} (hcut : ¬ M.IsCut F (p : ℝ)) :
    ∃ X ∈ M.regions F, ∃ l r, M.IsArc F X l r ∧ (sideInArc l r p ∨ (p : ℝ) = l) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc l r ztdvn := by
  zuqx
  · obtain ⟨⟨U, hU, a, b, harc⟩, -⟩ := arcCover M Q ∅ hGM hFam
    zutn
    · simp_all
    refine ⟨U, hU, 0, 0, harc, ?_, ?_⟩
    · zucym
      · simp
      · zucnl
    · zusq
      zuesg
      zujv
  · obtain ⟨X, hX, l, r, harc, hin⟩ :=
      (walkAx_of_goodModel hGM).arc_around hFam.2.1 hFam.1 hne hcut
    exact ⟨X, hX, l, r, harc, Or.inl hin, sideInArc_eventually_add hin⟩

/-- **A non-cut walk vertex whose next positions face `U`** is on an arc of `U` (any key). -/
theorem arc_of_faces_after' (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    (hcut : ¬ M.IsCut F p) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) :
    ∃ a b, M.IsArc F U a b ∧ ztwoe := by
  obtain ⟨X, hX, l, r, harc, hin, hev⟩ := arc_after_key hGM hFam hcut
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ := ((hf.and hev).and ztctd).exists
  zuddc

  grind

/-- `Sweep.arc_of_attach_after` with the key in the closed arc. -/
theorem arc_of_attach_afterK (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hA : SideAttach M.W c p 0)
    {U : Set Point} (hU : U ∈ M.regions F) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U) :
    ∃ a b, M.IsArc F U a b ∧ ztwoe := by
  zubot
  zubar
  zufij
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hf.and ztqdf).and ztctd).exists
  zucaq

  grind

/-- `Sweep.arc_of_faces_edge` with the key in the arc. -/
theorem arc_of_faces_edgeK (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F ztk) (hf : M.Faces p t U) :
    ∃ a b, M.IsArc F U a b ∧ ztwyh := by
  zukep
  zucsj
  zuddd

  grind
end Wrap

/-! ## The hit point lies on an arc of the region (any key) -/
section Hit
variable {M : Model}

/-- **The first-hit point lies on an arc of the region**, for any good model and any key
(`Sweep.hit_mem_arcSet` without `0 < p + t`). -/
theorem hit_key_arc (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : ∀ s > 0, sideLeft M.W p t ztxon)
    (happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ U) :
    ∃ a b, M.IsArc F U a b ∧
      ztwyh := by
  zubm
  zubl

  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hfin hp ht ht1
  zubdr
  zund
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ ball ztbp r := by
    zuclm
    zudak

  zubud

  -- the chords through the ray near `w` avoid it
  have havoid : ∀ c ∈ F, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∉ c := by
    zung
    zudxn

  zujtd
  · -- a chord is attached at the position
    zuhb

    -- a point of the chord near `w`
    set s₂ := min ztcmw ztohc with hs₂
    zudph

    zuial
    have hx₂ : ztwyk := by
      zudsr
      · zuq
        have := congrArg Prod.fst h
        zudv
        zubll
      · zuczr
    -- the position is a walk vertex
    have ht0 : ztbhh := by
      zubiy

      have hw0 : ztycn :=
        Geometry.det_lerp_self _ _ _
      zuqc

    zqbcs
    have hav : ztiyw := by
      have := hM.nd _ ztwwc
      zudbf
    zuyp

    have hsecv : ztjbo :=
      fun x => sideLeft_zero _ _ _
    zuwk
    have hdm0 : ztxfe := by
      zuqm
      grind
    have hvdm : ztwyl := by
      grind
    have hdp : ztxby := by
      have := (hsecv _).1 ztfsl
      zurl
    have hdm : ztxbx := by
      have := (hsecv _).1 hx₂
      zubin
    -- the edge after the vertex does not go along the chord
    have hBdm : ¬ (sideCross ztfd (ztdx : Point) = 0 ∧
        0 < sideDot ztfd (ztdx : Point)) := by
      zubf
      zuxa
      have hb2 : ztplo := by
        grind
      zuhn

      zufvo
      zucmn
      zuck

      have e : ztccd := by
        zucky
        zubjw
        · zudcf
          have h3 : ztwwu := by
            zubyn
            zujcd
          linarith
        · zuqb

      zubuu
    -- the ray is on one side of the chord
    have hdich : ztwre := by
      zudl
      · grind
      · zucvi
      · grind
      · zucyt
        · zuist
        · zugkk
          zujh
          · grind
          · zubyz

        grind
    -- chord points through the sector are on the chord's ray
    have hchord : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∉ ⋃₀ F →
        x ∈ freeIn M.D F := by
      zuetk

    have hray : ∀ x ∈ ball v r, sideLeft M.W p 0 x → x ∈ ⋃₀ F →
        ∃ s' : ℝ, 0 ≤ s' ∧ x - v = s' • (ztdx : Point) := by
      zucbz

      zueh

    zubfa

    · -- the ray is between the edge after the vertex and the chord
      obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hvdm hbv (S := ∅) hr
        ztbqd
      have hHsec : ∀ x ∈ ball v r ∩ {x | sideLeftOf ztwji v b x},
          sideCcw ztfd ztsq (ztdx : Point) := by
        zuh
        zuhdj
        zuof
      have hHfree : ball v r ∩ {x | sideLeftOf ztwji v b x} ⊆
          freeIn M.D F := by
        zuh
        have hxs :=
          (hsecv x).2 ztgdj
        zqbct
        zugan
        · zubag
        · zqbcv
      have hs₁H : ztbajs := by
        zujfx
        show sideLeftOf _ v b _
        zuns
        zuisw
      zubwe
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U := by
        zqbcu
        have := hHU hδ.2
        zubvd
      exact arc_of_attach_afterK hM hF hfin hcF hA' hU hf
    · -- the ray is between the chord and the edge before the vertex
      obtain ⟨-, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hvdm (S := ∅) hr
        ztbqd
      have hHsec : ∀ x ∈ ball v r ∩ {x | sideLeftOf a v ztwji x},
          sideCcw (ztdx : Point) ztsq ztgg := by
        zuh
        zueph
        zuof
      have hHfree : ball v r ∩ {x | sideLeftOf a v ztwji x} ⊆
          freeIn M.D F := by
        zuh
        have hxs :=
          (hsecv x).2 ztfba
        zqbct
        zugam
        · zubag
        · zqbcv
      have hs₁H : ztbajr := by
        zujfx
        show sideLeftOf a v _ _
        zuns
        zuisx
      zubwe
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ztcm zteb U := by
        zqbcu
        have := hHU hδ.1
        zucqb
        show Jordan.offset ztffo
          ztffo _ δ ∈ U
        zuhnd
        omega
      exact arc_of_attach_before' hM hF hfin hcF hA' hU hf
  · -- no chord is attached at the position
    have hfreeS : ztwnw := by
      intro x hx hxl
      obtain ⟨hxD, hxc⟩ := hsf x hx hxl
      zugsz

      exact hcut ztexz
    zubhu
    · -- inside a walk edge
      zufwm
      have hHc : IsPreconnected (ball ztbp r ∩
          {x : Point | 0 < 1 * det ztoy ztbakv x}) :=
        ((convex_ball _ r).inter zthqu).isPreconnected
      have hHfree : ball _ r ∩
          {x : Point | 0 < 1 * det _ _ x} ⊆
          freeIn M.D F := fun x hx =>
        hfreeS x hx.1 ztyhc
      have hs₁H : rayPt _ τ s₁ ∈ ball _ r ∩
          {x : Point | 0 < 1 * det _ _ x} :=
        ⟨hs₁B, by simpa using (sideLeft_edge hne ht' _).1 by_simp_all⟩
      zudhg
      have hf : ztuln := by
        zuepc

      exact arc_of_faces_edgeK hGM hFam hU hp ht' hcut hf
    · -- at a walk vertex
      zqbcs
      have hav : ztiyw := by
        have := hM.nd _ ztwwc
        zudbf
      zuzf
      have hHfree : ztddz := fun x hx =>
        hfreeS x ztdyx ztdxy
      have hs₁H : ztdar := by
        zuevy
        have := hsec s₁ hs₁pos'
        zubmc

      zuhed
      have hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p s U := by
        zqbcu
        have := hHU hδ.2
        zubvd
      exact arc_of_faces_after' hGM hFam hU hp by_grind hf

/-- **The first-hit point lies on an arc of the region**, for any good model and any key. -/
theorem hit_mem_arcSet' (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : ∀ s > 0, sideLeft M.W p t ztxon)
    (happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp τ s ∈ U) :
    ∃ a b, M.IsArc F U a b ∧ sidePt M.W p t ∈ M.arcSet a b := by
  obtain ⟨a, b, h1, h2⟩ := hit_key_arc hGM hFam hU hp ht ht1 hτ hsec happ
  exact ⟨a, b, h1, mem_arcSet_of_key hp ht ht1.le h2⟩
end Hit

/-! ## Rays in a good model -/
section Ray
variable {M : Model}

/-- The admissible chords of a good model are horizontal chords of its domain. -/
theorem adm_hchord (hGM : GoodModel M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ y a b, IsHChordIn M.D y a b ∧ c = Visibility.hseg y a b := by
  zqbcw
  · obtain ⟨y, a, b, h, -, rfl, -, -⟩ := Merge.augChords_spec hc
    tauto
  tauto

/-- A horizontal chord of the domain of a good model is admissible (for a chain model, if it is
not above the top of the chain). -/
theorem hchord_adm (hGM : GoodModel M) {y a b : ℝ} (h : IsHChordIn M.D y a b)
    (htop : ∀ C : Chain, M = chainModel C → y ≤ C.top.2) : Visibility.hseg y a b ∈ M.Adm := by
  zqbcw
  · exact ⟨y, a, b, h, by_simp_all, rfl⟩
  · exact ztfxb

/-- **Regions are closed under visibility, along a ray** (any good model): if the open stretch
`(0, T)` of a horizontal ray is in the domain and its initial part is in the region `U` of an
admissible family, the whole stretch is in `U`. -/
theorem ray_open_subset (hGM : GoodModel M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {U : Set Point} (hU : U ∈ regionsIn M.D F) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {T : ℝ} (hT : 0 < T) (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D)
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) :
    ∀ t, 0 < t → t < T → rayPt z σ t ∈ U := by
  zubdr
  have hIc : ztlxh :=
    isPreconnected_Ioo.image _ (Chazelle.Visibility.continuous_rayPt z σ).continuousOn
  have hIfree : rayPt z σ '' Ioo 0 T ⊆ freeIn M.D F := by
    zucze

    obtain ⟨y, a, b, h, rfl⟩ := adm_hchord hGM ztgjz
    zucnx

    have hall : ztfxm := by
      zufib

      · zqbcx
        · zube

          apply h.left_not
          have := hdom ztten by_linarith by_grind
          zuckt
        grind
      · zqbcx
        · linarith
        · zube

          apply h.right_not
          have := hdom ztuev by_linarith by_grind
          zuckt
    zucoi

  zucbp
variable {D : Set Point} {z : Point} {σ T : ℝ} {W : Polygon} {p : ℕ} {t : ℝ}
/-- **The first exit of a ray**: a ray starting in an open set `D` and reaching a point outside
leaves `D` at a first parameter `T`. -/
theorem exit_exists (hD : IsOpen D) {z : Point} {σ : ℝ}
    (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ D) {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hout : rayPt z σ t₁ ∉ D) :
    ∃ T, 0 < T ∧ T ≤ t₁ ∧ rayPt z σ T ∉ D ∧ ∀ t, 0 < t → t < T → rayPt z σ t ∈ D := by
  set S := {t : ℝ | 0 < t ∧ rayPt z σ t ∉ D} with hS
  have hne : S.Nonempty := ⟨t₁, ht₁, hout⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.le⟩
  obtain ⟨ε, hε, hεD⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hini)
  have hTε : ε ≤ sInf S := by
    refine le_csInf hne fun t ht => ?_
    zubq

    exact ht.2 (hεD (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact h) ht.1)
  have hTt : sInf S ≤ t₁ := csInf_le hbdd by_simp_all
  have hbelow : ∀ t, 0 < t → t < sInf S → rayPt z σ t ∈ D := fun t ht htT => by
    zumv
    exact absurd (csInf_le hbdd by_simp_all) (not_le.2 htT)
  refine ⟨sInf S, by_linarith, hTt, fun hTD => ?_, hbelow⟩
  have hc : Continuous _ := Chazelle.Visibility.continuous_rayPt z σ
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hD.preimage hc) ztwdb hTD
  obtain ⟨s, hsS, hs⟩ := exists_lt_of_csInf_lt hne (show sInf S < sInf S + δ by linarith)
  have hTs : sInf S ≤ s := by_grind
  exact hsS.2 (hball (by rw [mem_ball, Real.dist_eq, abs_lt]; grind))

/-- The horizontal segment from `z` to the point of the ray in direction `σ` at parameter `T`. -/
noncomputable def chordOf (z : Point) (σ T : ℝ) : Set Point :=
  Visibility.hseg z.2 ztzxd ztzxb

/-- The points of `chordOf z σ T` are the ray points up to `T`. -/
theorem mem_chordOf (hσ : σ = 1 ∨ σ = -1) (hT : 0 ≤ T) {x : Point} :
    x ∈ chordOf z σ T ↔ ∃ s, 0 ≤ s ∧ s ≤ T ∧ x = rayPt z σ s := by
  unfold chordOf Visibility.hseg
  zuwb
  zqbcx
  · zuilp
    constructor
    · zuecm
      exact ⟨x.1 - z.1, by_linarith, by_linarith, point_ext by_simp by_simp_all⟩
    simp_all
  · zuilq
    constructor
    · zuecm
      exact ⟨z.1 - x.1, by_linarith, by_linarith, point_ext by_simp by_simp_all⟩
    · zugtj
      zuipr
theorem rayPt_zero' (z : Point) (σ : ℝ) : rayPt z σ 0 = z := by_simp_all

/-- The ray back from the point at parameter `T`. -/
theorem rayPt_back (z : Point) (σ T s : ℝ) : rayPt ztxn (-σ) s = rayPt z σ ztctq :=
  point_ext (by simp; ring) by_simp

/-- **The chord is attached at its origin** when the ray leaves the origin's position into its
left sector. -/
theorem attach_start (hp : p < W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hsec : sideLeft W p t ztxoo) :
    SideAttach W (chordOf ztia σ T) p t := by
  refine ⟨hp, ht0, ht1, (mem_chordOf hσ hT.le).2 ⟨0, le_rfl, hT.le, (rayPt_zero' _ _).symm⟩,
    1, one_pos, fun x hx hxz _ => ?_⟩
  obtain ⟨s, hs0, -, rfl⟩ := (mem_chordOf hσ hT.le).1 hx
  have hs : ztxx := by
    zuvl
    · zubh
    · zujpp
  exact (sideLeft_rayPt_iff W p t σ one_pos hs).1 hsec

/-- **The chord is attached at its far end** when the ray back from it enters the left sector of
the far end's position. -/
theorem attach_end (hp : p < W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T)
    (hw : sidePt W p t = rayPt z σ T) (hsec : sideLeft W p t (rayPt ztia (-σ) 1)) :
    SideAttach W ztcmu p t := by
  refine ⟨hp, ht0, ht1, by zunft; exact (mem_chordOf hσ hT.le).2 by_grind,
    1, one_pos, fun x hx hxz _ => ?_⟩
  obtain ⟨s, -, hsT, rfl⟩ := (mem_chordOf hσ hT.le).1 hx
  have hs : ztppt := by
    grind
  have e : rayPt z σ s = rayPt ztia (-σ) ztctq := by rw [hw, rayPt_back]; simp
  zui
  exact (sideLeft_rayPt_iff W p t _ one_pos by_linarith).1 hsec

/-- A point of the chord off the domain is one of its ends, when its open part is in the
domain. -/
theorem chordOf_end (hσ : σ = 1 ∨ σ = -1) (hT : 0 ≤ T)
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ D) {x : Point} (hx : x ∈ chordOf z σ T)
    (hxD : x ∉ D) : x = z ∨ x = rayPt z σ T := by
  obtain ⟨s, hs0, hsT, rfl⟩ := (mem_chordOf hσ hT).1 hx
  zunl
  · grind
  · left; rw [← h0, rayPt_zero']

/-- **Local shooting in a good model.**  Let the ray from the point `z` off the domain start in
the region `U` of a chord family and reach a point off the domain at parameter `t₁`.  Then it
leaves the domain first at some `T ≤ t₁`; the open stretch before `T` is in `U`; the segment
`chordOf z σ T` is an admissible chord (for a chain model, if `z` is not above the top); it is
attached at a walk position of its far end; and the far end lies on an arc of `U`. -/
theorem local_exit (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzD : z ∉ M.D) (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U)
    {t₁ : ℝ} (ht₁ : 0 < t₁) (hout : rayPt z σ t₁ ∉ M.D)
    (htop : ∀ C : Chain, M = chainModel C → z.2 ≤ C.top.2) :
    ∃ T, 0 < T ∧ T ≤ t₁ ∧ rayPt z σ T ∉ M.D ∧ ztgnn ∧
      chordOf z σ T ∈ M.Adm ∧
      ztxeo ∧
      ∃ a b, M.IsArc F U a b ∧ rayPt z σ T ∈ M.arcSet a b := by
  zubm
  zubdr
  have hiniD := hini.mono fun t h => (hUfree h).1
  obtain ⟨T, hT, hTt, hTD, hdom⟩ := exit_exists hM.isOpen hiniD ht₁ hout
  have hray := ray_open_subset hGM hFam.2.1 hU hσ hT hdom hini
  -- the segment is a horizontal chord of the domain
  have hH : IsHChordIn M.D z.2 ztzxd ztzxb := by
    zqbcx
    · zuilp
      refine ⟨by_linarith, by_omega, by_tauto, fun x h1 h2 => ?_⟩
      have := hdom ztudv by_linarith by_linarith
      zugid
    · zuilq
      refine ⟨by_linarith, by_tauto, by_omega, fun x h1 h2 => ?_⟩
      have := hdom (z.1 - x) by_linarith by_linarith
      zugid
  have hadm : chordOf z σ T ∈ M.Adm := hchord_adm hGM hH htop
  -- a walk position at the far end
  obtain ⟨a, b, hab, -, -, -, ⟨⟨pa, ta, hAa, hpa⟩, -⟩, ⟨⟨pb, tb, hAb, hpb⟩, -⟩⟩ := hM.ends _ hadm
  have hend : ∃ p t, SideAttach M.W ztcmu p t ∧ sidePt M.W p t = rayPt z σ T := by
    have ca := chordOf_end hσ hT.le hdom hAa.2.2.2.1 (hM.trace pa hAa.1 ta hAa.2.1 hAa.2.2.1.le)
    have cb := chordOf_end hσ hT.le hdom hAb.2.2.2.1 (hM.trace pb hAb.1 tb hAb.2.1 hAb.2.2.1.le)
    grind
  obtain ⟨p, t, hA, hpt⟩ := hend
  refine ⟨T, hT, hTt, hTD, hray, hadm, by_grind, ?_⟩
  -- the far end lies on an arc of `U`
  zukv
  obtain ⟨r, hr, hcl⟩ := hA.2.2.2.2
  set s₀ := min T r / 2 with hs₀
  have hmin : 0 < min T r := by_grind
  have hs₀0 : ztphv := by_grind
  have hs₀T : s₀ < T := by_grind
  have hs₀r : s₀ < r := by_grind
  have hx₀ : sideLeft M.W p t (rayPt ztbp (-σ) s₀) := by
    zukvq
    refine hcl _ ((mem_chordOf hσ hT.le).2 by_grind) ?_ ?_
    · grind
    · rw [hpt, ← rayPt_back, dist_rayPt _ hnσ hs₀0.le]; omega
  have hsec : ∀ s > 0, sideLeft M.W p t (rayPt _ _ s) := fun s hs =>
    (sideLeft_rayPt_iff M.W p t _ hs₀0 hs).1 hx₀
  have happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztbp (-σ) s ∈ U := by
    zumy
    zuesg
    zukvq
    grind
  obtain ⟨a', b', harc, hmem⟩ :=
    hit_mem_arcSet' hGM hFam hU hA.1 hA.2.1 hA.2.2.1 hnσ hsec happ
  grind
end Ray
end
end Restore
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbjq" : tactic => `(tactic| (config_simp; omega))
local macro "zqbjr" : tactic => `(tactic| have f₃ := exec_frameB e₃ (B := Bl [50062, 50063, 50064]) by_decide)
local macro "zqbjs" : tactic => `(tactic| (obtain ⟨h1, h2, h3⟩ := hh
                                           simp [itemOf, h1, h2, h3]))
set_option hygiene true

/-!
# Reading a host polygon on the RAM (WP-C, target 2: chain model)

The chain model of a chain `C` of a host polygon `H.poly Q` (`HostAt` layout: the number of
items, then three words per item) needs the symbolic points of `H` at given indices.  Two loops
over the items (at most `64` in the down phase, `HostOk`):

* `cntLoop`: the number `N = (H.pts n).length` of symbolic points (`cnt_exec`);
* `lookLoop`: the symbolic point of index `p < N` (`look_exec`), into `lr 46 … lr 48`
  (`SymPtIn` layout).

Well-formedness needed (`HostWF`): runs `run a ℓ` with `a, ℓ < n` (so that `(a + k) mod n` is
one conditional subtraction), points in range (`SymPt.Lt n`, for the sign kernel).

Registers: `lr 60` the host handle, `lr 61` the number of items, `lr 62` the item index, `lr 63`
the running count, `lr 64` the address of the item, `lr 65 … lr 76` scratch, `lr 67 = 1`,
`lr 68 = 2`, `lr 69 = 3`, `lr 71` the target index.
-/
namespace Chazelle.Core
namespace NFLoc
open Machine Machine.Stmt Programs SignK
@[expose] public section
def itemCnt : HostItem → ℕ
  | .run _ ℓ => ℓ + 1
  | .pt _ => 1
theorem pts_length_item (n : ℕ) (it : HostItem) : (it.pts n).length = itemCnt it := by
  cases it <;> simp [HostItem.pts, itemCnt]

/-- The number of symbolic points of the first `i` items. -/
def preLen (n : ℕ) (H : Host) (i : ℕ) : ℕ := ((H.take i).flatMap ztmbf).length
theorem preLen_zero (n : ℕ) (H : Host) : preLen n H 0 = 0 := by_rfl
theorem preLen_succ (n : ℕ) (H : Host) {i : ℕ} (hi : i < H.length) :
    preLen n H ztg = preLen n H i + itemCnt H[i] := by
  unfold preLen
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append,
    List.length_append]
  simp [pts_length_item]
theorem preLen_length (n : ℕ) (H : Host) : preLen n H H.length = (H.pts n).length := by
  unfold preLen Host.pts
  simp
theorem preLen_le_succ (n : ℕ) (H : Host) (i : ℕ) : preLen n H i ≤ preLen n H ztg := by
  by_cases hi : i < H.length
  · rw [preLen_succ n H hi]; omega
  · unfold preLen
    grind
theorem preLen_mono (n : ℕ) (H : Host) {i j : ℕ} (hij : i ≤ j) : preLen n H i ≤ preLen n H j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact ih.trans (preLen_le_succ n H j)

/-- **The point of index `p`** lies in item `i` when `p` is in its range. -/
theorem pts_getElem? (n : ℕ) (H : Host) {i p : ℕ} (hi : i < H.length) (h1 : preLen n H i ≤ p)
    (h2 : p < preLen n H i + itemCnt H[i]) :
    ztmbe[p]? = (H[i].pts n)[p - preLen n H i]? := by
  have e : H.pts n = (H.take i).flatMap ztmbf ++
      (H[i].pts n ++ (H.drop ztg).flatMap ztmbf) := by
    zultt
    conv_lhs => rw [← List.take_append_drop i H, List.drop_eq_getElem_cons hi]
    grind
  unfold preLen at h1 h2 ⊢
  rw [e, List.getElem?_append_right h1, List.getElem?_append_left]
  rw [pts_length_item]
  omega

/-- The points of a run. -/
theorem run_pts_getElem? (n a ℓ : ℕ) {k : ℕ} (hk : k ≤ ℓ) :
    ((HostItem.run a ℓ).pts n)[k]? = some (SymPt.vtx ztxyt) := by
  simp [HostItem.pts, List.getElem?_map, List.getElem?_range (by omega : k < ℓ + 1)]

/-! ## Decoding the layout -/

/-- The item coded by the words `k, a, b`. -/
def itemOf (k a b : ℕ) : HostItem :=
  if k = 0 then .run a b else if k = 1 then .pt ztpsg else .pt (.onEdge a b)
variable {m : ℕ → ℕ} {B : ℕ} {P : Polygon} {W : ℕ}
/-- **The layout determines the items.** -/
theorem hostAt_item {H : Host} (h : HostAt m B H) {i : ℕ}
    (hi : i < H.length) :
    H[i] = itemOf (m ztban) (m ztelu) (m ztgzt) ∧
      m ztban ≤ 2 := by
  have hh := h.2 i hi
  rw [getD_of_lt _ hi] at hh
  generalize H[i] = it at hh ⊢
  cases it with
  | run a l =>
    zqbjs
  | pt x =>
    cases x with
    | vtx j =>
      obtain ⟨h1, h2⟩ := hh
      simp [itemOf, h1, h2]
    | onEdge e hh' =>
      zqbjs

/-- The layout determines the host. -/
theorem hostAt_unique {H H' : Host} (h : HostAt m B H)
    (h' : HostAt m B H') : H = H' := by
  have hl := h.1.symm.trans h'.1
  zuiqu
  zugoh
  rw [(hostAt_item h hi).1, (hostAt_item h' hi').1]

/-- The count of the item coded by `k, a, b`, as the machine computes it. -/
theorem itemCnt_itemOf (k a b : ℕ) : itemCnt (itemOf k a b) = if k < 1 then b + 1 else 1 := by
  unfold itemOf
  zufcy

/-- All symbolic points of a well-formed host are in range. -/
theorem hostWF_pts {n : ℕ} {H : Host} (h : HostWF n H) (hn : 0 < n) :
    ∀ x ∈ H.pts n, x.Lt n := by
  zuh
  unfold Host.pts at hx
  obtain ⟨it, hit, hx⟩ := List.mem_flatMap.1 hx
  have := h it hit
  cases it with
  | run a l =>
    simp only [HostItem.pts, List.mem_map, List.mem_range] at hx
    obtain ⟨k, -, rfl⟩ := hx
    zuiss
  | pt y =>
    simp only [HostItem.pts, List.mem_singleton] at hx
    zultk
    zufep

/-! ## Counting the points -/

/-- One item of the count. -/
def cntBody : Stmt :=
  .seq (.instr (.loadN 50065 50064))
    (.seq (.ifLtN 50065 50067 (block [.addN 50070 50064 50068, .loadN 50066 50070,
        .addN 50063 50063 50066, .addN 50063 50063 50067])
      (.instr (.addN 50063 50063 50067)))
      (block [.addN 50062 50062 50067, .addN 50064 50064 50069]))

/-- Constants, `i := 0`, count `:= 0`, address of item `0`. -/
def hostInit : Stmt := block [.constN 50067 1, .constN 50068 2, .constN 50069 3,
  .loadN 50061 50060, .constN 50062 0, .constN 50063 0, .addN 50064 50060 50067]

/-- **The number of symbolic points of the host at `lr 60`**, into `lr 63`. -/
def cntStmt : Stmt := .seq hostInit (.whileLtN 50062 50061 cntBody)

/-- The registers written by the host routines. -/
def Bhost (r : ℕ) : Bool := decide (50046 ≤ r ∧ r < 50049) || decide (50061 ≤ r ∧ r < 50077)
theorem wr_cntStmt : wr Bhost cntStmt = true := by_decide

/-- The facts the host loops keep. -/
structure HostEnv (W Hh len : ℕ) (m : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  h60 : c.nreg 50060 = Hh
  h61 : c.nreg 50061 = len
  h67 : c.nreg 50067 = 1
  h68 : c.nreg 50068 = 2
  h69 : c.nreg 50069 = 3
  mem : c.nmem = m

/-- One step of the count. -/
theorem cntBody_exec {Hh len : ℕ} {m : ℕ → ℕ} {c : Config}
    (h : HostEnv W Hh len m c) {i : ℕ} (hi : c.nreg 50062 = i) (hil : i < len)
    (ha : c.nreg 50064 = Hh + 1 + 3 * i) (haW : Hh + 3 * len + 4 ≤ W)
    (hacc : c.nreg 50063 + ztbog ≤ W) :
    ∃ c' k, Exec P W cntBody c c' k ∧ k ≤ 10 ∧ HostEnv W Hh len m c' ∧
      c'.nreg 50062 = i + 1 ∧ c'.nreg 50064 = Hh + 1 + 3 * ztg ∧
      c'.nreg 50063 = c.nreg 50063 +
        ztbog ∧
      (∀ r, (r < 50061 ∨ 50077 ≤ r) → c'.nreg r = c.nreg r) := by
  zuesn
  have h60 := h.h60
  have h61 := h.h61
  have h67 := h.h67
  have h68 := h.h68
  have h69 := h.h69
  have hm := h.mem
  have ad : Hh + 1 + 3 * i + 2 = Hh + 3 + 3 * i := by_omega
  unfold cntBody
  refine spec_seq (spec_instr (Exec.loadN hw 50065 50064) fun hw₁ => ?_)
  by_cases hk : m zthas < 1
  · rw [ite_eq_left hk] at hacc ⊢
    refine spec_seq (spec_ifLtN_true by_simp_all ?_)
    exec_block
    · zqbjq
    · config_simp; rw [ha, h68, hm, ad]; omega
    · config_simp; zunml; omega
    · zqbjq
    · zqbjq
    refine ⟨by_omega, ⟨by_omega, by_simp_all, by_simp_all,
      by simp_all, by_simp_all, by_simp_all,
      by omega⟩, by_simp_all, by config_simp; omega,
      by config_simp; zunml; ring, fun r hr => ?_⟩
    zuby
    grind
  · rw [ite_eq_right hk] at hacc ⊢
    refine spec_seq (spec_ifLtN_false by_simp_all
      (spec_instr (Exec.addN hw₁ _ _ _ by_simp_all) fun hw₂ => ?_))
    exec_block
    · zqbjq
    · zqbjq
    refine ⟨by_omega, ⟨by_omega, by_simp_all, by_simp_all,
      by simp_all, by_simp_all, by_simp_all,
      by omega⟩, by_simp_all, by config_simp; omega,
      by simp_all, fun r hr => ?_⟩
    zuby
    grind

/-- The count the machine adds for item `i` is the number of its points. -/
theorem machineCnt_eq {Hh : ℕ} {H : Host} (hH : HostAt m Hh H) {i : ℕ}
    (hi : i < H.length) :
    ztbog = itemCnt H[i] := by
  rw [(hostAt_item hH hi).1, itemCnt_itemOf]

/-- **The count of the symbolic points of a host** (at most `12 |H| + 12` steps). -/
theorem cnt_exec {Hh n : ℕ} {H : Host} (c : Config) (hw : WordsBounded W c)
    (hH : HostAt c.nmem Hh H) (h60 : c.nreg 50060 = Hh) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hN : (H.pts n).length ≤ W) :
    ∃ c' k, Exec P W cntStmt c c' k ∧ k ≤ 12 * H.length + 12 ∧ FrameB Bhost c c' ∧
      c'.nreg 50063 = (H.pts n).length ∧ HostEnv W Hh H.length c.nmem c' := by
  zumdu
  obtain ⟨c₁, k₁, e₁, hk₁, I₁⟩ : ∃ c₁ k₁, Exec P W hostInit c c₁ k₁ ∧ k₁ = 7 ∧
      (HostEnv W Hh H.length c.nmem c₁ ∧ c₁.nreg 50062 = 0 ∧ c₁.nreg 50063 = 0 ∧
        c₁.nreg 50064 = Hh + 1) := by
    unfold hostInit
    exec_block
    · omega
    · omega
    · omega
    · omega
    · omega
    · zqbjq
    · refine ⟨rfl, ⟨by_omega, by_simp_all, by_simp_all,
        by config_simp, by config_simp, by config_simp, rfl⟩, by config_simp, by config_simp,
        by simp_all⟩
  obtain ⟨E₁, i0, a0, d0⟩ := I₁
  let I : Config → Prop := fun d => HostEnv W Hh H.length c.nmem d ∧ d.nreg 50062 ≤ H.length ∧
    d.nreg 50063 = preLen n H ztqlr ∧ d.nreg 50064 = Hh + 1 + 3 * d.nreg 50062
  have hI₁ : ztkzz := ⟨E₁, by_omega, by rw [a0, i0, preLen_zero], by_omega⟩
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 50062) (b := 50061)
    (body := cntBody) I ztnys 10 ztjvt
    (fun d hd ht => by
      obtain ⟨E, hi, ha, hd'⟩ := hd
      zukpa
      have hcnt := machineCnt_eq hH ht
      have hpre := preLen_succ n H ht
      have hle := preLen_mono n H (show d.nreg 50062 + 1 ≤ H.length by omega)
      rw [preLen_length] at hle
      obtain ⟨d', k, e, hk, E', i', a', c', -⟩ := cntBody_exec (P := P) E rfl ht hd' haW
        by_omega
      grind) hI₁
  obtain ⟨E₂, i₂, a₂, -⟩ := I₂
  zukpc
  have hlast : zturd := by_omega
  have ex : Exec P W cntStmt c c₂ _ := .seq e₁ e₂
  refine ⟨c₂, _, ex, ?_, exec_frameB ex wr_cntStmt, by rw [a₂, hlast, preLen_length], E₂⟩
  omega

/-! ## Looking up a point -/

/-- Membership in a list of registers, as a write set. -/
def Bl (l : List ℕ) (r : ℕ) : Bool := l.contains r
theorem ne_of_Bl {l : List ℕ} {r a : ℕ} (h : Bl l r = false) (ha : a ∈ l) : r ≠ a := by
  zunq
  rw [Bl, List.contains_iff_mem.2 ha] at h
  simp_all
theorem Bl_mono {l l' : List ℕ} {r : ℕ} (h : Bl l' r = false) (hs : l ⊆ l') : Bl l r = false := by
  unfold Bl at *
  grind

/-- Advance to the next item: count `:= lr 73`, `i := i + 1`, address `+ 3`. -/
def advance : Stmt := block [.copyN 50063 50073, .addN 50062 50062 50067, .addN 50064 50064 50069]

/-- Found in a run `run a ℓ` (`a` in `lr 66`): the vertex `(a + (p - count)) mod n`; exit. -/
def foundRun : Stmt :=
  .seq (block [.subN 50074 50071 50063, .inputSize 50075, .subN 50076 50075 50066])
    (.seq (.ifLtN 50074 50076 (.instr (.addN 50047 50066 50074)) (.instr (.subN 50047 50074 50076)))
      (block [.constN 50046 0, .copyN 50062 50061]))

/-- Found a point item (kind `1` vertex, `2` edge point): copy it; exit. -/
def foundPt : Stmt :=
  block [.subN 50046 50065 50067, .copyN 50047 50066, .copyN 50048 50072, .copyN 50062 50061]

/-- Read item `i` (kind, two arguments), then decide. -/
def lookBody : Stmt :=
  .seq (block [.loadN 50065 50064, .addN 50070 50064 50067, .loadN 50066 50070,
      .addN 50070 50070 50067, .loadN 50072 50070])
    (.ifLtN 50065 50067
      (.seq (block [.addN 50073 50063 50072, .addN 50073 50073 50067])
        (.ifLtN 50071 50073 foundRun advance))
      (.seq (.instr (.addN 50073 50063 50067)) (.ifLtN 50071 50073 foundPt advance)))

/-- **The symbolic point of index `lr 71`** of the host at `lr 60` (after `hostInit`), into
`lr 46 … lr 48`. -/
def lookStmt : Stmt :=
  .seq (block [.constN 50062 0, .constN 50063 0, .addN 50064 50060 50067])
    (.whileLtN 50062 50061 lookBody)
theorem wr_lookStmt : wr Bhost lookStmt = true := by_decide

/-- The invariant of the lookup. -/
def LkI (W n Hh p : ℕ) (H : Host) (m : ℕ → ℕ) (d : Config) : Prop :=
  HostEnv W Hh H.length m d ∧ d.nreg 50071 = p ∧ d.nreg 50062 ≤ H.length ∧
    ((d.nreg 50063 = preLen n H ztqlr ∧ preLen n H ztqlr ≤ p ∧
        d.nreg 50064 = Hh + 1 + 3 * d.nreg 50062) ∨
      (d.nreg 50062 = H.length ∧ ∃ sp, ztmbe[p]? = some sp ∧ SymPtIn d 50046 sp))

/-- `(a + k) mod n` by one conditional subtraction. -/
theorem mod_of_lt_two {a k n : ℕ} (ha : a < n) (hk : k < n) :
    ztbzd % n = if k < n - a then a + k else k - (n - a) := by
  zus
  · zudgs
  · zul
    omega

/-- One step of the lookup. -/
theorem lookBody_exec {W Hh p : ℕ} {H : Host} {m : ℕ → ℕ} {d : Config}
    (hH : HostAt m Hh H) (hwf : HostWF P.n H) (hW : P.n ≤ W) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hN : (H.pts P.n).length ≤ W) (hI : LkI W P.n Hh p H m d) (ht : d.nreg 50062 < d.nreg 50061) :
    ∃ d' k, Exec P W lookBody d d' k ∧ LkI W P.n Hh p H m d' ∧ k ≤ 25 ∧
      H.length - d'.nreg 50062 < H.length - d.nreg 50062 := by
  obtain ⟨E, h71, hil, hs⟩ := hI
  zugnh
  zukpa
  set i := d.nreg 50062 with hi
  zudjm

  · omega
  zubez

  have hmem := List.getElem_mem ht
  zucqm

  -- the loads
  obtain ⟨d₁, k₁, e₁, hk₁, l65, l66, l72⟩ : ∃ d₁ k₁, Exec P W (block [.loadN 50065 50064,
      .addN 50070 50064 50067, .loadN 50066 50070, .addN 50070 50070 50067,
      .loadN 50072 50070]) d d₁ k₁ ∧ k₁ = 5 ∧ d₁.nreg 50065 = k ∧ d₁.nreg 50066 = a ∧
      d₁.nreg 50072 = b := by
    exec_block
    · config_simp; rw [ha, E.h67]; omega
    · config_simp; rw [ha, E.h67]; omega
    · refine ⟨rfl, by config_simp; rw [ha, E.mem], ?_, ?_⟩
      · config_simp; rw [ha, E.h67, E.mem]; grind
      · config_simp; rw [ha, E.h67, E.mem]; grind
  have f₁ := exec_frameB e₁ (B := Bl [50065, 50066, 50070, 50072]) by_decide
  zud
  have g := fun r (hr : Bl [50065, 50066, 50070, 50072] r = false) => f₁.1 r hr
  have g60 := (g _ by_decide).trans E.h60
  have g61 := (g _ by_decide).trans E.h61
  have g62 : d₁.nreg 50062 = i := g _ by_decide
  have g63 := (g _ by_decide).trans hacc
  have g64 := (g _ by_decide).trans ha
  have g67 := (g _ by_decide).trans E.h67
  have g68 := (g _ by_decide).trans E.h68
  have g69 := (g _ by_decide).trans E.h69
  have g71 := (g _ by_decide).trans h71
  zulhf
  -- the environment is kept by the rest (they write only `Bhost` registers other than these)
  have env : ∀ d' : Config, WordsBounded W d' → d'.nmem = d₁.nmem →
      (∀ r, Bl [50046, 50047, 50048, 50062, 50063, 50064, 50073, 50074, 50075, 50076] r = false →
        d'.nreg r = d₁.nreg r) → HostEnv W Hh H.length m d' ∧ d'.nreg 50071 = p :=
    fun d' hw' hm' hr' => ⟨⟨hw', (hr' _ by_decide).trans g60, (hr' _ by_decide).trans g61,
      (hr' _ by_decide).trans g67, (hr' _ by_decide).trans g68,
      (hr' _ by_decide).trans g69, hm'.trans gm⟩, (hr' _ by_decide).trans g71⟩
  zujtn
  · -- a run
    zufvc
    have hrun : H[i] = .run a b := by rw [hitem.1]; simp [itemOf, hk0]
    have hab : a < P.n ∧ b < P.n := by have := hwf _ hmem; grind
    rw [ite_eq_left hkind] at hcnt
    obtain ⟨d₂, k₂, e₂, hk₂, l73⟩ : ∃ d₂ k₂, Exec P W (block [.addN 50073 50063 50072,
        .addN 50073 50073 50067]) d₁ d₂ k₂ ∧ k₂ = 2 ∧
        d₂.nreg 50073 = preLen P.n H i + ztds := by
      exec_block
      · omega
      · zqbjq
      · exact ⟨rfl, by config_simp; omega⟩
    have f₂ := exec_frameB e₂ (B := Bl [50073]) by_decide
    zue
    have h2 : ∀ r, r ≠ 50073 → d₂.nreg r = d₁.nreg r := fun r hr =>
      f₂.1 r ztnuo
    by_cases hf : p < preLen P.n H i + ztds
    · -- found
      have off : p - preLen P.n H i ≤ b := by_omega
      obtain ⟨d₃, k₃, e₃, hk₃, o46, o47, o62⟩ : ∃ d₃ k₃, Exec P W foundRun d₂ d₃ k₃ ∧
          k₃ ≤ 8 ∧ d₃.nreg 50046 = 0 ∧ d₃.nreg 50047 = (a + (p - preLen P.n H i)) % P.n ∧
          d₃.nreg 50062 = H.length := by
        unfold foundRun
        refine spec_seq ?_
        exec_block
        · zugkh
        rw [mod_of_lt_two hab.1 by_omega]
        by_cases hc : p - preLen P.n H i < P.n - a
        · refine spec_seq (spec_ifLtN_true (by
            config_simp; grind) (spec_instr (Exec.addN ‹_› _ _ _ (by
              config_simp; grind)) fun _ => ?_))
          exec_block
          · omega
          refine ⟨by_omega, by config_simp, ?_, ?_⟩
          · config_simp
            grind
          · config_simp; grind
        · refine spec_seq (spec_ifLtN_false (by
            config_simp; grind) (spec_instr (Exec.subN ‹_› _ _ _) fun _ => ?_))
          exec_block
          · omega
          refine ⟨by_omega, by config_simp, ?_, ?_⟩
          · config_simp
            grind
          · config_simp; grind
      have f₃ := exec_frameB e₃ (B := Bl [50046, 50047, 50062, 50074, 50075, 50076]) by_decide
      obtain ⟨E₃, p₃⟩ := env d₃ e₃.wb_right ztvqv (fun r hr => by
        rw [f₃.1 r ztsvr,
          h2 r ztkbh])
      zukiu
      have t2 : d₂.nreg 50071 < d₂.nreg 50073 := by
        grind
      refine ⟨d₃, k₁ + (ztdhs + 1),
        .seq e₁ (.ifLtN_true t1 ztncn),
        ⟨E₃, p₃, by_omega, Or.inr ⟨o62, .vtx _, ?_,
          ⟨o46, o47⟩⟩⟩, by_omega, by_omega⟩
      rw [pts_getElem? P.n H ht hpi by_omega, hrun,
        run_pts_getElem? _ _ _ off]
    · -- not in this item
      obtain ⟨d₃, k₃, e₃, hk₃, o63, o62, o64⟩ : ∃ d₃ k₃, Exec P W advance d₂ d₃ k₃ ∧ k₃ = 3 ∧
          d₃.nreg 50063 = preLen P.n H i + ztds ∧ d₃.nreg 50062 = i + 1 ∧
          d₃.nreg 50064 = Hh + 1 + 3 * ztg := by
        unfold advance
        exec_block
        · config_simp; grind
        · config_simp; grind
        · refine ⟨rfl, by config_simp; rw [l73], ?_, ?_⟩
          · config_simp; grind
          · config_simp; grind
      zqbjr
      obtain ⟨E₃, p₃⟩ := env d₃ e₃.wb_right ztvqv (fun r hr => by
        rw [f₃.1 r ztsvs,
          h2 r ztkbh])
      have hpre' : preLen P.n H ztg = preLen P.n H i + ztds := by
        omega
      zukiu
      have t2 : ¬ d₂.nreg 50071 < d₂.nreg 50073 := by
        grind
      refine ⟨d₃, k₁ + (ztoch + 1),
        .seq e₁ (.ifLtN_true t1 ztzsc),
        ⟨E₃, p₃, by_omega, Or.inl ⟨?_, ?_, ?_⟩⟩, by_omega, by_omega⟩
      · grind
      · grind
      omega
  · -- a point
    rw [ite_eq_right hkind] at hcnt
    have hk12 : k = 1 ∨ k = 2 := by_omega
    have e₂ := Exec.addN (P := P) w₁ 50073 50063 50067 by_omega
    zue
    by_cases hf : p < preLen P.n H i + 1
    · -- found
      have hp0 : p - preLen P.n H i = 0 := by_omega
      obtain ⟨d₃, k₃, e₃, hk₃, o46, o47, o48, o62⟩ : ∃ d₃ k₃, Exec P W foundPt
          { d₁ with nreg := upd d₁.nreg 50073 _ } d₃ k₃ ∧
          k₃ = 4 ∧ d₃.nreg 50046 = k - 1 ∧ d₃.nreg 50047 = a ∧ d₃.nreg 50048 = b ∧
          d₃.nreg 50062 = H.length := by
        unfold foundPt
        exec_block
        exact ⟨rfl, by config_simp; omega, by config_simp; rw [l66],
          by config_simp; rw [l72], by config_simp; zuozj⟩
      have f₃ := exec_frameB e₃ (B := Bl [50046, 50047, 50048, 50062]) by_decide
      obtain ⟨E₃, p₃⟩ := env d₃ e₃.wb_right f₃.2.2.1 (fun r hr => by
        rw [f₃.1 r ztsvr]
        zuby
        zuosi)
      have hsp : ztbkj[p]? = some (if k = 1 then SymPt.vtx a else SymPt.onEdge a b) := by
        rw [pts_getElem? P.n H ht hpi by_omega, hp0, hitem.1]
        rcases hk12 with h1 | h1 <;> simp [itemOf, HostItem.pts, h1]
      zukit
      have t2 : upd d₁.nreg 50073 ztgil 50071 <
          upd d₁.nreg 50073 ztgil 50073 := by
        zqbjq
      refine ⟨d₃, k₁ + (ztndk + 2),
        .seq e₁ (.ifLtN_false t1 ztncn),
        ⟨E₃, p₃, by_omega, Or.inr ⟨o62, _, hsp, ?_⟩⟩, by_omega, by_omega⟩
      rcases hk12 with h1 | h1
      · zuorm; exact ⟨by_omega, o47⟩
      · zvmyd; exact ⟨by_omega, o47, o48⟩
    · -- not in this item
      obtain ⟨d₃, k₃, e₃, hk₃, o63, o62, o64⟩ : ∃ d₃ k₃, Exec P W advance
          { d₁ with nreg := upd d₁.nreg 50073 _ } d₃ k₃ ∧
          k₃ = 3 ∧ d₃.nreg 50063 = preLen P.n H i + 1 ∧ d₃.nreg 50062 = i + 1 ∧
          d₃.nreg 50064 = Hh + 1 + 3 * ztg := by
        unfold advance
        exec_block
        · zqbjq
        · zqbjq
        · refine ⟨rfl, by config_simp; omega, ?_, ?_⟩
          · zqbjq
          · zqbjq
      zqbjr
      obtain ⟨E₃, p₃⟩ := env d₃ e₃.wb_right f₃.2.2.1 (fun r hr => by
        rw [f₃.1 r ztsvs]
        zuby
        zuosi)
      have hpre' : preLen P.n H ztg = preLen P.n H i + 1 := by_omega
      zukit
      have t2 : ¬ upd d₁.nreg 50073 ztgil 50071 <
          upd d₁.nreg 50073 ztgil 50073 := by
        zqbjq
      refine ⟨d₃, k₁ + ((1 + (k₃ + 2)) + 2),
        .seq e₁ (.ifLtN_false t1 ztzsc),
        ⟨E₃, p₃, by_omega, Or.inl ⟨?_, ?_, ?_⟩⟩, by_omega, by_omega⟩
      · grind
      · grind
      omega

/-- **The lookup of the symbolic point of index `p`** of the host (at most `27 |H| + 5`
steps). -/
theorem look_exec {W Hh p : ℕ} {H : Host} {m : ℕ → ℕ} (c : Config)
    (E : HostEnv W Hh H.length m c) (h71 : c.nreg 50071 = p) (hH : HostAt m Hh H)
    (hwf : HostWF P.n H) (hW : P.n ≤ W) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hN : (H.pts P.n).length ≤ W) (hp : p < (H.pts P.n).length) :
    ∃ c' k, Exec P W lookStmt c c' k ∧ k ≤ 27 * H.length + 5 ∧ FrameB Bhost c c' ∧
      HostEnv W Hh H.length m c' ∧ c'.nreg 50071 = p ∧
      ∃ sp, ztbkj[p]? = some sp ∧ SymPtIn c' 50046 sp := by
  zugnh
  obtain ⟨c₁, k₁, e₁, hk₁, I₁⟩ : ∃ c₁ k₁, Exec P W (block [.constN 50062 0, .constN 50063 0,
      .addN 50064 50060 50067]) c c₁ k₁ ∧ k₁ = 3 ∧ LkI W P.n Hh p H m c₁ := by
    exec_block
    · omega
    · omega
    · config_simp; zuoly; omega
    · refine ⟨rfl, ⟨⟨by_omega, by config_simp; exact E.h60, by config_simp; exact E.h61,
        by config_simp; exact E.h67, by config_simp; exact E.h68, by config_simp; exact E.h69,
        E.mem⟩, by_simp_all, by_simp, Or.inl ⟨?_, ?_, ?_⟩⟩⟩
      · rfl
      · positivity
      · config_simp; zuoly
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 50062) (b := 50061)
    (body := lookBody) (LkI W P.n Hh p H m) ztnys 25
    ztjvt (fun d hd ht => by
      obtain ⟨d', k, e, I', hk, hμ⟩ := lookBody_exec hH hwf hW haW hN hd ht
      grind) I₁
  obtain ⟨E₂, p₂, hi₂, hs₂⟩ := I₂
  zukpc
  have ex : Exec P W lookStmt c c₂ _ := .seq e₁ e₂
  refine ⟨c₂, _, ex, ?_, exec_frameB ex wr_lookStmt, E₂, p₂, ?_⟩
  · omega
  · rcases hs₂ with ⟨-, hle, -⟩ | ⟨-, hd⟩
    · have : zturd := by_omega
      rw [this, preLen_length] at hle
      omega
    omega
end
end NFLoc
end Chazelle.Core
end
namespace Chazelle.Core
namespace NFLoc
open Machine Machine.Stmt Programs SignK WalkKey
open Chazelle.Chain (sideE)
@[expose] public section
section walk
variable (C : Chain)
variable {a b : ℝ}
theorem dirOf_lt (h : a < b) : dirOf a b = 1 := by
  unfold dirOf; simp_all
theorem dirOf_gt (h : b < a) : dirOf a b = 2 := by
  zubqi
theorem dirOf_self (a : ℝ) : dirOf a a = 0 := by
  unfold dirOf; simp

/-- The walk vertex heights of the box and slit edges. -/
theorem chain_dirCode_small {e : ℕ} (he : e < 6) :
    dirCode ztc e = if e = 1 ∨ e = 5 then 2 else if e = 3 then 1 else 0 := by
  zuiza
  zumev
  zulkp
  have hs : C.slitTop.2 = C.radius := rfl
  have h6 : ztoqa := by
    zucqc
  zujht
  simp only [Model.wa, Model.wb, chainModel, hn]
  interval_cases e
  · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_zero, C.sideWalk_vtx_one, hs]
    zulew
  · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_one, C.sideWalk_vtx_two]
    exact dirOf_gt by_simp_all
  · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_two, C.sideWalk_vtx_three]
    zulew
  · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_three, C.sideWalk_vtx_four]
    exact dirOf_lt by_simp_all
  · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_four, C.sideWalk_vtx_five, hs]
    zulew
  · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_five, h6, hs]
    exact dirOf_gt ht

/-- The closing edge goes up the slit. -/
theorem chain_dirCode_last : dirCode ztc ztcc = 1 := by
  zumev
  zujht
  zubzo
  zugto
  exact dirOf_lt ht

/-- The walk vertices of a tour edge. -/
theorem chain_dirCode_tour {i : ℕ} (hi : i < 2 * C.m) :
    dirCode ztc ztcy =
      dirOf (C.vertex ztlx).2 (C.vertex ztwlt).2 := by
  zujht
  zubzo
  rw [C.sideWalk_n, Nat.mod_eq_of_lt by_omega, show i + 6 + 1 = ztg + 6 by ring,
    C.sideWalk_vtx_tour _ by_omega, C.sideWalk_vtx_tour _ by_omega]
  rfl

/-- The tour position of step `i`, by one conditional subtraction. -/
theorem tour_mod {S i m : ℕ} (hS : S ≤ 2 * m) (hi : i < 2 * m) :
    ztbat % ztdk = if i < 2 * m - S then S + i else i - ztbru := by
  zus
  · zudgs
  · zul
    omega

/-- The tour vertex index by one comparison. -/
theorem sideE_eq (m j : ℕ) : sideE m j = if m < j then 2 * m - j else j := by
  zumu

/-- **The chain vertices at the ends of tour edge `i`**. -/
theorem sideIdx_pair (i : ℕ) :
    C.sideIdx C.sideBeta i = sideE C.m (ztwz % ztbb) ∧
      C.sideIdx C.sideBeta ztg = sideE C.m (ztwz % ztbb + 1) :=
  ⟨C.sideIdx_eq _ _, C.sideIdx_succ _ _⟩

/-- A vertex of the chain is the host point of index `(s + k) mod N`. -/
theorem chain_vertex_host {Q : Polygon} {H : Host} (hP : C.P = H.poly Q) (k : ℕ) {sp : SymPt}
    (hsp : ztpze[zttw % C.P.n]? = some sp) : C.vertex k = sp.eval Q := by
  zugil
  generalize zttw % C.P.n = q at hsp ⊢
  zujig
  zumra
end walk

/-! ## The program -/

/-- Read the chain descriptor at `lr 0 + 1`: host handle (`lr 60`), start `s` (`lr 52`), edges
`m` (`lr 53`), top index `T` (`lr 54`), orientation bit (`lr 55`); constants `1 … 6`. -/
def chHead : Stmt := block [.constN 50032 1, .addN 50050 50000 50032, .loadN 50060 50050,
  .addN 50050 50050 50032, .loadN 50052 50050, .addN 50050 50050 50032, .loadN 50053 50050,
  .addN 50050 50050 50032, .loadN 50054 50050, .addN 50050 50050 50032, .loadN 50055 50050,
  .constN 50082 2, .constN 50083 3, .constN 50084 4, .constN 50085 5, .constN 50081 6]

/-- Set the direction code. -/
def setDir (v : ℕ) : Stmt := .instr ztsol

/-- The box and slit edges `0 … 5`. -/
def smallDir : Stmt :=
  .ifLtN 50002 50032 ztqwc (.ifLtN 50002 50082 ztwdm (.ifLtN 50002 50083 ztqwc
    (.ifLtN 50002 50084 (setDir 1) (.ifLtN 50002 50085 ztqwc ztwdm))))

/-- The chain vertex indices `k₁ = sideE m j` (`lr 78`), `k₂ = sideE m (j + 1)` (`lr 79`) of
tour edge `i = lr 56`, `j = (S + i) mod 2m`. -/
def chIdx : Stmt :=
  .seq (block [.addN 50058 50053 50053])
    (.seq (.ifLtN 50055 50032 zteju
        ztbkh)
      (.seq ztnbx
        (.seq (.ifLtN 50056 50089 ztnaq
            ztnbt)
          (.seq (.ifLtN 50053 50077 ztnbv
              ztovj)
            (.seq (.instr (.addN 50090 50077 50032))
              (.ifLtN 50053 50090 ztnbw
                ztovk))))))

/-- The host point of index `(s + lr 91) mod N` (`N` in `lr 87`) into `lr 46 … lr 48`. -/
def hostPt : Stmt :=
  .seq (.instr (.addN 50071 50052 50091))
    (.seq ztifk lookStmt)

/-- A tour edge: the two host points, then the height comparison. -/
def chGeneral : Stmt :=
  .seq chIdx (.seq cntStmt (.seq ztdca
    (.seq hostPt (.seq (block [.copyN 50040 50046, .copyN 50041 50047, .copyN 50042 50048,
        .copyN 50091 50079])
      (.seq hostPt (.seq ztccn
        dirTail))))))

/-- **The direction procedure of the chain model.** -/
def chainDir : Stmt :=
  .seq chHead (.ifLtN 50002 50081 smallDir
    (.seq ztbin
      ztlzy))
theorem wr_chainDir : wr Bdir chainDir = true := by_decide
theorem wr_hostPt : wr Bhost hostPt = true := by_decide
variable {P : Polygon} {W : ℕ}
/-- The host point of index `(s + k) mod N`. -/
theorem hostPt_exec {W Hh s k : ℕ} {H : Host} {m : ℕ → ℕ} (c : Config)
    (E : HostEnv W Hh H.length m c) (hH : HostAt m Hh H) (hwf : HostWF P.n H) (hW : P.n ≤ W)
    (haW : Hh + 3 * H.length + 4 ≤ W) (hNW : 2 * (H.pts P.n).length ≤ W)
    (h52 : c.nreg 50052 = s) (h87 : c.nreg 50087 = (H.pts P.n).length) (h91 : c.nreg 50091 = k)
    (hs : s < (H.pts P.n).length) (hk : k < (H.pts P.n).length) :
    ∃ c' k', Exec P W hostPt c c' k' ∧ k' ≤ 27 * H.length + 9 ∧ FrameB Bhost c c' ∧
      HostEnv W Hh H.length m c' ∧
      ∃ sp, ztbkj[ztnj % (H.pts P.n).length]? = some sp ∧ SymPtIn c' 50046 sp := by
  zugnh
  set N := (H.pts P.n).length
  have e₁ := Exec.addN (P := P) hw 50071 50052 50091 by_omega
  zud
  obtain ⟨c₂, k₂, e₂, hk₂, h71, E₂⟩ : ∃ c₂ k₂, Exec P W
      ztifk
      { c with nreg := upd c.nreg 50071 (c.nreg 50052 + c.nreg 50091) } c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 50071 = ztnj % N ∧ HostEnv W Hh H.length m c₂ := by
    by_cases hlt : s + k < N
    · refine spec_ifLtN_true by_simp_all
        (spec_skip w₁ ⟨by_omega, by config_simp; rw [h52, h91, Nat.mod_eq_of_lt hlt], ?_⟩)
      exact ⟨w₁, by config_simp; exact E.h60, by config_simp; exact E.h61,
        by config_simp; exact E.h67, by config_simp; exact E.h68, by config_simp; exact E.h69,
        E.mem⟩
    · refine spec_ifLtN_false by_simp_all
        (spec_instr ztbly fun w₂ => ztss)
      · config_simp
        rw [h52, h91, h87, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]
      · exact ⟨w₂, by config_simp; exact E.h60, by config_simp; exact E.h61,
          by config_simp; exact E.h67, by config_simp; exact E.h68, by config_simp; exact E.h69,
          E.mem⟩
  have hpN : ztnj % N < N := Nat.mod_lt _ by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, E₃, -, sp, hsp, hin⟩ := look_exec (P := P) c₂ E₂ h71 hH hwf hW haW
    by_omega hpN
  have ex : Exec P W hostPt c c₃ _ := .seq e₁ ztcr
  exact ⟨c₃, _, ex, by_omega, exec_frameB ex wr_hostPt, E₃, sp, hsp, hin⟩

/-- **The chain vertex indices of tour edge `i`.** -/
theorem chIdx_exec (c : Config) (hw : WordsBounded W c) {m T b i : ℕ}
    (h32 : c.nreg 50032 = 1) (h53 : c.nreg 50053 = m) (h54 : c.nreg 50054 = T)
    (h55 : c.nreg 50055 = b) (h56 : c.nreg 50056 = i) (hi : i < 2 * m) (hT : T ≤ m)
    (h2m : 2 * m ≤ W) :
    ∃ c' k, Exec P W chIdx c c' k ∧ k ≤ 20 ∧
      c'.nreg 50078 = sideE m (ztpp % ztdk) ∧
      c'.nreg 50079 = sideE m (ztpp % ztdk + 1) ∧
      FrameB (Bl [50058, 50059, 50089, 50077, 50078, 50090, 50079]) c c' := by
  set S := (if b = 1 then T else 2 * m - T) with hS
  have hS2 : ztsck := by_grind
  -- `2m`
  have e₁ := Exec.addN (P := P) hw 50058 50053 50053 by_omega
  zudkx
  zud
  have q58 : ztrgj := by rw [hc₁]; config_simp; omega
  have q : ztkot := by_simp_all
  -- `S`
  obtain ⟨c₂, k₂, e₂, hk₂, q59, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 50055 50032
      zteju
      ztbkh)
      c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧ c₂.nreg 50059 = S ∧ ∀ r, r ≠ 50059 → c₂.nreg r = c₁.nreg r := by
    zujwt
    have b55 : c₁.nreg 50055 = b := by_simp_all
    have b54 : ztuqh := by_simp_all
    zufqs
    · refine spec_ifLtN_true by_omega
        ztxct
      simp_all
    · zubv
      zujsp
      · refine spec_ifLtN_true by_omega
          ztxct
        config_simp; grind
      · refine spec_ifLtN_false by_omega
          ztywq
        config_simp; grind
  zue
  have g := fun r (h1 : r ≠ 50059) (h2 : r ≠ 50058) => (r₂ r h1).trans (q r h2)
  -- `2m - S`, `j`
  zuepu
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50089 _ }
    with hc₃
  zubj
  have t89 : ztoqx := by
    rw [hc₃]; config_simp; grind
  have t : ztkou := fun r hr => by zumwr; zumwy
  have t56 : c₃.nreg 50056 = i := by_grind
  have t59 : ztuse := by_grind
  obtain ⟨c₄, k₄, e₄, hk₄, j4, r₄⟩ : ∃ c₄ k₄, Exec P W (.ifLtN 50056 50089
      ztnaq ztnbt) c₃ c₄ k₄ ∧
      k₄ ≤ 3 ∧ c₄.nreg 50077 = ztbat % ztdk ∧ ∀ r, r ≠ 50077 → c₄.nreg r = c₃.nreg r := by
    rw [tour_mod hS2 hi]
    zugjk
    · refine spec_ifLtN_true by_omega (spec_instr (Exec.addN w₃ _ _ _
        by_omega) fun _ => ⟨by_omega, ?_, fun r hr => by zumwy⟩)
      config_simp; grind
    · refine spec_ifLtN_false by_omega (spec_instr ztgdp
        fun _ => ztzw)
      config_simp; grind
  zucc
  set j := ztbat % ztdk with hj
  have hjm : ztmwc := Nat.mod_lt _ by_omega
  have u53 : ztusw := by
    rw [r₄ _ by_omega, t _ by_omega, g _ by_omega by_omega, h53]
  have u58 : ztrgm := by
    grind
  have u32 : c₄.nreg 50032 = 1 := by
    rw [r₄ _ by_omega, t _ by_omega, g _ by_omega by_omega, h32]
  -- `k₁`
  obtain ⟨c₅, k₅, e₅, hk₅, k78, r₅⟩ : ∃ c₅ k₅, Exec P W (.ifLtN 50053 50077
      ztnbv ztovj) c₄ c₅ k₅ ∧
      k₅ ≤ 3 ∧ c₅.nreg 50078 = sideE m j ∧ ∀ r, r ≠ 50078 → c₅.nreg r = c₄.nreg r := by
    zugxd

    · refine spec_ifLtN_true by_omega (spec_instr ztgdq
        fun _ => ztzw)
      config_simp; grind
    · refine spec_ifLtN_false by_omega (spec_instr ztlek
        fun _ => ztzw)
      config_simp; grind
  zuef
  have e₆ := Exec.addN (P := P) w₅ 50090 50077 50032
    (by zunit; omega)
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 50090 _ }
    with hc₆
  zujb
  have v90 : c₆.nreg 50090 = j + 1 := by
    zumys; config_simp; zunit
  have v : ∀ r, r ≠ 50090 → c₆.nreg r = c₅.nreg r := fun r hr => by zumys; zumwy
  have v53 : c₆.nreg 50053 = m := by rw [v _ by_omega, r₅ _ by_omega, u53]
  have v58 : c₆.nreg 50058 = 2 * m := by rw [v _ by_omega, r₅ _ by_omega, u58]
  -- `k₂`
  obtain ⟨c₇, k₇, e₇, hk₇, k79, r₇⟩ : ∃ c₇ k₇, Exec P W (.ifLtN 50053 50090
      ztnbw ztovk) c₆ c₇ k₇ ∧
      k₇ ≤ 3 ∧ c₇.nreg 50079 = sideE m ztl ∧ ∀ r, r ≠ 50079 → c₇.nreg r = c₆.nreg r := by
    rw [sideE_eq]
    by_cases hc : m < j + 1
    · refine spec_ifLtN_true by_omega (spec_instr ztjio
        fun _ => ztzw)
      config_simp; grind
    · refine spec_ifLtN_false by_omega (spec_instr (Exec.copyN w₆ _ _)
        fun _ => ztzw)
      config_simp; grind
  have ex : Exec P W chIdx c c₇ _ :=
    .seq ztzsb ztfc
  refine ⟨c₇, _, ex, by_omega, by rw [r₇ _ by_omega, v _ by_omega, k78], k79,
    exec_frameB ex by_decide⟩

/-- The box and slit edges. -/
theorem smallDir_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    (h32 : c.nreg 50032 = 1) (h82 : c.nreg 50082 = 2) (h83 : c.nreg 50083 = 3)
    (h84 : c.nreg 50084 = 4) (h85 : c.nreg 50085 = 5) (he : c.nreg 50002 < 6) :
    ∃ c' k, Exec P W smallDir c c' k ∧ k ≤ 12 ∧
      c'.nreg 10502 = (if c.nreg 50002 = 1 ∨ c.nreg 50002 = 5 then 2
        else if c.nreg 50002 = 3 then 1 else 0) := by
  unfold smallDir setDir
  zujmw
  have fin : ∀ v, v ≤ 2 → ∀ k : ℕ, k ≤ 10 → ztfsq = v →
      ∃ c' k', Exec P W (.instr ztsol) c c' k' ∧ k' + k ≤ 12 ∧
        c'.nreg 10502 = ztfsq :=
    fun v hv k hk hval => ⟨_, 1, Exec.constN hw _ _ by_omega, by_omega,
      by simp_all⟩
  by_cases t0 : e < 1
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 0 by_omega 1 by_omega by_grind
    exact ⟨c', k' + 1, .ifLtN_true by_omega ex, by_omega, hr⟩
  by_cases t1 : e < 2
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 2 by_omega 3 by_omega by_grind
    exact ⟨c', k' + 1 + 2, .ifLtN_false by_omega
      ztcrz, by_omega, hr⟩
  by_cases t2 : e < 3
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 0 by_omega 5 by_omega by_grind
    exact ⟨c', k' + 1 + 2 + 2, .ifLtN_false by_omega
      ztzrk,
      by omega, hr⟩
  by_cases t3 : e < 4
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 1 by_omega 7 by_omega by_grind
    exact ⟨c', k' + 1 + 2 + 2 + 2, .ifLtN_false by_omega
      (.ifLtN_false by_omega (.ifLtN_false by_omega
        ztcrz)), by_omega, hr⟩
  by_cases t4 : e < 5
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 0 by_omega 9 by_omega by_grind
    exact ⟨c', k' + 1 + 2 + 2 + 2 + 2, .ifLtN_false by_omega
      (.ifLtN_false by_omega (.ifLtN_false by_omega
        ztzrk)),
      by omega, hr⟩
  · obtain ⟨c', k', ex, hk, hr⟩ := fin 2 by_omega 10 by_omega by_grind
    exact ⟨c', k' + 2 + 2 + 2 + 2 + 2, .ifLtN_false by_omega
      (.ifLtN_false by_omega (.ifLtN_false by_omega
        (.ifLtN_false by_omega ztdrw))),
      by omega, hr⟩

/-- **A tour edge**: the two host points and their height comparison. -/
theorem chGeneral_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {H : Host} {Hh s m T b i : ℕ} (hH : HostAt c.nmem Hh H)
    (hwf : HostWF P.n H) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hNW : 2 * (H.pts P.n).length ≤ W) (hs : s < (H.pts P.n).length)
    (hmN : m < (H.pts P.n).length) (hT : T ≤ m) (hi : i < 2 * m)
    (h32 : c.nreg 50032 = 1) (h60 : c.nreg 50060 = Hh) (h52 : c.nreg 50052 = s)
    (h53 : c.nreg 50053 = m) (h54 : c.nreg 50054 = T) (h55 : c.nreg 50055 = b)
    (h56 : c.nreg 50056 = i) :
    ∃ c' k, Exec P W chGeneral c c' k ∧ k ≤ 70 * H.length + 560 ∧
      ∃ sp₁ sp₂ : SymPt,
        ztbkj[ztyfo %
          (H.pts P.n).length]? = some sp₁ ∧
        ztbkj[ztxxx %
          (H.pts P.n).length]? = some sp₂ ∧
        c'.nreg 10502 = dirOf (sp₁.eval zta).2 (sp₂.eval zta).2 := by
  zubsq

  -- indices
  obtain ⟨c₁, k₁, e₁, hk₁, k78, k79, f₁⟩ := chIdx_exec (P := P) c hw h32 h53 h54 h55 h56 hi hT
    by_omega
  zud
  zubju

  have g₁ := fun r (hr : Bl [50058, 50059, 50089, 50077, 50078, 50090, 50079] r = false) =>
    f₁.1 r hr
  -- the count
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, n63, E₂⟩ := cnt_exec (P := P) (n := P.n) c₁ w₁
    ztmdh ztmyz haW by_omega
  zubdn
  -- first point
  obtain ⟨c₃, k₃, e₃, hk₃, q87, q91, r₃⟩ : ∃ c₃ k₃, Exec P W
      ztdca c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 50087 = N ∧ c₃.nreg 50091 = sideE m j ∧
      ∀ r, r ≠ 50087 → r ≠ 50091 → c₃.nreg r = c₂.nreg r := by
    zuja
    exec_block
    refine ⟨rfl, by_simp_all, ?_, by_simp_all⟩
    config_simp; rw [g₂ _ by_decide, k78]
  have E₃ : ztrfn :=
    ⟨e₃.wb_right, by zunvp,
      by zunvq, by zunvr,
      by zunvs, by zunvt,
      by rw [(exec_frameB e₃ (B := Bl [50087, 50091]) by_decide).2.2.1, E₂.mem,
        f₁.2.2.1]⟩
  have s₃ : ztusd := by
    zudkk
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, E₄, sp₁, hsp₁, in₁⟩ := hostPt_exec (P := P) c₃ E₃ hH hwf
    by_omega haW hNW s₃ q87 q91 hs by_omega
  zudha
  -- second point
  obtain ⟨c₅, k₅, e₅, hk₅, a₅, q91', r₅⟩ : ∃ c₅ k₅, Exec P W
      ztfxz
      c₄ c₅ k₅ ∧ k₅ = 4 ∧ SymPtIn c₅ 50040 sp₁ ∧ c₅.nreg 50091 = sideE m ztl ∧
      ∀ r, r ≠ 50040 → r ≠ 50041 → r ≠ 50042 → r ≠ 50091 → c₅.nreg r = c₄.nreg r := by
    zubwq
    exec_block
    refine ⟨rfl, symPtIn_copy in₁ (by config_simp) (by config_simp) (by config_simp), ?_,
      fun r h1 h2 h3 h4 => by zunaf⟩
    config_simp
    rw [g₄ _ by_decide, r₃ _ by_omega by_omega, g₂ _ by_decide, k79]
  have E₅ : ztrfo :=
    ⟨e₅.wb_right, by zunpd,
      by zunpe,
      by zunpf,
      by zunpg,
      by zunph,
      by rw [(exec_frameB e₅ (B := Bl [50040, 50041, 50042, 50091]) by_decide).2.2.1,
        E₄.mem]⟩
  have s₅ : ztutc := by
    zuedv
  have n₅ : ztutd := by
    zuedu
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, -, sp₂, hsp₂, in₂⟩ := hostPt_exec (P := P) c₅ E₅ hH hwf
    by_omega haW hNW s₅ n₅ q91' hs by_omega
  have a₆ := symPtIn_copy a₅ ztfrw ztfrw
    ztfrw
  obtain ⟨c₇, k₇, e₇, hk₇, a₇, b₇⟩ : ∃ c₇ k₇, Exec P W
      ztccn c₆ c₇ k₇ ∧ k₇ = 3 ∧
      SymPtIn c₇ 50040 sp₁ ∧ SymPtIn c₇ 50043 sp₂ := by
    zuizr
    exec_block
    exact ⟨rfl, symPtIn_copy a₆ (by config_simp) (by config_simp) (by config_simp),
      symPtIn_copy in₂ (by config_simp) (by config_simp) (by config_simp)⟩
  have l₁ := hLt _ ztnmn
  have l₂ := hLt _ ztnmo

  obtain ⟨c₈, k₈, e₈, hk₈, -, d₈⟩ := dirTail_exec (P := P) hG hW c₇ e₇.wb_right l₁ l₂ a₇ b₇
  refine ⟨c₈, _, .seq e₁ ztey, ?_,
    sp₁, sp₂, hsp₁, hsp₂, d₈⟩
  omega

/-- **The direction procedure of the chain model** (at most `70 |H| + 600` steps). -/
theorem chainDir_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {H : Host} {C : Chain}
    (hC : ChainDescAt c.nmem ztcct zta H C)
    (hDW : c.nreg 50000 + 6 ≤ W) (hHW : c.nmem ztcct + 3 * H.length + 4 ≤ W)
    (hwf : HostWF P.n H) (hs : C.s < C.P.n) (hNW : 2 * C.P.n ≤ W)
    (he : c.nreg 50002 < 2 * C.m + 7) :
    ∃ c' k, Exec P W chainDir c c' k ∧ k ≤ 70 * H.length + 600 ∧ FrameB Bdir c c' ∧
      c'.nreg 10502 = dirCode ztc ztmgd := by
  set D := c.nreg 50000 with hD
  zujmw
  zubhc
  zuc
  have hNlen : ztehu := by
    zujif
    show ((H.pts (Qof P).n).map _).length = _
    simp
  zubnw
  zuwi
  zubb
  -- the header
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W chHead c c₁ k₁ ∧ k₁ = 16 ∧
      (c₁.nreg 50032 = 1 ∧ c₁.nreg 50060 = c.nmem ztef ∧ c₁.nreg 50052 = C.s ∧
        c₁.nreg 50053 = C.m ∧ c₁.nreg 50054 = C.topIdx ∧ c₁.nreg 50055 = c.nmem ztswj ∧
        c₁.nreg 50081 = 6 ∧ c₁.nreg 50082 = 2 ∧ c₁.nreg 50083 = 3 ∧ c₁.nreg 50084 = 4 ∧
        c₁.nreg 50085 = 5 ∧ c₁.nreg 50002 = e ∧ c₁.nmem = c.nmem) := by
    unfold chHead
    exec_block
    all_goals try omega
    all_goals try (config_simp; omega)
    zubee
    config_simp
    grind
  obtain ⟨q32, q60, q52, q53, q54, q55, q81, q82, q83, q84, q85, q02, qm⟩ := q
  zud
  zubta
  · obtain ⟨c₂, k₂, e₂, hk₂, d₂⟩ := smallDir_exec c₁ w₁ by_omega q32 q82 q83 q84 q85
      by_omega
    have ex : Exec P W chainDir c c₂ _ :=
      .seq e₁ ztbxn
    refine ⟨c₂, _, ex, by_omega, exec_frameB ex wr_chainDir, ?_⟩
    rw [d₂, q02, chain_dirCode_small C hsm]
  -- the tour and the closing edge
  obtain ⟨c₂, k₂, e₂, hk₂, q56, q57, r₂⟩ : ∃ c₂ k₂, Exec P W
      ztbin c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg 50056 = e - 6 ∧ c₂.nreg 50057 = e - 6 - C.m ∧
      ∀ r, r ≠ 50056 → r ≠ 50057 → c₂.nreg r = c₁.nreg r := by
    exec_block
    simp_all
  zue
  have p53 : ztpnh := by_simp_all
  zucus
  · zufuu
    have hH₂ : HostAt c₂.nmem (c.nmem ztef) H := by
      zubfs
      zungj; omega
    obtain ⟨c₃, k₃, e₃, hk₃, sp₁, sp₂, hsp₁, hsp₂, d₃⟩ := chGeneral_exec hG hW c₂ w₂
      hH₂ hwf hHW by_omega ztljg
      by_omega hT hi by_simp_all
      by_simp_all by_simp_all p53
      ztkup ztkuq q56
    have ex : Exec P W chainDir c c₃ _ :=
      .seq e₁ (.ifLtN_false ztkuf
        (.seq e₂ (.ifLtN_true ztfbp e₃)))
    refine ⟨c₃, _, ex, by_omega, exec_frameB ex wr_chainDir, ?_⟩
    zubsj

    have hS : (if c.nmem ztswj = 1 then C.topIdx else 2 * C.m - C.topIdx) =
        C.sideS C.sideBeta := by
      zueeu

      · zuikz
      · rw [ite_eq_right by_grind, ite_eq_right hb]
    zupw

    rw [chain_vertex_host C hP _ ztepz,
      chain_vertex_host C hP _ ztepz]
  · zufvg
    have ex : Exec P W chainDir c { c₂ with nreg := upd c₂.nreg 10502 1 } _ :=
      .seq e₁ (.ifLtN_false by_omega
        (.seq e₂ (.ifLtN_false by_omega ztpxz)))
    refine ⟨_, _, ex, by_omega, exec_frameB ex wr_chainDir, ?_⟩
    config_simp
    zukuw
open Chazelle.Chain (sideInArc)
def locDir : Stmt :=
  .seq ztkrf (.ifLtN 50033 50032 chainDir intDir)
theorem wr_locDir : wr Bdir locDir = true := by_decide

/-- **Well-formed chain descriptors** for the direction procedure, for a model descriptor at
`D`: if it describes a chain model, at most `64` host items, the host well formed and
addressable, the start below the number `N` of host points, `2 N` within the word bound.  (It
follows from the specification's `ModelDescWF` and `hostWords`: `locChainWF_of`.) -/
def LocChainWF (P : Polygon) (W : ℕ) (m : ℕ → ℕ) (D : ℕ) : Prop :=
  m D = 0 → ∀ H C, ChainDescAt m ztef zta H C →
    H.length ≤ 64 ∧ HostWF P.n H ∧ m ztef + 3 * H.length + 4 ≤ W ∧ C.s < C.P.n ∧
      2 * C.P.n ≤ W

/-- The precondition of the direction procedure. -/
def LocDPre (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ P.n + 3 ≤ W ∧ c.nreg 50000 + 6 ≤ W ∧ LocChainWF P W c.nmem zthut ∧
    ∃ M, ModelDescAt c.nmem zthut zta M ∧ c.nreg 50002 < M.W.n
variable {m : ℕ → ℕ} {E : ℕ} {P : Polygon}
/-- The layout determines the chain. -/
theorem chain_eq_of_desc {B : ℕ} {Q : Polygon} {H H' : Host} {C C' : Chain}
    (h : ChainDescAt m B Q H C) (h' : ChainDescAt m B Q H' C') : C = C' := by
  have hH : H = H' := hostAt_unique h.1 h'.1
  have hP : C.P = C'.P := by rw [h.2.1, h'.2.1, hH]
  have hs : C.s = C'.s := h.2.2.1.symm.trans h'.2.2.1
  have hm : C.m = C'.m := h.2.2.2.1.symm.trans h'.2.2.2.1
  cases C
  simp_all

/-- **The descriptor determines the model.** -/
theorem modelDesc_unique {D : ℕ} {Q : Polygon} {M M' : Model}
    (h : ModelDescAt m D Q M) (h' : ModelDescAt m D Q M') : M = M' := by
  rcases h with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, -, rfl⟩ <;>
    rcases h' with ⟨h0', H', C', hC', rfl⟩ | ⟨h1', -, rfl⟩
  · rw [chain_eq_of_desc hC hC']
  · omega
  · omega
  · rfl

/-- **The direction procedure meets its contract** (at most `5100` steps). -/
theorem locDir_ok : DirOK locDir 5100 LocDPre := by
  intro P W c hw ⟨hG, hW, hDW, hCW, M, hM, he⟩
  obtain ⟨c₁, k₁, e₁, hk₁, q32, q33, r₁⟩ : ∃ c₁ k₁, Exec P W
      ztkrf c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 50032 = 1 ∧
      c₁.nreg 50033 = c.nmem zthut ∧
      (∀ r, r ≠ 50032 → r ≠ 50033 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    · omega
    simp_all
  obtain ⟨r₁, m₁⟩ := r₁
  zud
  have d₁ : c₁.nreg 50000 = c.nreg 50000 := r₁ _ by_omega by_omega
  have x₁ : ztmvd := r₁ _ by_omega by_omega
  suffices hmain : ∃ c' k, Exec P W locDir c c' k ∧ k ≤ 5100 ∧
      c'.nreg 10502 = dirCode M ztmgd by
    obtain ⟨c', k, ex, hk, hd⟩ := hmain
    exact ⟨c', k, ex, hk, exec_frameB ex wr_locDir, fun M' hM' => by
      rw [hd, modelDesc_unique hM hM']⟩
  zutl
  · obtain ⟨hlen, hwf, hHW, hs, hNW⟩ := hCW h0 H C hC
    have he' : c₁.nreg 50002 < 2 * C.m + 7 := by
      zuozk; simpa [chainModel, C.sideWalk_n] using he
    obtain ⟨c₂, k₂, e₂, hk₂, -, d₂⟩ := chainDir_exec (P := P) hG hW c₁ w₁ (H := H) (C := C)
      by_simp_all by_omega by_simp_all hwf hs hNW
      he'
    refine ⟨c₂, _, .seq e₁ ztbxn, by_omega, ?_⟩
    simp_all
  · have he' : c₁.nreg 50002 < P.n := by
      zuozk
      have := interiorWalk_n zta
      zujom
      zvmwk at he
      zubp
      omega
    obtain ⟨c₂, k₂, e₂, hk₂, -, d₂⟩ := intDir_exec (P := P) hG hW c₁ w₁ he'
      by_omega by_simp_all
    refine ztxzn
    simp_all

/-! ## The specification -/

/-! ## Robust layouts are addressable -/

/-- A word that robustly holds a value lies below the bound. -/
theorem robust_addr {m : ℕ → ℕ} {a v : ℕ} (h : Robust E m fun m' => m' a = v) :
    a < E := by
  zucux
  have := h ztzjx (fun b hb => by
    grind)
  simp_all

/-- A word reached through a pointer that robustly holds a value: the pointer and the word lie
below the bound. -/
theorem robust_addr2 {m : ℕ → ℕ} {b o v : ℕ}
    (h : Robust E m fun m' => m' ztrtu = v) : b < E ∧ m b + o < E := by
  have hb : ztsdn := by
    zucux
    zukat
    have := h ztzka
      (fun a ha => by
        grind)
    simp_all
  refine ztonz
  zucux
  have := h ztzjz (fun a ha => by
    grind)
  grind

/-- **A normal form readable below `E`** has its header, arc area and sequence table below
`E`. -/
theorem nfWithin_bounds {B E : ℕ} {M : Model} {Q : Polygon} {N : NF}
    (h : NFWithin m B E N) (hNF : IsNF M Q N) (hA : 0 < N.arcs.length) :
    B + 7 ≤ E ∧ m ztow + 5 * N.arcs.length ≤ E ∧ m ztcsw + N.arcs.length ≤ E := by
  have hsl := seq_length hNF
  have h1 : Robust E m fun m' => m' (m' ztow + 5 * ztdfr + 4) =
      (N.arc ztdfr).e.hgt := fun m' hm' =>
    ((h m' hm').2.2.2.2.2.2.1 _ by_omega).2.2.2.2
  have h2 : Robust E m fun m' => m' (m' ztcsw + ztdfr) =
      N.seq.getD ztdfr 0 := fun m' hm' =>
    (h m' hm').2.2.2.2.2.2.2.2.1 _ by_omega
  have a1 := robust_addr2 (b := B + 4) (o := 5 * ztdfr + 4)
    by_omega
  have a2 := robust_addr2 h2
  omega

/-- A well-formed host of a chain of the geometry polygon has at most `64 n` points. -/
theorem chain_n_le {m : ℕ → ℕ} {B : ℕ} {H : Host} {C : Chain}
    (hC : ChainDescAt m B zta H C) (hlen : H.length ≤ 64) (hwf : HostWF P.n H) :
    C.P.n ≤ 64 * P.n := by
  zuc
  have e : ztehu := by
    zuozl
    show ((H.pts (Qof P).n).map ztbafl).length = _
    simp_all
  zui
  exact (Host.pts_length_le hwf).trans ztnnl

/-- **The specification's descriptor conditions give the direction procedure's.** -/
theorem locChainWF_of {W E : ℕ} {m : ℕ → ℕ} {D : ℕ} (h : ModelDescWF P E m D)
    (hE : E ≤ W) (hW : hostWords P.n ≤ W) : D + 6 ≤ W ∧ LocChainWF P W m D := by
  refine ⟨by have := h.1; omega, fun h0 H C hC => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := (h.2 h0).2 H C hC
  have hN := chain_n_le hC h1 h2
  zumsu
  grind
