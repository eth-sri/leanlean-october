module
public import Chazelle.Core.ModelAccess
public import Chazelle.Programs.Address
public import Chazelle.Programs.Evidence

public import Chazelle.Core.DownPhaseDrvXKept

/-!
# Down phase, extraction (D6): X-R2, the interior positions of the kept ends

An end of a kept chord is at a host point (`t = 0`) or strictly inside an arc piece of the host
polygon (`t > 0`, inner side).  In both cases its interior walk position is
`xPos … = ⟨⌊hk ι⌋, h + 1⟩` with `ι` the host key of the start point of its walk edge
(`pEdge_rep`: the edge computed from the symbolic host point is `⌊hk ι⌋`), and its key lies in
the closure of an arc of the region (`end_xpos`).

* `cyc_end`: a key outside an arc whose previous gap lies in the arc is the end of the arc;
* `pEdge_rep`: the walk edge of a representing symbolic point;
* `iparam`: the parameter of an interior position from its point;
* `end_xpos`: the interior position of an end of a kept chord.
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

open Set DownHost DownMath
open Chazelle.Chain (SideAttach sidePt sideLeft sideLeftOf sideCcw sideInArc IsHChordIn)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (lerp)
open BuildNF (buildNF)
open DrvR (regHost ivB qE)

/-- **The end of a cyclic interval**: if `y` is not in `(a, b)` but the gap `(x, y)` is, then
`y = b`. -/
theorem cyc_end {n a b x y : ℝ} (hxy : x ≠ y) (hx0 : 0 ≤ x) (hxn : x < n) (hy0 : 0 ≤ y)
    (hyn : y < n) (hb0 : 0 ≤ b) (hbn : b < n)
    (hsub : ∀ z, 0 ≤ z → z < n → sideInArc x y z → sideInArc a b z)
    (hnot : ¬ sideInArc a b y) : y = b := by
  by_contra hyb
  rcases hy0.lt_or_eq with hy | hy
  · -- points just before `y` are in the gap
    have hpt : ∀ u < y, ∃ z > u, z < y ∧ sideInArc a b z := by
      intro u hu
      rcases lt_or_gt_of_ne hxy with h | h
      · refine ⟨(max u x + y) / 2, ?_, ?_, hsub _ ?_ ?_ ?_⟩
        · grind [le_max_left]
        · grind [max_lt]
        · grind [le_max_right]
        · grind [max_lt]
        · grind [sideInArc, le_max_right, max_lt]
      · grind [sideInArc, le_max_left, max_lt, le_max_right]
    unfold sideInArc at hnot hpt
    by_cases hab : a < b
    · simp only [ite_eq_left hab] at hnot hpt
      obtain ⟨z, -, hz2, hz3, -⟩ := at_index hpt (y - 1)
      have hby : b < y := by
        rcases lt_or_ge b y with h | h
        · exact h
        · grind
      grind
    · simp only [ite_eq_right hab] at hnot hpt
      push Not at hnot
      have := hpt b (lt_of_le_of_ne hnot.2 (by intro e; exact hyb (by linarith))); grind
  · subst hy
    unfold sideInArc at hnot
    by_cases hab : a < b
    · have hz := hsub ((max x b + n) / 2) (by grind [le_max_left])
        (by grind [max_lt])
        (by grind [sideInArc, le_max_left])
      unfold sideInArc at hz
      grind
    all_goals grind

/-- A horizontal direction is not strictly inside an arc of horizontal directions that is not a
spike. -/
theorem not_sideCcw_flat {B X A : Point} (hB : B.2 = 0) (hX : X.2 = 0) (hA : A.2 = 0)
    (hns : Chazelle.Chain.sideNonSpike B A) : ¬ sideCcw B X A := by
  have e1 : Chazelle.Chain.sideCross B A = 0 := by
    simp_all [Chazelle.Chain.sideCross]
  have e2 : Chazelle.Chain.sideCross B X = 0 := by
    simp_all [Chazelle.Chain.sideCross]
  rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, h4, -⟩)
  · simp_all
  · simp_all
  · simp_all
  · solve_by_elim [hns]

section

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The walk edge of a representing symbolic point** is the walk edge of its host key. -/
theorem pEdge_rep (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) {li : Bool}
    (hli : li = true ↔ Mountain.LeftInside Q) (hdh : DistinctHeights Q) {ι : ℕ}
    (hι : ι < nk (interiorModel Q) S R) {s : SymPt} (hs : RepPt li Q S R ι s) :
    pEdge li Q.n s = ⌊hk (interiorModel Q) S R ι⌋₊ := by
  have hM : WalkAx Q.interiorModel := walkAx_interiorModel hQ
  have hn3 := Chazelle.Jordan.simple_three_le hQ
  have hb := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hι)
  have hW : Q.interiorModel.W = interiorWalk Q := rfl
  rw [hW, walk_n] at hb
  unfold RepPt at hs
  generalize hk Q.interiorModel S R ι = κ at hs hb ⊢
  have hp : ⌊κ⌋₊ < Q.n := by
    have : (⌊κ⌋₊ : ℝ) < Q.n := lt_of_le_of_lt (Nat.floor_le hb.1) hb.2
    exact_mod_cast this
  have hp1 : (⌊κ⌋₊ + 1) % Q.n < Q.n := at_index Nat.mod_lt _
  -- consecutive walk vertices have distinct heights
  have hd : (Q.vtx (ivB li Q.n ⌊κ⌋₊)).2 ≠ (Q.vtx (ivB li Q.n ((⌊κ⌋₊ + 1) % Q.n))).2 := by
    refine hdh _ _ (ivB_lt li hp) (ivB_lt li hp1) fun h' => ?_
    have := ivB_inj li hp hp1 h'
    by_cases h1 : ⌊κ⌋₊ + 1 < Q.n
    · grind [Nat.mod_eq_of_lt]
    · grind [Nat.mod_self]
  rcases hs with ⟨-, rfl⟩ | ⟨-, h, hhn, hy, (⟨hint, -, rfl⟩ | ⟨hnot, rfl⟩)⟩
  · exact ivB_ivB li hp
  · -- an arc end at a vertex, written with the previous edge
    have hprev : (⌊κ⌋₊ + Q.n - 1) % Q.n < Q.n := at_index Nat.mod_lt _
    have hsucc : ((⌊κ⌋₊ + Q.n - 1) % Q.n + 1) % Q.n = ⌊κ⌋₊ := by
      have := succ_prevIdx (N := Q.n) hp; unfold prevIdx at this; exact this
    simp [pEdge]
    rw_facts [qE_qE, hsucc]
    have hpt : hostPt Q.interiorModel.W κ = Q.vtx (ivB li Q.n ⌊κ⌋₊) := by
      unfold hostPt; rw_facts [← hint, sub_self, Chazelle.Chain.sidePt_zero, hW, DownMath.walk_vtx]
    rw [hpt] at hy
    have hh : h = ivB li Q.n ⌊κ⌋₊ := by
      by_contra hne; exact hdh _ _ hhn (ivB_lt li hp) hne hy
    rw_facts [ite_eq_left]
  · simp [pEdge]
    rw_facts [qE_qE]
    rw [ite_eq_right]
    intro hh
    rw [hh] at hy
    have hf1 : κ - ⌊κ⌋₊ < 1 := by have := Nat.lt_floor_add_one κ; linarith
    unfold hostPt sidePt at hy
    rw [hW, walk_n, DownMath.walk_vtx hli hp, DownMath.walk_vtx hli hp1, Chazelle.Geometry.lerp_snd] at hy
    have : (1 - (κ - ⌊κ⌋₊)) * ((Q.vtx (ivB li Q.n ⌊κ⌋₊)).2 -
        (Q.vtx (ivB li Q.n ((⌊κ⌋₊ + 1) % Q.n))).2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    all_goals grind

/-- **The parameter of an interior walk position** from its point. -/
theorem iparam {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) (hdh : DistinctHeights Q)
    (hn : 2 ≤ Q.n) {q : ℕ} (hq : q < Q.n) {τ : ℝ} {h : ℕ}
    (hz : (sidePt (interiorWalk Q) q τ).2 = (Q.vtx h).2) :
    (interiorModel Q).param Q ⟨q, h + 1⟩ = τ := by
  have hq1 : (q + 1) % Q.n < Q.n := at_index Nat.mod_lt _
  have hd : (Q.vtx (ivB li Q.n q)).2 ≠ (Q.vtx (ivB li Q.n ((q + 1) % Q.n))).2 := by
    refine hdh _ _ (ivB_lt li hq) (ivB_lt li hq1) fun h' => ?_
    have := ivB_inj li hq hq1 h'
    by_cases h1 : q + 1 < Q.n
    · grind [Nat.mod_eq_of_lt]
    · grind [Nat.mod_self]
  have hW : Q.interiorModel.W = interiorWalk Q := rfl
  have ha : Q.interiorModel.wa q = Q.vtx (ivB li Q.n q) := by
    unfold Model.wa; rw_facts [hW, DownMath.walk_vtx]
  have hb : Q.interiorModel.wb q = Q.vtx (ivB li Q.n ((q + 1) % Q.n)) := by
    unfold Model.wb; rw_facts [hW, walk_n, DownMath.walk_vtx]
  unfold sidePt at hz
  rw [walk_n, DownMath.walk_vtx hli hq, DownMath.walk_vtx hli hq1, Chazelle.Geometry.lerp_snd] at hz
  show (if (Q.interiorModel.wa q).2 = (Q.interiorModel.wb q).2 then 0
    else ((Q.vtx h).2 - (Q.interiorModel.wa q).2) /
      ((Q.interiorModel.wb q).2 - (Q.interiorModel.wa q).2)) = τ
  rw [ha, hb, ite_eq_right hd]
  grind

end

section

variable {P : Polygon} {li : Bool} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
  {r : ℕ} {C : Chain} {NR : NF} {i0 g : ℕ}

set_option quotPrecheck false in
local notation "xS" => (buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
  (Qof P)
set_option quotPrecheck false in
local notation "xK" => nk (interiorModel (Qof P)) xS (reg r)
set_option quotPrecheck false in
local notation "xG" => hostPoly (Qof P) xS (reg r)
set_option quotPrecheck false in
local notation "xH" => regHost li (Qof P).n (buildNF (interiorModel (Qof P)) (Qof P) L E) r

namespace XCtx

variable (Y : XCtx P li L E reg r C NR i0 g)
include Y

/-- No horizontal chord is attached inside a horizontal edge of `G`. -/
theorem not_attach_flat {y a b : ℝ} (hab : a < b) {q : ℕ} (hq : q < xK) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hflat : ((xG).vtx q).2 = ((xG).vtx ((q + 1) % xK)).2)
    (hA : SideAttach xG (hseg y a b) q t) : False := by
  obtain ⟨-, -, -, hmem, rA, hrA, hsec⟩ := hA
  obtain ⟨x, hxc, hxne, hxd⟩ := Extract.exists_near_mem hab hmem hrA
  have hx := (Chazelle.Chain.sideLeft_edge (Chazelle.Jordan.simple_vtx_succ_ne Y.gSimple (by rw [Y.gn]; exact hq)) ht x).1 (from_facts hsec)
  rw [Y.gn] at hx
  have hzy : (sidePt xG q t).2 = y := hmem.1
  have hxy := hxc.1
  unfold sidePt at hzy
  rw [Y.gn, Chazelle.Geometry.lerp_snd, ← hflat] at hzy
  have hy : ((xG).vtx q).2 = y := by linarith
  simp_all [det]

/-- A chord gap of the region is a horizontal edge of `G`. -/
theorem chordGap_flat {ι : ℕ} (hι : ι < xK)
    (hC : ChordGap (interiorModel (Qof P)) xS (reg r) ι) :
    ((xG).vtx ι).2 = ((xG).vtx ((ι + 1) % xK)).2 := by
  obtain ⟨c', hc', p₁, p₂, t₁, t₂, hA₁, hA₂, e₁, e₂, -⟩ := hC
  obtain ⟨h', -, a, b, rfl⟩ := Y.X.hFam.2.2 c' hc'
  rw [hostPoly_vtx hι, hostPoly_vtx (at_index Nat.mod_lt _), e₁, e₂,
    hostPt_eq _ hA₁.2.1 hA₁.2.2.1, hostPt_eq _ hA₂.2.1 hA₂.2.2.1, hA₁.2.2.2.1.1, hA₂.2.2.2.1.1]

/-- At a vertex of `G` between two chord gaps no horizontal chord is attached. -/
theorem not_attach_junction {y a b : ℝ} (hab : a < b) {ι : ℕ} (hι : ι < xK)
    (h1 : ((xG).vtx ι).2 = ((xG).vtx ((ι + 1) % xK)).2)
    (h2 : ((xG).vtx (prevIdx xK ι)).2 = ((xG).vtx ι).2)
    (hA : SideAttach xG (hseg y a b) ι 0) : False := by
  obtain ⟨-, -, -, hmem, rA, hrA, hsec⟩ := hA
  obtain ⟨x, hxc, hxne, hxd⟩ := Extract.exists_near_mem hab hmem hrA
  have hx := at_index hsec x
  rw [Chazelle.Chain.sideLeft_zero] at hx
  have hns := FactsInterior.corner_nonSpike Y.gSimple (by rwa [Y.gn])
  unfold Chazelle.Jordan.prevIdx at hns
  rw [Chazelle.Chain.sidePt_zero] at hmem
  unfold prevIdx at h2
  rw [Y.gn] at hns hx
  unfold sideLeftOf at hx
  refine not_sideCcw_flat ?_ ?_ ?_ hns hx
  all_goals try (solve | simp_all)
  · simp; rw [hxc.1, hmem.1]; ring

end XCtx

end

end

end DrvX

end Chazelle.Core
