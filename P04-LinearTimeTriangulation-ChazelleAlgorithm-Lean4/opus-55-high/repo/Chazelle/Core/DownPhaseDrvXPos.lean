module
public import Chazelle.MacT

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
    have hpt : ∀ u, u < y → ∃ z, u < z ∧ z < y ∧ sideInArc a b z := by
      zubgt
      zujeo
      · refine ⟨(max u x + y) / 2, ?_, ?_, hsub _ ?_ ?_ ?_⟩
        · grind
        · grind
        · grind
        · grind
        · zujv
      · refine ⟨(max u 0 + y) / 2, ?_, ?_, hsub _ ?_ ?_ ?_⟩
        · grind
        · grind
        · grind
        · grind
        · zujv
    zuluy
    zuul
    · zuhpr
      obtain ⟨z, -, hz2, hz3, -⟩ := hpt (y - 1) by_linarith
      have hay : a < y := lt_trans hz3 hz2
      have hby : b < y := by
        grind
      grind
    · zuhps
      zudrw
      have hby : b < y := lt_of_le_of_ne hnot.2 by_grind
      grind
  · subst hy
    have hx : ztrzq := lt_of_le_of_ne hx0 (Ne.symm hxy)
    unfold sideInArc at hnot
    zuul
    · have hz := hsub ((max x b + n) / 2) by_grind
        by_grind
        (by unfold sideInArc; grind)
      unfold sideInArc at hz
      grind
    grind

/-- A horizontal direction is not strictly inside an arc of horizontal directions that is not a
spike. -/
theorem not_sideCcw_flat {B X A : Point} (hB : B.2 = 0) (hX : X.2 = 0) (hA : A.2 = 0)
    (hns : Chazelle.Chain.sideNonSpike B A) : ¬ sideCcw B X A := by
  have e1 : Chazelle.Chain.sideCross B A = 0 := by
    zumql
  have e2 : Chazelle.Chain.sideCross B X = 0 := by
    zumql
  rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, h4, -⟩)
  · simp_all
  · simp_all
  · simp_all
  tauto

section

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The walk edge of a representing symbolic point** is the walk edge of its host key. -/
theorem pEdge_rep (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) {li : Bool}
    (hli : li = true ↔ Mountain.LeftInside Q) (hdh : DistinctHeights Q) {ι : ℕ}
    (hι : ι < nk ztd S R) {s : SymPt} (hs : RepPt li Q S R ι s) :
    pEdge li Q.n s = ⌊hk ztd S R ι⌋₊ := by
  zuok
  zuert
  zuljr
  zucmb
  zuijj
  unfold RepPt at hs
  generalize hk ztd S R ι = κ at hs hb ⊢
  have hp : ⌊κ⌋₊ < Q.n := by
    have : (⌊κ⌋₊ : ℝ) < Q.n := lt_of_le_of_lt ztjkj hb.2
    simp_all
  have hp1 : (⌊κ⌋₊ + 1) % Q.n < Q.n := Nat.mod_lt _ by_omega
  -- consecutive walk vertices have distinct heights
  have hd : (Q.vtx zthid).2 ≠ (Q.vtx zthic).2 := by
    refine hdh _ _ ztjyy zttpt fun h' => ?_
    have := ivB_inj li hp hp1 h'
    by_cases h1 : ⌊κ⌋₊ + 1 < Q.n
    · zufu
    · rw [show ⌊κ⌋₊ + 1 = Q.n by omega, Nat.mod_self] at this; omega
  rcases hs with ⟨-, rfl⟩ | ⟨-, h, hhn, hy, (⟨hint, -, rfl⟩ | ⟨hnot, rfl⟩)⟩
  · exact ivB_ivB li hp
  · -- an arc end at a vertex, written with the previous edge
    have hprev : ztmpw % Q.n < Q.n := Nat.mod_lt _ by_omega
    have hsucc : (ztmpw % Q.n + 1) % Q.n = ⌊κ⌋₊ := by
      have := succ_prevIdx (N := Q.n) hp; tauto
    zufbv
    rw [qE_qE li hprev, hsucc]
    have hpt : hostPt (interiorModel Q).W κ = Q.vtx zthid := by
      unfold hostPt; rw [← hint, sub_self, Chazelle.Chain.sidePt_zero, hW, DownMath.walk_vtx hli hp]
    zvmxe at hy
    have hh : h = ivB li Q.n ⌊κ⌋₊ := by
      by_contra hne; exact hdh _ _ hhn ztjyy hne hy
    grind
  · zufbv
    rw [qE_qE li hp]
    zucjw
    zujba
    rw [hh] at hy
    zucap

    unfold hostPt sidePt at hy
    rw [hW, walk_n, DownMath.walk_vtx hli hp, DownMath.walk_vtx hli hp1, Chazelle.Geometry.lerp_snd] at hy
    have : (1 - ztbkw) * ((Q.vtx zthid).2 -
        (Q.vtx zthic).2) = 0 := by_linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    grind

/-- **The parameter of an interior walk position** from its point. -/
theorem iparam {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) (hdh : DistinctHeights Q)
    (hn : 2 ≤ Q.n) {q : ℕ} (hq : q < Q.n) {τ : ℝ} {h : ℕ}
    (hz : (sidePt ztkb q τ).2 = (Q.vtx h).2) :
    (interiorModel Q).param Q ztgph = τ := by
  have hq1 : ztfo % Q.n < Q.n := Nat.mod_lt _ by_omega
  have hd : (Q.vtx ztlqk).2 ≠ (Q.vtx ztbamz).2 := by
    refine hdh _ _ (ivB_lt li hq) (ivB_lt li hq1) fun h' => ?_
    have := ivB_inj li hq hq1 h'
    by_cases h1 : q + 1 < Q.n
    · zufu
    · rw [show q + 1 = Q.n by omega, Nat.mod_self] at this; omega
  zucmb
  have ha : (interiorModel Q).wa q = Q.vtx ztlqk := by
    zugim
  have hb : (interiorModel Q).wb q = Q.vtx ztbamz := by
    unfold Model.wb; rw [hW, walk_n, DownMath.walk_vtx hli hq1]
  unfold sidePt at hz
  rw [walk_n, DownMath.walk_vtx hli hq, DownMath.walk_vtx hli hq1, Chazelle.Geometry.lerp_snd] at hz
  show (if ((interiorModel Q).wa q).2 = ((interiorModel Q).wb q).2 then 0
    else ((Q.vtx h).2 - ((interiorModel Q).wa q).2) /
      (((interiorModel Q).wb q).2 - ((interiorModel Q).wa q).2)) = τ
  grind

end

section

variable {P : Polygon} {li : Bool} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
  {r : ℕ} {C : Chain} {NR : NF} {i0 g : ℕ}

set_option quotPrecheck false in
local notation "xS" => (buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
  zta
set_option quotPrecheck false in
local notation "xK" => nk (interiorModel (Qof P)) xS (reg r)
set_option quotPrecheck false in
local notation "xG" => hostPoly (Qof P) xS (reg r)
set_option quotPrecheck false in
local notation "xH" => regHost li (Qof P).n (buildNF (interiorModel (Qof P)) (Qof P) L E) r

namespace XCtx

variable (Y : XCtx P li L E reg r C NR i0 g)
include Y

variable {y a b : ℝ}
/-- No horizontal chord is attached inside a horizontal edge of `G`. -/
theorem not_attach_flat (hab : a < b) {q : ℕ} (hq : q < xK) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hflat : ((xG).vtx q).2 = ((xG).vtx (ztfo % xK)).2)
    (hA : SideAttach xG ztbiq q t) : False := by
  have hne : (xG).vtx q ≠ (xG).vtx (ztfo % (xG).n) :=
    Chazelle.Jordan.simple_vtx_succ_ne Y.gSimple (by rw [Y.gn]; exact hq)
  obtain ⟨-, -, -, hmem, rA, hrA, hsec⟩ := hA
  obtain ⟨x, hxc, hxne, hxd⟩ := Extract.exists_near_mem hab hmem hrA

  have hx := (Chazelle.Chain.sideLeft_edge hne ht x).1 (hsec x hxc hxne hxd)
  rw [Y.gn] at hx
  have hzy : (sidePt xG q t).2 = y := hmem.1
  have hxy : ztsnb := hxc.1
  unfold sidePt at hzy
  rw [Y.gn, Chazelle.Geometry.lerp_snd, ← hflat] at hzy
  have hy : ((xG).vtx q).2 = y := by_linarith
  zumsi
  simp_all

/-- A chord gap of the region is a horizontal edge of `G`. -/
theorem chordGap_flat {ι : ℕ} (hι : ι < xK)
    (hC : ChordGap (interiorModel (Qof P)) xS (reg r) ι) :
    ((xG).vtx ι).2 = ((xG).vtx ((ι + 1) % xK)).2 := by
  have h3 := Y.three
  obtain ⟨c', hc', p₁, p₂, t₁, t₂, hA₁, hA₂, e₁, e₂, -⟩ := hC
  obtain ⟨h', -, a, b, rfl⟩ := Y.X.hFam.2.2 c' hc'
  rw [hostPoly_vtx hι, hostPoly_vtx (Nat.mod_lt _ (by omega)), e₁, e₂,
    hostPt_eq _ hA₁.2.1 hA₁.2.2.1, hostPt_eq _ hA₂.2.1 hA₂.2.2.1, hA₁.2.2.2.1.1, hA₂.2.2.2.1.1]

/-- At a vertex of `G` between two chord gaps no horizontal chord is attached. -/
theorem not_attach_junction (hab : a < b) {ι : ℕ} (hι : ι < xK)
    (h1 : ((xG).vtx ι).2 = ((xG).vtx ((ι + 1) % xK)).2)
    (h2 : ((xG).vtx (prevIdx xK ι)).2 = ((xG).vtx ι).2)
    (hA : SideAttach xG (hseg y a b) ι 0) : False := by
  have hσ : ι < (xG).n := by rw [Y.gn]; exact hι
  obtain ⟨-, -, -, hmem, rA, hrA, hsec⟩ := hA
  obtain ⟨x, hxc, hxne, hxd⟩ := Extract.exists_near_mem hab hmem hrA
  have hx := hsec x hxc hxne hxd
  rw [Chazelle.Chain.sideLeft_zero] at hx
  have hns := FactsInterior.corner_nonSpike Y.gSimple hσ
  unfold Chazelle.Jordan.prevIdx at hns
  rw [Chazelle.Chain.sidePt_zero] at hmem
  have hzy : ((xG).vtx ι).2 = y := hmem.1
  have hxy : x.2 = y := hxc.1
  unfold prevIdx at h2
  rw [Y.gn] at hns hx
  unfold sideLeftOf at hx
  refine not_sideCcw_flat ?_ ?_ ?_ hns hx
  · simp_all
  · simp_all
  simp_all

end XCtx

end

end

end DrvX

end Chazelle.Core
