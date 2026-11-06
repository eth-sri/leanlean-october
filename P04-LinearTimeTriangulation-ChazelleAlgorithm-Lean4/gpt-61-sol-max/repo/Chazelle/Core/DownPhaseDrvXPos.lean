module

public meta import Chazelle.Arithmetic

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
      intro u hu
      rcases lt_or_gt_of_ne hxy with h | h
      · refine ⟨(max u x + y) / 2, ?_, ?_, hsub _ ?_ ?_ ?_⟩
        · ram_grind
        · ram_grind
        · ram_grind
        all_goals ram_grind
      · ram_grind
    ram_grind
  · subst hy
    have hx : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxy)
    unfold sideInArc at hnot
    by_cases hab : a < b
    · have hz := hsub ((max x b + n) / 2) (by ram_grind)
        (by ram_grind)
        (by ram_grind)
      ram_grind
    ram_grind

/-- A horizontal direction is not strictly inside an arc of horizontal directions that is not a
spike. -/
theorem not_sideCcw_flat {B X A : Point} (hB : B.2 = 0) (hX : X.2 = 0) (hA : A.2 = 0)
    (hns : Chazelle.Chain.sideNonSpike B A) : ¬ sideCcw B X A := by
  grind [Chazelle.Chain.sideCcw, Chazelle.Chain.sideNonSpike, Chazelle.Chain.sideCross]

section

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The walk edge of a representing symbolic point** is the walk edge of its host key. -/
theorem pEdge_rep (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) {li : Bool}
    (hli : li = true ↔ Mountain.LeftInside Q) (hdh : DistinctHeights Q) {ι : ℕ}
    (hι : ι < nk (interiorModel Q) S R) {s : SymPt} (hs : RepPt li Q S R ι s) :
    pEdge li Q.n s = ⌊hk (interiorModel Q) S R ι⌋₊ := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  have hn3 : 3 ≤ Q.n := Chazelle.Jordan.simple_three_le hQ
  have hb := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hι)
  have hW : (interiorModel Q).W = interiorWalk Q := rfl
  rw [hW, walk_n] at hb
  unfold RepPt at hs
  generalize hk (interiorModel Q) S R ι = κ at hs hb ⊢
  have hp : ⌊κ⌋₊ < Q.n := by
    have : (⌊κ⌋₊ : ℝ) < Q.n := lt_of_le_of_lt (Nat.floor_le hb.1) hb.2
    exact_mod_cast this
  have hp1 : (⌊κ⌋₊ + 1) % Q.n < Q.n := Nat.mod_lt _ (by omega)
  -- consecutive walk vertices have distinct heights
  have hd : (Q.vtx (ivB li Q.n ⌊κ⌋₊)).2 ≠ (Q.vtx (ivB li Q.n ((⌊κ⌋₊ + 1) % Q.n))).2 := by
    refine hdh _ _ (ivB_lt li hp) (ivB_lt li hp1) fun h' => ?_
    have := ivB_inj li hp hp1 h'
    by_cases h1 : ⌊κ⌋₊ + 1 < Q.n
    · rw [Nat.mod_eq_of_lt h1] at this; omega
    grind [Nat.mod_self]
  rcases hs with ⟨-, rfl⟩ | ⟨-, h, hhn, hy, (⟨hint, -, rfl⟩ | ⟨hnot, rfl⟩)⟩
  · exact ivB_ivB li hp
  · -- an arc end at a vertex, written with the previous edge
    have hprev : (⌊κ⌋₊ + Q.n - 1) % Q.n < Q.n := Nat.mod_lt _ (by omega)
    have hsucc : ((⌊κ⌋₊ + Q.n - 1) % Q.n + 1) % Q.n = ⌊κ⌋₊ := by
      have := succ_prevIdx (N := Q.n) hp; unfold prevIdx at this; exact this
    simp only [pEdge]
    rw [qE_qE li hprev, hsucc]
    have hpt : hostPt (interiorModel Q).W κ = Q.vtx (ivB li Q.n ⌊κ⌋₊) := by
      unfold hostPt; rw [← hint, sub_self, Chazelle.Chain.sidePt_zero, hW, DownMath.walk_vtx hli hp]
    rw [hpt] at hy
    have hh : h = ivB li Q.n ⌊κ⌋₊ := by
      by_contra hne; exact hdh _ _ hhn (ivB_lt li hp) hne hy
    ram_grind
  · simp only [pEdge]
    rw [qE_qE li hp]
    rw [ite_eq_right]
    intro hh
    rw [hh] at hy
    
    have hf1 : κ - ⌊κ⌋₊ < 1 := by have := Nat.lt_floor_add_one κ; linarith
    unfold hostPt sidePt at hy
    rw [hW, walk_n, DownMath.walk_vtx hli hp, DownMath.walk_vtx hli hp1, Chazelle.Geometry.lerp_snd] at hy
    have : (1 - (κ - ⌊κ⌋₊)) * ((Q.vtx (ivB li Q.n ⌊κ⌋₊)).2 -
        (Q.vtx (ivB li Q.n ((⌊κ⌋₊ + 1) % Q.n))).2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    all_goals ram_grind

/-- **The parameter of an interior walk position** from its point. -/
theorem iparam {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) (hdh : DistinctHeights Q)
    (hn : 2 ≤ Q.n) {q : ℕ} (hq : q < Q.n) {τ : ℝ} {h : ℕ}
    (hz : (sidePt (interiorWalk Q) q τ).2 = (Q.vtx h).2) :
    (interiorModel Q).param Q ⟨q, h + 1⟩ = τ := by
  have hq1 : (q + 1) % Q.n < Q.n := Nat.mod_lt _ (by omega)
  have hd : (Q.vtx (ivB li Q.n q)).2 ≠ (Q.vtx (ivB li Q.n ((q + 1) % Q.n))).2 := by
    refine hdh _ _ (ivB_lt li hq) (ivB_lt li hq1) fun h' => ?_
    have := ivB_inj li hq hq1 h'
    by_cases h1 : q + 1 < Q.n
    · rw [Nat.mod_eq_of_lt h1] at this; omega
    grind [Nat.mod_self]
  have hW : (interiorModel Q).W = interiorWalk Q := rfl
  have ha : (interiorModel Q).wa q = Q.vtx (ivB li Q.n q) := by
    unfold Model.wa; rw [hW, DownMath.walk_vtx hli hq]
  have hb : (interiorModel Q).wb q = Q.vtx (ivB li Q.n ((q + 1) % Q.n)) := by
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
  have hne : (xG).vtx q ≠ (xG).vtx ((q + 1) % (xG).n) :=
    Chazelle.Jordan.simple_vtx_succ_ne Y.gSimple (by rw [Y.gn]; exact hq)
  obtain ⟨-, -, -, hmem, rA, hrA, hsec⟩ := hA
  obtain ⟨x, hxc, hxne, hxd⟩ := Extract.exists_near_mem hab hmem hrA
  have hx := (Chazelle.Chain.sideLeft_edge hne ht x).1 (hsec x hxc hxne hxd)
  rw [Y.gn] at hx
  have hzy : (sidePt xG q t).2 = y := hmem.1
  have hxy : x.2 = y := hxc.1
  unfold sidePt at hzy
  rw [Y.gn, Chazelle.Geometry.lerp_snd, ← hflat] at hzy
  aesop (add simp [det, sub_self, mul_zero]) (add safe (by omega))

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
theorem not_attach_junction {y a b : ℝ} (hab : a < b) {ι : ℕ} (hι : ι < xK)
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
  · simp only [Prod.snd_sub]; ram_grind
  · simp only [Prod.snd_sub]; ram_grind
  · simp only [Prod.snd_sub]; ram_grind

end XCtx

end

end

end DrvX

end Chazelle.Core
