module

public import Chazelle.Core.OracleRamLoad
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics

/-!
# Lemma 3.6 (WP-H), part 16: the chords of the table, geometrically

The query compares the ends of the chords at the height of the ray with the origin through their
*class* (`xpClass`: left side of the box, right side, or a symbolic point of `Q`).  This file
shows that the class describes the end exactly:

* `end_class`: a point of walk edge `w` at the height of a vertex `h` below the top of the chain
  is `(xv w h, y_h)` (`xv`: `-r`, `r`, or the abscissa of the symbolic point `xpSym`); it is on
  the chain (and on the edge `symIdx (xpSym …)` of `Q`) iff its class is `1`.
* `chord_facts`: a chord record of a normal form is the horizontal chord of the domain between
  its two ends.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
open Chazelle.Visibility (rayPt hseg)

@[expose] public section

open Classical in
/-- **The abscissa of the end `(w, h + 1)`** by its class. -/
noncomputable def xv (P : Polygon) (C : Chain) (V : QV) (w h : ℕ) : ℝ :=
  if xpClass w = 0 then -C.radius else if xpClass w = 2 then C.radius else xpX P C V w h

/-- The chain data of the values. -/
structure TopOK (P : Polygon) (C : Chain) (V : QV) : Prop where
  hv : QVOK P C V
  top : (Qof P).vtx V.tv = C.top
  tv_lt : V.tv < P.n
  hD : DistinctHeights (Qof P)

variable {P : Polygon} {C : Chain} {V : QV}

theorem vtx_snd_lt_radius (hCQ : C.P = Qof P) {h : ℕ} (hh : h < P.n) :
    |((Qof P).vtx h).2| < C.radius := by
  have hn : h < C.P.n := by rwx [hCQ, show (Qof P).n = P.n from shear_n _ _]
  have := Chazelle.Jordan.abs_snd_vtx_le_coordBound C.P hn
  rw [hCQ] at this
  have := C.coordBound_lt_radius
  rw [hCQ] at this
  linarith

theorem abs_fst_lt_radius_of_mem {p : Point} (hp : p ∈ C.set) : |p.1| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).1 C.coordBound_lt_radius

/-- The chain edge `ci` is the edge `eIdx n s ci` of `Q`. -/
theorem chainEdge_eq_edge (hv : QVOK P C V) (ci : ℕ) :
    C.chainEdge ci = (Qof P).edge (eIdx P.n V.s ci) := by
  unfold Chain.chainEdge Chain.edgeIdx eIdx
  rw [hv.CQ, hv.s, show (Qof P).n = P.n from shear_n _ _]

/-- The edges of `Q` are not horizontal. -/
theorem edge_nonhoriz (hD : DistinctHeights (Qof P)) {e : ℕ} (he : e < P.n) (hn : 2 ≤ P.n) :
    ((Qof P).vtx e).2 ≠ ((Qof P).vtx ((e + 1) % (Qof P).n)).2 := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  refine hD _ _ (by rwx [hQn]) (Nat.mod_lt _ (by rwo [hQn])) ?_
  rw [hQn]
  intro h
  rcases Nat.lt_or_ge (e + 1) P.n with h' | h'
  · rwo [Nat.mod_eq_of_lt h'] at h
  · rwo [show e + 1 = P.n by omega, Nat.mod_self] at h

/-- **The ends by class.** -/
theorem end_class (hT : TopOK P C V) {w h : ℕ} (hw : w < 2 * C.m + 7) (hh : h < P.n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hy : (Geometry.lerp ((chainModel C).W.vtx w)
      ((chainModel C).W.vtx ((w + 1) % (chainModel C).W.n)) t).2 = ((Qof P).vtx h).2)
    (hyt : ((Qof P).vtx h).2 ≤ C.top.2) :
    Geometry.lerp ((chainModel C).W.vtx w)
        ((chainModel C).W.vtx ((w + 1) % (chainModel C).W.n)) t =
      (xv P C V w h, ((Qof P).vtx h).2) ∧
    (xpClass w = 1 → Geometry.lerp ((chainModel C).W.vtx w)
        ((chainModel C).W.vtx ((w + 1) % (chainModel C).W.n)) t ∈ C.set ∧
      symIdx (xpSym C V P.n w h) < P.n ∧
      Geometry.lerp ((chainModel C).W.vtx w)
        ((chainModel C).W.vtx ((w + 1) % (chainModel C).W.n)) t ∈
          (Qof P).edge (symIdx (xpSym C V P.n w h))) ∧
    (xpClass w ≠ 1 → Geometry.lerp ((chainModel C).W.vtx w)
        ((chainModel C).W.vtx ((w + 1) % (chainModel C).W.n)) t ∉ C.set) := by
  have hv := hT.hv
  have hR := C.radius_pos
  have hyR := vtx_snd_lt_radius hv.CQ hh
  rw [abs_lt] at hyR
  have htopR := C.top_snd_lt_radius
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  have hm1 := C.one_le
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn2 : 2 ≤ P.n := by
    have := C.add_one_le; rwo [hv.CQ, hQn] at this
  set y := ((Qof P).vtx h).2 with hydef
  -- the box and slit edges
  have hW : ∀ i, (chainModel C).W.vtx i = (C.sideWalk C.sideBeta).vtx i := fun _ => rfl
  rw [hnW] at hy ⊢
  simp only [hW] at hy ⊢
  have notset : ∀ p : Point, |p.1| = C.radius → p ∉ C.set := fun p hp hm => by
    have := abs_fst_lt_radius_of_mem hm; linarith
  rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ (6 ≤ w ∧ w < 2 * C.m + 6) ∨
      w = 2 * C.m + 6) with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h6, h6'⟩ | rfl
  · exfalso
    rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_zero, C.sideWalk_vtx_one] at hy
    sil [Geometry.lerp, Chain.slitTop] at hy
  · rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_one, C.sideWalk_vtx_two] at hy ⊢
    have hx : xpClass 1 = 0 := rfl
    refine ⟨?_, by rwo [hx], fun _ => notset _ ?_⟩
    · ext
      · simp [Geometry.lerp, xv, hx]
      · exact hy
    · simp [Geometry.lerp, abs_of_neg (neg_lt_zero.2 hR)]
  · exfalso
    rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_two, C.sideWalk_vtx_three] at hy
    sil [Geometry.lerp] at hy
  · rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hy ⊢
    have hx : xpClass 3 = 2 := rfl
    refine ⟨?_, by rwo [hx], fun _ => notset _ ?_⟩
    · ext
      · simp [Geometry.lerp, xv, hx]
      · exact hy
    · simp [Geometry.lerp, abs_of_pos hR]
  · exfalso
    rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_four, C.sideWalk_vtx_five] at hy
    sil [Geometry.lerp, Chain.slitTop] at hy
  · exfalso
    rw [Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_five, C.sideWalk_vtx_six] at hy
    simp only [Geometry.lerp, Chain.slitTop] at hy
    nlinarith
  · -- a tour edge
    obtain ⟨i, rfl⟩ : ∃ i, w = i + 6 := ⟨w - 6, by omega⟩
    rw [Nat.mod_eq_of_lt (by omega), show i + 6 + 1 = (i + 1) + 6 by ring,
      C.sideWalk_vtx_tour _ (by omega), C.sideWalk_vtx_tour _ (by omega)] at hy ⊢
    have hseg : Geometry.lerp (C.sideTour C.sideBeta i) (C.sideTour C.sideBeta (i + 1)) t ∈
        C.chainEdge (tci C i) := by
      rw [← tour_seg C i]; exact ⟨t, ht0, ht1.le, rfl⟩
    have hcls : xpClass (i + 6) = 1 := by unfold xpClass; splao
    have hsym : xpSym C V P.n (i + 6) h = .onEdge (eIdx P.n V.s (tci C i)) h := by
      unfold xpSym; rw [ite_eq_left (by rwo [hv.m]), show i + 6 - 6 = i by omega]
    have hci := tci_lt C i
    set e := eIdx P.n V.s (tci C i) with he
    have hen : e < P.n := Nat.mod_lt _ (by omega)
    have hedge := hseg
    rw [chainEdge_eq_edge hv] at hedge
    set p := Geometry.lerp (C.sideTour C.sideBeta i) (C.sideTour C.sideBeta (i + 1)) t
    have hx : p.1 = xe (Qof P) e h := by
      have := (rayPt_mem_edge_iff (Qof P) (edge_nonhoriz hT.hD hen hn2) (z := p) hy (Or.inl rfl)
        0).1 (by simpa [rayPt] using hedge)
      linarith [this.2]
    refine ⟨?_, fun _ => ⟨⟨_, hci, hseg⟩, by rwx [hsym], by rwx [hsym]⟩,
      fun h' => absurd hcls h'⟩
    ext
    · show p.1 = xv P C V (i + 6) h
      rw [hx]; urr xv xpX [ite_eq_right (by omega), ite_eq_right (by omega), hsym]
    · exact hy
  · -- up the slit: the top vertex
    rw [show (2 * C.m + 6 + 1) % (2 * C.m + 7) = 0 by
      rw [show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self],
      show 2 * C.m + 6 = 2 * C.m + 6 from rfl, C.sideWalk_vtx_tour _ le_rfl,
      C.sideTour_two_m, C.sideWalk_vtx_zero] at hy ⊢
    simp only [Geometry.lerp, Chain.slitTop] at hy
    have ht : t = 0 := by nlinarith
    subst ht
    have hcls : xpClass (2 * C.m + 6) = 1 := by unfold xpClass; splao
    have hsym : xpSym C V P.n (2 * C.m + 6) h = .vtx V.tv := by
      unfold xpSym; rw [ite_eq_right (by rwo [hv.m])]
    rw [Geometry.lerp_zero]
    refine ⟨?_, fun _ => ⟨C.top_mem_set, by rw [hsym]; exact hT.tv_lt, ?_⟩,
      fun h' => absurd hcls h'⟩
    · ext
      · unfold xv xpX; rw [ite_eq_right (by omega), ite_eq_right (by omega), hsym]
        show C.top.1 = ((Qof P).vtx V.tv).1; rw [hT.top]
      · sil at hy
    · rw [hsym]; show C.top ∈ Polygon.edge _ V.tv
      rw [← hT.top]; exact ⟨0, le_rfl, zero_le_one, by simp⟩

/-- Two horizontal segments with `a < b` are equal only if their data are. -/
theorem hseg_inj {y a b y' a' b' : ℝ} (hab : a < b) (ha'b' : a' ≤ b')
    (h : hseg y a b = hseg y' a' b') : y = y' ∧ a = a' ∧ b = b' := by
  have m1 : ((a, y) : Point) ∈ hseg y' a' b' := by rw [← h]; exact ⟨rfl, le_rfl, hab.le⟩
  have m2 : ((b, y) : Point) ∈ hseg y' a' b' := by rw [← h]; exact ⟨rfl, hab.le, le_rfl⟩
  have e1  := m1.1
  subst e1
  have m3 : ((a', y) : Point) ∈ hseg y a b := by rw [h]; exact ⟨rfl, le_rfl, ha'b'⟩
  have m4 : ((b', y) : Point) ∈ hseg y a b := by rw [h]; exact ⟨rfl, ha'b', le_rfl⟩
  exact ⟨rfl, le_antisymm m3.2.1 m1.2.1, le_antisymm m2.2.2 m4.2.2⟩

/-- The facts of one end of a chord. -/
def EndFacts (P : Polygon) (C : Chain) (V : QV) (w h : ℕ) : Prop :=
  (chainModel C).pos (Qof P) ⟨w, h + 1⟩ = (xv P C V w h, ((Qof P).vtx h).2) ∧
    (xpClass w = 1 → (chainModel C).pos (Qof P) ⟨w, h + 1⟩ ∈ C.set ∧
      symIdx (xpSym C V P.n w h) < P.n ∧
      (chainModel C).pos (Qof P) ⟨w, h + 1⟩ ∈ (Qof P).edge (symIdx (xpSym C V P.n w h))) ∧
    (xpClass w ≠ 1 → (chainModel C).pos (Qof P) ⟨w, h + 1⟩ ∉ C.set) ∧
    (w < 2 * C.m + 7 ∧ 0 ≤ (chainModel C).param (Qof P) ⟨w, h + 1⟩ ∧
      (chainModel C).param (Qof P) ⟨w, h + 1⟩ < 1)

/-- **A chord record is the horizontal chord of the domain between its two ends.** -/
theorem chord_facts (hT : TopOK P C V) {N : NF} (hN : IsNF (chainModel C) (Qof P) N) {i : ℕ}
    (hi : i < N.chords.length) :
    (N.chord i).h < P.n ∧ ((Qof P).vtx (N.chord i).h).2 ≤ C.top.2 ∧
    Chazelle.Chain.IsHChordIn C.dom ((Qof P).vtx (N.chord i).h).2
      (xv P C V (N.chord i).lp (N.chord i).h) (xv P C V (N.chord i).rp (N.chord i).h) ∧
    (N.chord i).toSet (chainModel C) (Qof P) = hseg ((Qof P).vtx (N.chord i).h).2
      (xv P C V (N.chord i).lp (N.chord i).h) (xv P C V (N.chord i).rp (N.chord i).h) ∧
    EndFacts P C V (N.chord i).lp (N.chord i).h ∧ EndFacts P C V (N.chord i).rp (N.chord i).h := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨hFam, -, hAtt, reg, -, -, -, -, -, hh, -⟩ := hN
  set ch := N.chord i with hch
  have hhn : ch.h < P.n := by have := hh i hi; rwa [hQn] at this
  have hmem : ch.toSet (chainModel C) (Qof P) ∈ N.F (chainModel C) (Qof P) :=
    ⟨ch, by rw [hch]; unfold NF.chord; rw [NFLoc.getD_of_lt _ hi]; exact List.getElem_mem hi,
      rfl⟩
  obtain ⟨y', a, b, hH, hyt, hset⟩ := hFam.2.1 hmem
  obtain ⟨⟨hl1, hl2, hl3, hl4, -⟩, ⟨hr1, hr2, hr3, hr4, -⟩⟩ := hAtt i hi
  -- the two ends lie on the chord
  have hl : (chainModel C).pos (Qof P) ch.lpos ∈ hseg ((Qof P).vtx ch.h).2
      ((chainModel C).pos (Qof P) ch.lpos).1 ((chainModel C).pos (Qof P) ch.rpos).1 := hl4
  have hr : (chainModel C).pos (Qof P) ch.rpos ∈ hseg ((Qof P).vtx ch.h).2
      ((chainModel C).pos (Qof P) ch.lpos).1 ((chainModel C).pos (Qof P) ch.rpos).1 := hr4
  have hle  := hl.2.2
  obtain ⟨ey, ea, eb⟩ := hseg_inj hH.lt hle hset.symm
  have hyt' : ((Qof P).vtx ch.h).2 ≤ C.top.2 := by rwx [← ey]
  have hnW := walk_n C
  have EL := end_class hT (w := ch.lp) (h := ch.h) (by rwx [← hnW]) hhn hl2 hl3 hl.1 hyt'
  have ER := end_class hT (w := ch.rp) (h := ch.h) (by rwx [← hnW]) hhn hr2 hr3 hr.1 hyt'
  have xl : ((chainModel C).pos (Qof P) ch.lpos).1 = xv P C V ch.lp ch.h := by
    have := congrArg Prod.fst EL.1; exact this
  have xr : ((chainModel C).pos (Qof P) ch.rpos).1 = xv P C V ch.rp ch.h := by
    have := congrArg Prod.fst ER.1; exact this
  refine ⟨hhn, hyt', ?_, ?_, ⟨EL.1, EL.2.1, EL.2.2, by rwx [← hnW], hl2, hl3⟩,
    ⟨ER.1, ER.2.1, ER.2.2, by rwx [← hnW], hr2, hr3⟩⟩
  · rwx [← xl, ← xr, ← ey, ← ea, ← eb]
  · show hseg _ _ _ = _
    rw [xl, xr]

/-! ## The comparisons of the program, geometrically -/

open Classical in
/-- **The effective origin**: the point where the ray enters the closed box (the origin itself if
it is in the box). -/
noncomputable def ζOf (C : Chain) (V : QV) (z : Point) : ℝ :=
  if V.σb = 1 then max z.1 (-C.radius) else min z.1 C.radius

/-- The origin is not past the box in the direction of the ray. -/
def NotPast (C : Chain) (V : QV) (z : Point) : Prop :=
  (V.σb = 1 → z.1 < C.radius) ∧ (V.σb ≠ 1 → -C.radius < z.1)

/-- A class-`1` end is strictly inside the box. -/
def EndGood (P : Polygon) (C : Chain) (V : QV) (w h : ℕ) : Prop :=
  xpClass w = 1 → |xpX P C V w h| < C.radius

theorem xpClass_cases (w : ℕ) : xpClass w = 0 ∨ xpClass w = 1 ∨ xpClass w = 2 := by
  unfold xpClass; split_ifs <;> simp

theorem endGtZ_iff {z : Point} (hσ : V.σb = 1) (hz : ZoOK C (sgnOf V.σb) z V.zo)
    (hnp : NotPast C V z) {w h : ℕ} (he : EndGood P C V w h) :
    EndGtZ P C V w h ↔ ζOf C V z < xv P C V w h := by
  have hR := C.radius_pos
  have hs : sgnOf V.σb = 1 := by unfold sgnOf; rw [ite_eq_left hσ]
  have hzR := hnp.1 hσ
  unfold EndGtZ ζOf xv; rw [ite_eq_left hσ]
  rcases xpClass_cases w with h0 | h1 | h2
  · rw [h0]; simp only [ite_true]
    constructor
    · rintro (h | ⟨h, -⟩) <;> omega
    · intro h; exact absurd h (not_lt.2 (le_max_right _ _))
  · have hx := abs_lt.1 (he h1)
    rw [h1]; simp only [show ¬ (1 : ℕ) = 0 by omega, show ¬ (1 : ℕ) = 2 by omega, ite_false,
      true_and, false_or]
    rcases hz with e | ⟨e, hz1⟩
    · rw [e]; simp only [max_lt_iff]
      exact ⟨fun h => ⟨h, hx.1⟩, fun h => h.1⟩
    · rw [e]; rw [hs] at hz1
      simp only [hσ, true_iff, max_lt_iff]
      exact ⟨by rw [hz1]; linarith [hx.1], hx.1⟩
  · rw [h2]; simp only [show ¬ (2 : ℕ) = 0 by omega, ite_false, ite_true, true_or, true_iff,
      max_lt_iff]
    exact ⟨hzR, by linarith⟩

theorem endLtZ_iff {z : Point} (hσ : V.σb ≠ 1) (hz : ZoOK C (sgnOf V.σb) z V.zo)
    (hnp : NotPast C V z) {w h : ℕ} (he : EndGood P C V w h) :
    EndLtZ P C V w h ↔ xv P C V w h < ζOf C V z := by
  have hR := C.radius_pos
  have hs : sgnOf V.σb = -1 := by unfold sgnOf; rw [ite_eq_right hσ]
  have hzR := hnp.2 hσ
  unfold EndLtZ ζOf xv; rw [ite_eq_right hσ]
  rcases xpClass_cases w with h0 | h1 | h2
  · rw [h0]; simp only [ite_true, true_or, true_iff, lt_min_iff]
    exact ⟨hzR, by linarith⟩
  · have hx := abs_lt.1 (he h1)
    rw [h1]; simp only [show ¬ (1 : ℕ) = 0 by omega, show ¬ (1 : ℕ) = 2 by omega, ite_false,
      true_and, false_or]
    rcases hz with e | ⟨e, hz1⟩
    · rw [e]; simp only [lt_min_iff]
      exact ⟨fun h => ⟨h, hx.2⟩, fun h => h.1⟩
    · rw [e]; rw [hs] at hz1
      refine ⟨fun _ => ?_, fun _ => hσ⟩
      rw [lt_min_iff]
      exact ⟨by rw [hz1]; linarith [hx.2], hx.2⟩
  · rw [h2]; simp only [show ¬ (2 : ℕ) = 0 by omega, show ¬ (2 : ℕ) = 1 by omega, ite_false,
      ite_true, false_and, or_false, false_iff, not_lt]
    exact min_le_right _ _

theorem endLtD_iff {eD w h : ℕ} (_he : EndGood P C V w h)
    (hD : |xe (Qof P) eD V.hz| < C.radius) :
    EndLtD P C V eD w h ↔ xv P C V w h < xe (Qof P) eD V.hz := by
  have hx := abs_lt.1 hD
  unfold EndLtD xv
  rcases xpClass_cases w with h0 | h1 | h2
  · rw [h0]; simp only [ite_true, true_or, true_iff]; exact hx.1
  · rw [h1]; simp only [show ¬ (1 : ℕ) = 0 by omega, show ¬ (1 : ℕ) = 2 by omega, ite_false,
      true_and, false_or]
  · rw [h2]; simp only [show ¬ (2 : ℕ) = 0 by omega, show ¬ (2 : ℕ) = 1 by omega, ite_false,
      ite_true, false_and, or_false, false_iff, not_lt]; exact hx.2.le

theorem endGtD_iff {eD w h : ℕ} (_he : EndGood P C V w h)
    (hD : |xe (Qof P) eD V.hz| < C.radius) :
    EndGtD P C V eD w h ↔ xe (Qof P) eD V.hz < xv P C V w h := by
  have hx := abs_lt.1 hD
  unfold EndGtD xv
  rcases xpClass_cases w with h0 | h1 | h2
  · rw [h0]; simp only [show ¬ (0 : ℕ) = 2 by omega, show ¬ (0 : ℕ) = 1 by omega, ite_true,
      false_and, or_false, false_iff, not_lt]; exact hx.1.le
  · rw [h1]; simp only [show ¬ (1 : ℕ) = 0 by omega, show ¬ (1 : ℕ) = 2 by omega, ite_false,
      true_and, false_or]
  · rw [h2]; simp only [show ¬ (2 : ℕ) = 0 by omega, ite_false, ite_true, true_or, true_iff]
    exact hx.2

/-- The ends of a chord are good. -/
theorem EndFacts.good {w h : ℕ} (hE : EndFacts P C V w h) : EndGood P C V w h := by
  intro h1
  obtain ⟨hpos, hc, -, -⟩ := hE
  have hm := (hc h1).1
  rw [hpos] at hm
  have := abs_fst_lt_radius_of_mem hm
  unfold xv at this; rwa [ite_eq_right (by omega), ite_eq_right (by omega)] at this

end

end OracleR

end Chazelle.Core
