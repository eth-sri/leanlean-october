module

public import Chazelle.MacT
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.SweepPrimJun
public import Chazelle.Core.GranInitL3
public import Chazelle.Core.ShootCutCore2

section
set_option hygiene false
local macro "zqblb" : tactic => `(tactic| (have d2 : decide zthvg = false := by_grind
                                           obtain ⟨c', k, ex, hk, h⟩ := leaf [] by_simp))
local macro "zqblc" : tactic => `(tactic| have : Cn ≠ N ∧ Cn ≠ N + 1 ∧ Cn ≠ N + 2 ∧ Cn ≠ N + 3 := by_omega)
local macro "zqbld" : tactic => `(tactic| obtain ⟨c', k, ex, hk, h⟩ := leaf [ztdrt] by_simp)
local macro "zqble" : tactic => `(tactic| obtain ⟨c', k, ex, hk, h⟩ := leaf [ztgwn] by_simp)
local macro "zqblf" : tactic => `(tactic| simp only [pieceR, posR, Prod.mk.injEq, WPos.mk.injEq])
local macro "zqblg" : tactic => `(tactic| refine ⟨_, _, ex, by_omega, v0 _ ?_, exec_frameB ex wk⟩)
local macro "zqblh" : tactic => `(tactic| (simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hq
                                           subst hq
                                           rw [← p₁]))
local macro "zqbli" : tactic => `(tactic| exact ⟨_, _, ex, by_omega, by_grind, exec_frameB ex wk⟩)
local macro "zqblj" : tactic => `(tactic| have g1 : Bone d r = false := by simp [Bone, hr.1])
set_option hygiene true

/-!
# Shooting at a list of arcs with holes, part 2: cutting an arc by a hole on the RAM

The wrapper `shotList sh R` (module `ShotList`) keeps its registers at `R + i` (`i < 300`), in a
band of the caller.  This file computes, at the cutting level `ℓ ≤ 2`, the pieces of the current
arc `[a, b]` (registers `L, L + 1` and `L + 2, L + 3`, `L = R + 40 + 10 ℓ`) outside the hole
`(x, y)` (the walk vertices in `R + 10 + 2 ℓ`, `R + 11 + 2 ℓ`), if the hole is present
(`ℓ < H`, `H = R + 9`).

Arc ends are **normalised** walk positions: proper (`ProperPos`) with `hgt = 0` exactly when the
parameter is `0` (`NormPos`).  Then the order of the keys of two positions is lexicographic in
(edge, interior bit), except for two interior positions of one edge, where `offCmp` decides
(`key_lt_iff`).  The bits of the twelve key comparisons give the tests of `cutK` (`kltB`, the
compiled formulas `siaF`), and the selection block writes the pieces: the first into the next
level's arc registers `L + 10 … L + 13`, the second into `L + 4 … L + 7`, their number into
`L + 8` (`cutB_exec`).
-/
namespace Chazelle.Core
namespace ShotList
open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
@[expose] public section
def NormPos (M : Model) (Q : Polygon) (n : ℕ) (x : WPos) : Prop :=
  ProperPos M Q n x ∧ (x.hgt = 0 ∨ 0 < M.param Q x)

/-- The interior bit of a position (`1` iff its height code is positive). -/
def ibit (x : WPos) : ℕ := if 0 < x.hgt then 1 else 0
variable {M : Model} {Q : Polygon} {n : ℕ} {P : Polygon} {W : ℕ} (c : Config)
theorem param_of_norm {x : WPos} (h : NormPos M Q n x) :
    (x.hgt = 0 → M.param Q x = 0) ∧ (0 < x.hgt → 0 < M.param Q x) := by
  refine ⟨fun h0 => by unfold Model.param; zvmzn, fun hp => ?_⟩
  rcases h.2 with h0 | h0
  · omega
  omega

/-- **The order of two normalised keys**, when they are not both inside one edge: lexicographic
in the edge and the interior bit. -/
theorem key_lt_iff {x y : WPos} (hx : NormPos M Q n x)
    (hy : NormPos M Q n y) (hne : ¬ (x.edge = y.edge ∧ 0 < x.hgt ∧ 0 < y.hgt)) :
    M.key Q x < M.key Q y ↔ x.edge < y.edge ∨ (x.edge = y.edge ∧ ibit x < ibit y) := by
  have px := param_of_norm hx
  have py := param_of_norm hy
  obtain ⟨⟨hx0, hx1, -⟩, -⟩ := hx
  obtain ⟨⟨hy0, hy1, -⟩, -⟩ := hy
  unfold Model.key ibit
  constructor
  · zuq
    rcases lt_trichotomy x.edge y.edge with he | he | he
    · omega
    · grind
    · exfalso
      have : ztddy := by exact_mod_cast he
      linarith
  · rintro (he | ⟨he, hi⟩)
    · have : ztddx := by exact_mod_cast he
      linarith
    grind

/-- The order of two keys is the order of their offsets from `0`. -/
theorem key_lt_iff_off {M : Model} {Q : Polygon} {x y : WPos} (hx0 : 0 ≤ M.param Q x)
    (hy0 : 0 ≤ M.param Q y) :
    M.key Q x < M.key Q y ↔
      WalkEmbed.off M.W.n 0 ztbys < WalkEmbed.off M.W.n 0 ztfof := by
  have k0 : (0 : ℝ) ≤ M.key Q x := by
    zuhac
  have k1 : (0 : ℝ) ≤ M.key Q y := by
    zuhac
  unfold WalkEmbed.off
  simp_all

/-! ## The comparison blocks -/

/-- The interior bit of a height code. -/
def ibv (h : ℕ) : ℕ := if 0 < h then 1 else 0

/-- Lexicographic order of (edge, interior bit) pairs. -/
def LexLt (e i e' i' : ℕ) : Prop := e < e' ∨ (e = e' ∧ i < i')

/-- `d := 1` if `(eu, ibv hu) < (ev, ibv hv)` lexicographically, else `0` (`z` holds `0`). -/
def kltB (eu hu ev hv d z : ℕ) : Stmt :=
  .ifLtN eu ev ztoul
    (.ifLtN ev eu ztfes
      (.ifLtN z hu ztfes
        (.ifLtN z hv ztoul ztfes)))

/-- The registers `kltB` writes. -/
def Bone (d : ℕ) (r : ℕ) : Bool := r == d
theorem wr_kltB (eu hu ev hv d z : ℕ) : wr ztuww zthik = true := by
  simp [wr, kltB, wrOK, Bone]
theorem kltB_exec (hw : WordsBounded W c) (hW : 1 ≤ W)
    (eu hu ev hv d z : ℕ) (hz : c.nreg z = 0) :
    ∃ c' k, Exec P W zthik c c' k ∧ k ≤ 9 ∧
      BitIs c' d (LexLt (c.nreg eu) (ibv (c.nreg hu)) (c.nreg ev) (ibv (c.nreg hv))) ∧
      FrameB ztuww c c' := by
  have e1 := Exec.constN (P := P) hw d 1 hW
  have e0 := Exec.constN (P := P) hw d 0 by_omega
  have wk := wr_kltB eu hu ev hv d z
  have v1 : ∀ p : Prop, p → BitIs { c with nreg := upd c.nreg d 1 } d p :=
    fun p hp => ztuge
  have v0 : ∀ p : Prop, ¬ p → BitIs { c with nreg := upd c.nreg d 0 } d p :=
    fun p hp => ztuge
  unfold LexLt ibv
  by_cases h1 : c.nreg eu < c.nreg ev
  · have ex : ztbov := .ifLtN_true h1 e1
    zqbli
  by_cases h2 : c.nreg ev < c.nreg eu
  · have ex : ztbov := .ifLtN_false h1 (.ifLtN_true h2 e0)
    zqbli
  by_cases h3 : c.nreg z < c.nreg hu
  · have ex : ztbov :=
      .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true h3 e0))
    zqblg
    grind
  by_cases h4 : c.nreg z < c.nreg hv
  · have ex : ztbov :=
      .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_false h3 (.ifLtN_true h4 e1)))
    refine ⟨_, _, ex, by_omega, v1 _ ?_, exec_frameB ex wk⟩
    grind
  · have ex : ztbov :=
      .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_false h3 (.ifLtN_false h4 e0)))
    zqblg
    simp_all

/-! ## The selection of the pieces -/

/-- The four ends of an arc and a hole. -/
inductive End where
  | A | B | X | Y
  deriving DecidableEq

/-- **The pieces selected by the bits**: `hp` the hole is present, `c1 … c6` the tests of
`cutK` (`(x, y) ∋ a`, `(a, b) ∋ y`, `(y, b) ∋ x`, `(a, b) ∋ x`, `(x, b) ∋ y`, `x = a`). -/
def selT (hp c1 c2 c3 c4 c5 c6 : Bool) : List ztjij :=
  if !hp then [ztgwn]
  else if c1 then (if c2 then (if c3 then [ztmzy] else [ztdrt]) else [])
  else if c4 then ztgwo :: (if c5 then [ztdrt] else [])
  else if c6 then (if c2 then [ztdrt] else [])
  else [ztgwn]

/-- The value of an end. -/
def End.val {α : Type} (a b x y : α) : End → α
  | .A => a
  | .B => b
  | .X => x
  | .Y => y

/-- **`cutK` is the selection** at the truth values of its tests. -/
theorem cutK_eq_selT {α : Type} (ka kb kx ky : ℝ) (a b x y : α) {c1 c2 c3 c4 c5 c6 : Bool}
    (h1 : c1 = true ↔ sideInArc kx ky ka) (h2 : c2 = true ↔ sideInArc ka kb ky)
    (h3 : c3 = true ↔ sideInArc ky kb kx) (h4 : c4 = true ↔ sideInArc ka kb kx)
    (h5 : c5 = true ↔ sideInArc kx kb ky) (h6 : c6 = true ↔ kx = ka) :
    cutK ka kb kx ky a b x y =
      (selT true c1 c2 c3 c4 c5 c6).map (fun e => (End.val a b x y e.1, End.val a b x y e.2)) := by
  unfold cutK selT
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases q1 : sideInArc kx ky ka
  · have := h1.2 q1
    simp only [q1, this, ↓reduceIte]
    zuirw
    · have := h2.2 q2
      simp only [q2, this, ↓reduceIte]
      by_cases q3 : sideInArc ky kb kx
      · simp [q3, h3.2 q3, End.val]
      · have : c3 = false := by_simp_all
        simp [q3, this, End.val]
    simp_all
  · have e1 : c1 = false := by_simp_all
    simp only [q1, e1, ↓reduceIte, Bool.false_eq_true]
    by_cases q4 : sideInArc ka kb kx
    · simp only [q4, h4.2 q4, ↓reduceIte]
      by_cases q5 : sideInArc kx kb ky
      · simp [q5, h5.2 q5, End.val]
      · have : c5 = false := by_simp_all
        simp [q5, this, End.val]
    · have e4 : c4 = false := by_simp_all
      simp only [q4, e4, ↓reduceIte, Bool.false_eq_true]
      by_cases q6 : kx = ka
      · simp only [q6, ↓reduceIte, h6.2 q6]
        zuirw
        · simp [q2, h2.2 q2, End.val]
        simp_all
      · have e6 : c6 = false := by_simp_all
        simp [q6, e6, End.val]

/-- The register pair of an end: `A = (L, L + 1)`, `B = (L + 2, L + 3)`, `X = (hx, z)`,
`Y = (hy, z)`. -/
def End.regs (L hx hy z : ℕ) : End → ℕ × ℕ
  | .A => ztctg
  | .B => ztbyo
  | .X => (hx, z)
  | .Y => (hy, z)

/-- Write the piece with ends `u`, `v` into `d … d + 3`. -/
def putPiece (d : ℕ) (u v : ℕ × ℕ) : List Instr :=
  [.copyN d u.1, .copyN ztet u.2, .copyN ztvq v.1, .copyN ztjte v.2]

/-- The leaves of the selection tree: the pieces into `N …` and `S …`, their number into `Cn`. -/
def selLeaf (L hx hy z N S Cn : ℕ) : List ztjij → Stmt
  | [] => block [.constN Cn 0]
  | [p] => .seq ztfbh
      (block [.constN Cn 1])
  | p :: q :: _ => .seq ztfbh
      (.seq (block (putPiece S (End.regs L hx hy z q.1) (End.regs L hx hy z q.2)))
        (block [.constN Cn 2]))

/-- **The selection tree** on the bit registers `hpA < hpB` (hole present) and `c1 … c6`
(tested against the zero register `z`). -/
def selB (L hx hy z N S Cn hpA hpB c1 c2 c3 c4 c5 c6 : ℕ) : Stmt :=
  let lf := selLeaf L hx hy z N S Cn
  .ifLtN hpA hpB
    (.ifLtN z c1
      (.ifLtN z c2 (.ifLtN z c3 (lf [ztmzy]) ztzmr) zttsg)
      (.ifLtN z c4 (.ifLtN z c5 (lf [ztgwo, ztdrt]) (lf [ztgwo]))
        (.ifLtN z c6 (.ifLtN z c2 ztzmr zttsg) ztzms)))
    ztzms

/-- The walk position in the registers `e`, `h`. -/
def posR (c : Config) (r : ℕ × ℕ) : WPos := ⟨c.nreg r.1, c.nreg r.2⟩

/-- The piece in the registers `d … d + 3`. -/
def pieceR (c : Config) (d : ℕ) : WPos × WPos := (posR c (d, d + 1), posR c (d + 2, d + 3))

/-- **The pieces in the registers**: their number in `Cn`, the first in `N …`, the second in
`S …`. -/
def PiecesAt (c : Config) (N S Cn : ℕ) (ps : List ztqx) : Prop :=
  c.nreg Cn = ps.length ∧ ps.length ≤ 2 ∧ (∀ p, ps[0]? = some p → pieceR c N = p) ∧
    (∀ p, ps[1]? = some p → pieceR c S = p)

/-- The output registers of the selection avoid the input registers. -/
def SelDisj (L hx hy z N S Cn : ℕ) : Prop :=
  ∀ e : End, ∀ o, (o = Cn ∨ (N ≤ o ∧ o < N + 4) ∨ (S ≤ o ∧ o < S + 4)) →
    (End.regs L hx hy z e).1 ≠ o ∧ (End.regs L hx hy z e).2 ≠ o

/-- **Writing a piece**: the ends read from `u`, `v` (not overwritten before they are read). -/
theorem putPiece_exec (hw : WordsBounded W c) {d : ℕ}
    {u v : ℕ × ℕ} (hu : u.2 ≠ d) (hv1 : v.1 ≠ d ∧ v.1 ≠ d + 1)
    (hv2 : v.2 ≠ d ∧ v.2 ≠ d + 1 ∧ v.2 ≠ d + 2) :
    ∃ c' k, Exec P W (block (putPiece d u v)) c c' k ∧ k = 4 ∧
      pieceR c' d = (posR c u, posR c v) ∧
      (∀ r, ¬ (d ≤ r ∧ r < d + 4) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨u1, u2⟩ := u
  zuide
  simp only at hu hv1 hv2
  unfold putPiece
  exec_block
  refine ztgob
  · zqblf
    simp_all
  · zubd
theorem selLeaf_exec (hw : WordsBounded W c) (hW : 2 ≤ W)
    {L hx hy z N S Cn : ℕ} (hd : SelDisj L hx hy z N S Cn) (hNS : N + 4 ≤ S ∨ S + 4 ≤ N)
    (hC : Cn < N ∨ N + 4 ≤ Cn) (hC' : Cn < S ∨ S + 4 ≤ Cn) (tl : List ztjij)
    (htl : tl.length ≤ 2) :
    ∃ c' k, Exec P W (selLeaf L hx hy z N S Cn tl) c c' k ∧ k ≤ 9 ∧
      PiecesAt c' N S Cn (tl.map fun e => (posR c ztowp,
        posR c ztowq)) ∧
      ztcqh ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ne := hd
  match tl, htl with
  | [], _ =>
    unfold selLeaf
    exec_block
    · omega
    · refine ⟨by_omega, ⟨by_simp, by_simp, by_simp, by_simp⟩, fun r h1 _ _ => by simp [upd, h1],
        rfl, rfl, rfl, rfl⟩
  | [p], _ =>
    zuebk
    obtain ⟨c₁, k₁, e₁, hk₁, p₁, r₁, m₁, rr₁, rm₁, o₁⟩ := putPiece_exec (P := P) c hw
      (ne u N by_omega).2
      ⟨(ne v N ztdby).1,
        (ne v zttg ztbaly).1⟩
      ⟨(ne v N ztdby).2,
        (ne v zttg ztbaly).2,
        (ne v _ by_omega).2⟩
    have e₂ := Exec.constN (P := P) e₁.wb_right Cn 1 by_omega
    refine ⟨_, _, .seq e₁ ztihc, by_omega,
      ⟨by_simp, by_simp, fun q hq => ?_, by_simp⟩, fun r h1 h2 _ => ?_, m₁, rr₁, rm₁, o₁⟩
    · zqblh
      simp only [pieceR, posR]
      zqblc
      simp [upd, this.1.symm, this.2.1.symm, this.2.2.1.symm, this.2.2.2.symm]
    · zugzq
      grind
  | [p, q], _ =>
    zuebk
    obtain ⟨u', v'⟩ := q
    obtain ⟨c₁, k₁, e₁, hk₁, p₁, r₁, m₁, rr₁, rm₁, o₁⟩ := putPiece_exec c hw
      (ne u N by_omega).2
      ⟨(ne v N ztdby).1,
        (ne v zttg ztbaly).1⟩
      ⟨(ne v N ztdby).2,
        (ne v zttg ztbaly).2,
        (ne v _ by_omega).2⟩
    obtain ⟨c₂, k₂, e₂, hk₂, p₂, r₂, m₂, rr₂, rm₂, o₂⟩ := putPiece_exec (P := P) c₁ e₁.wb_right
      (ne u' S by_omega).2
      ⟨(ne v' S ztkqh).1,
        (ne v' ztbgu ztbasf).1⟩
      ⟨(ne v' S ztkqh).2,
        (ne v' ztbgu ztbasf).2,
        (ne v' _ by_omega).2⟩
    have e₃ := Exec.constN (P := P) e₂.wb_right Cn 2 by_omega
    have keep : ∀ e : End, posR c₁ ztowo = posR c ztowo := by
      zuchf
      have h1 := ne e N by_omega
      have h2 := ne e zttg by_omega
      have h3 := ne e (N + 2) by_omega
      have h4 := ne e (N + 3) by_omega
      simp only [posR, WPos.mk.injEq]
      exact ⟨r₁ _ by_omega, r₁ _ by_omega⟩
    refine ⟨_, _, .seq e₁ ztkpr,
      by omega, ⟨by_simp, by_simp, fun q hq => ?_, fun q hq => ?_⟩, fun r h1 h2 h3 => ?_,
      m₂.trans m₁, rr₂.trans rr₁, rm₂.trans rm₁, o₂.trans o₁⟩
    · zqblh
      zqblf
      zqblc
      simp only [upd, ↓reduceIte, this.1.symm, this.2.1.symm, this.2.2.1.symm,
        this.2.2.2.symm]
      refine ⟨⟨r₂ _ by_omega, r₂ _ by_omega⟩, r₂ _ by_omega, r₂ _ by_omega⟩
    · simp only [List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hq
      subst hq
      rw [← keep u', ← keep v', ← p₂]
      zqblf
      have : Cn ≠ S ∧ Cn ≠ S + 1 ∧ Cn ≠ S + 2 ∧ Cn ≠ S + 3 := by_omega
      simp only [upd, ↓reduceIte, this.1.symm, this.2.1.symm, this.2.2.1.symm,
        this.2.2.2.symm, and_self]
    · zugzq
      rw [r₂ r h3, r₁ r h2]

/-- The pieces of the selection, as walk positions read in `c`. -/
def selPos (c : Config) (L hx hy z : ℕ) (tl : List ztjij) : List ztqx :=
  tl.map fun e => (posR c ztowp, posR c ztowq)

/-- **The selection tree** computes the pieces of `selT` at the bits of its registers. -/
theorem selB_exec (hw : WordsBounded W c) (hW : 2 ≤ W)
    {L hx hy z N S Cn hpA hpB c1 c2 c3 c4 c5 c6 : ℕ} (hd : SelDisj L hx hy z N S Cn)
    (hNS : N + 4 ≤ S ∨ S + 4 ≤ N) (hC : Cn < N ∨ N + 4 ≤ Cn) (hC' : Cn < S ∨ S + 4 ≤ Cn)
    (hz : c.nreg z = 0) (b1 : c.nreg c1 ≤ 1) (b2 : c.nreg c2 ≤ 1) (b3 : c.nreg c3 ≤ 1)
    (b4 : c.nreg c4 ≤ 1) (b5 : c.nreg c5 ≤ 1) (b6 : c.nreg c6 ≤ 1) :
    ∃ c' k, Exec P W (selB L hx hy z N S Cn hpA hpB c1 c2 c3 c4 c5 c6) c c' k ∧ k ≤ 24 ∧
      PiecesAt c' N S Cn (selPos c L hx hy z (selT (decide ztjsh)
        (decide ztllj) (decide zthvg) (decide ztllk)
        (decide ztlll) (decide ztllm) (decide ztlln))) ∧
      ztcqh ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have leaf := fun (tl : List _) (htl : tl.length ≤ 2) =>
    selLeaf_exec (P := P) c hw hW hd hNS hC hC' tl htl
  have t : ∀ {r : ℕ}, c.nreg r ≤ 1 → (c.nreg z < c.nreg r ↔ c.nreg r = 1) := by_grind
  unfold selB
  zubi
  by_cases hp : c.nreg hpA < c.nreg hpB
  · have hpd : decide ztjsh = true := by_grind
    zumny
    by_cases q1 : c.nreg c1 = 1
    · have d1 : decide ztllj = true := by_grind
      zuirv
      · zujwx
        by_cases q3 : c.nreg c3 = 1
        · have d3 : decide ztllk = true := by_grind
          obtain ⟨c', k, ex, hk, h⟩ := leaf [ztmzy] by_simp
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_true by_omega (.ifLtN_true by_omega
            ztcrz)), by_omega, ?_⟩
          zugcm
        · have d3 : decide ztllk = false := by_grind
          zqbld
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_true by_omega (.ifLtN_true by_omega
            ztdrw)), by_omega, ?_⟩
          zugcm
      · zqblb
        refine ⟨c', _, .ifLtN_true hp (.ifLtN_true by_omega
          ztdrw), by_omega, ?_⟩
        rw [d1, d2]; exact h
    · have d1 : decide ztllj = false := by_grind
      have n1 : ¬ c.nreg z < c.nreg c1 := by_omega
      by_cases q4 : c.nreg c4 = 1
      · have d4 : decide ztlll = true := by_grind
        by_cases q5 : c.nreg c5 = 1
        · have d5 : decide ztllm = true := by_grind
          obtain ⟨c', k, ex, hk, h⟩ := leaf [ztgwo, ztdrt] by_simp
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_true by_omega
            ztcrz)), by_omega, ?_⟩
          zugcn
        · have d5 : decide ztllm = false := by_grind
          obtain ⟨c', k, ex, hk, h⟩ := leaf [ztgwo] by_simp
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_true by_omega
            ztdrw)), by_omega, ?_⟩
          zugcn
      · have d4 : decide ztlll = false := by_grind
        have n4 : ¬ c.nreg z < c.nreg c4 := by_omega
        by_cases q6 : c.nreg c6 = 1
        · have d6 : decide ztlln = true := by_grind
          zuirv
          · zujwx
            zqbld
            refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_false n4
              (.ifLtN_true by_omega ztcrz))), by_omega, ?_⟩
            zuexg
          · zqblb
            refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_false n4
              (.ifLtN_true by_omega ztdrw))),
              by omega, ?_⟩
            zuexg
        · have d6 : decide ztlln = false := by_grind
          zqble
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_false n4
            ztdrw)), by_omega, ?_⟩
          rw [d1, d4, d6]; exact h
  · have hpd : decide ztjsh = false := by_grind
    zumny
    zqble
    exact ⟨c', _, .ifLtN_false hp ex, by_omega, h⟩

/-! ## A sequence of comparisons -/

/-- A comparison `(eu, hu, ev, hv, d)`: `d := [(eu, ibv hu) < (ev, ibv hv)]`. -/
abbrev Cmp := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The comparisons one after the other. -/
def kltSeq (z : ℕ) : List Cmp → Stmt
  | [] => .skip
  | (eu, hu, ev, hv, d) :: t => .seq zthik (kltSeq z t)

/-- The output registers of the comparisons. -/
def cmpOuts (ts : List Cmp) : List ℕ := ts.map fun t => t.2.2.2.2

/-- The inputs of the comparisons and the zero register avoid the outputs; the outputs are
distinct. -/
def CmpOK (z : ℕ) (ts : List Cmp) : Prop :=
  z ∉ cmpOuts ts ∧ (cmpOuts ts).Nodup ∧
    ∀ t ∈ ts, t.1 ∉ cmpOuts ts ∧ t.2.1 ∉ cmpOuts ts ∧ t.2.2.1 ∉ cmpOuts ts ∧
      t.2.2.2.1 ∉ cmpOuts ts

/-- The write set of a list of comparisons. -/
def Bouts (ts : List Cmp) (r : ℕ) : Bool := (cmpOuts ts).contains r
theorem kltSeq_exec (hW : 1 ≤ W) (z : ℕ) :
    ∀ (ts : List Cmp) (c : Config), WordsBounded W c → c.nreg z = 0 → CmpOK z ts →
      ∃ c' k, Exec P W (kltSeq z ts) c c' k ∧ k ≤ 9 * ts.length ∧
        (∀ t ∈ ts, BitIs c' t.2.2.2.2 (LexLt (c.nreg t.1) (ibv (c.nreg t.2.1))
          (c.nreg t.2.2.1) (ibv (c.nreg t.2.2.2.1)))) ∧ FrameB (Bouts ts) c c'
  | [], c, hw, _, _ => ⟨c, 0, .skip hw, by_simp, by_simp, FrameB.refl _ _⟩
  | (eu, hu, ev, hv, d) :: t, c, hw, hz, ⟨hzo, hnd, hin⟩ => by
    have hd : d ∉ cmpOuts t := by
      simp only [cmpOuts, List.map_cons, List.nodup_cons] at hnd; tauto
    have hok : CmpOK z t := by
      refine ⟨fun h => hzo ?_, (List.nodup_cons.1 hnd).2, fun u hu' => ?_⟩
      · tauto
      · obtain ⟨a1, a2, a3, a4⟩ := hin u by_simp_all
        simp only [cmpOuts, List.map_cons, List.mem_cons, not_or] at a1 a2 a3 a4 ⊢
        grind
    obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := kltB_exec (P := P) c hw hW eu hu ev hv d z hz
    have hzd : z ≠ d := by
      intro h; apply hzo; zvmwc; tauto
    have z₁ : c₁.nreg z = 0 := by
      have g : Bone d z = false := by simp [Bone, hzd]
      rw [f₁.1 z g]; exact hz
    obtain ⟨c₂, k₂, e₂, hk₂, b₂, f₂⟩ := kltSeq_exec hW z t c₁ e₁.wb_right z₁ hok
    have keep1 : ∀ r, r ∉ cmpOuts ((eu, hu, ev, hv, d) :: t) → c₂.nreg r = c.nreg r := by
      zuz
      simp only [cmpOuts, List.map_cons, List.mem_cons, not_or] at hr
      have g2 : ztsap := by
        zuggt
      zqblj
      rw [f₂.1 r g2, f₁.1 r g1]
    refine ⟨c₂, _, .seq e₁ e₂, by_grind, fun u hu' => ?_, ?_⟩
    · rcases List.mem_cons.1 hu' with rfl | hu'
      · refine b₁.of_eq (f₂.1 _ ?_)
        simp only [Bouts, List.contains_eq_mem, decide_eq_false_iff_not]; exact hd
      · have := b₂ u hu'
        obtain ⟨a1', a2', a3', a4'⟩ := hin u by_omega
        simp only [cmpOuts, List.map_cons, List.mem_cons, not_or] at a1' a2' a3' a4'
        rwa [f₁.1 _ (by simp [Bone, a1'.1]), f₁.1 _ (by simp [Bone, a2'.1]),
          f₁.1 _ (by simp [Bone, a3'.1]), f₁.1 _ (by simp [Bone, a4'.1])] at this
    · refine ⟨fun r hr => ?_, fun r hr => ?_, f₂.2.2.1.trans f₁.2.2.1,
        f₂.2.2.2.1.trans f₁.2.2.2.1, f₂.2.2.2.2.trans f₁.2.2.2.2⟩
      · simp only [Bouts, List.contains_eq_mem, decide_eq_false_iff_not] at hr
        grind
      · simp only [Bouts, List.contains_eq_mem, decide_eq_false_iff_not, cmpOuts,
          List.map_cons, List.mem_cons, not_or] at hr
        have g2 : ztsap := by
          zuggt
        zqblj
        rw [f₂.2.1 r g2, f₁.2.1 r g1]
end
end ShotList
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbiu" : tactic => `(tactic| exact ⟨gR' _ by_omega by_omega, gR' _ by_omega by_omega⟩)
local macro "zqbiv" : tactic => `(tactic| exact ⟨c, _, ex, by_omega, by_grind, exec_frameB ex wk⟩)
local macro "zqbiw" : tactic => `(tactic| exact ⟨c, _, ex, by_omega, by_simp_all, exec_frameB ex wk⟩)
set_option hygiene true

/-!
# Shooting at a list of arcs with holes, part 4: the cutting block

`cutB R ℓ`: the eight key comparisons (`kltSeq`), the correction of `a < b` by `offCmp` for two
interior positions of one edge (`offB`), the six tests of `cutK` (compiled formulas, `formB`)
and the selection (`selB`).  `cutB_exec`: the pieces of the arc of level `ℓ` outside its hole
(`cut1`), or the arc itself when the hole is absent, in the registers of the next level.
-/
namespace Chazelle.Core
namespace ShotList
open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
@[expose] public section
theorem normPos_vtx (M : Model) (Q : Polygon) (n x : ℕ) : NormPos M Q n ztbrb := by
  refine ⟨⟨?_, ?_, by_simp⟩, Or.inl rfl⟩ <;> simp [Model.param]
theorem key_vtx (M : Model) (Q : Polygon) (x : ℕ) : M.key Q ztbrb = x := by
  zugga

/-- **Lexicographic comparison of normalised positions** (not both inside one edge). -/
theorem lexLt_iff_key {M : Model} {Q : Polygon} {n : ℕ} {u v : WPos} (hu : NormPos M Q n u)
    (hv : NormPos M Q n v) (hne : ¬ (u.edge = v.edge ∧ 0 < u.hgt ∧ 0 < v.hgt)) :
    LexLt u.edge (ibv u.hgt) v.edge (ibv v.hgt) ↔ M.key Q u < M.key Q v := by
  rw [key_lt_iff hu hv hne]; rfl

/-- The test `sideInArc` as a formula of three comparison bits. -/
def siaF (uw uk kw : ℕ) : BF :=
  .or (.and (.and ztuvz ztuvy) ztuvx) (.and (.not ztuvz) (.or ztuvy ztuvx))
theorem siaF_size (uw uk kw : ℕ) : (siaF uw uk kw).size = 12 := rfl

/-- The test `x = a` from the two comparison bits. -/
def eqF (xa ax : ℕ) : BF := .and (.not (.var xa)) (.not (.var ax))
theorem eqF_size (xa ax : ℕ) : (eqF xa ax).size = 5 := rfl
variable {c : Config} {P : Polygon} {W : ℕ} {R ℓ : ℕ}
theorem siaF_eval {uw uk kw : ℕ} {u w k : ℝ} (h1 : BitIs c uw ztoiz)
    (h2 : BitIs c uk ztucl) (h3 : BitIs c kw zttqe) :
    (siaF uw uk kw).eval ztzfj = true ↔ sideInArc u w k := by
  zudqq

  obtain ⟨-, i3⟩ := h3
  unfold siaF sideInArc
  simp only [BF.eval, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, i1, i2, i3]
  grind
theorem eqF_eval {xa ax : ℕ} {x a : ℝ} (h1 : BitIs c xa ztudx)
    (h2 : BitIs c ax zttep) :
    (eqF xa ax).eval ztzfj = true ↔ x = a := by
  zudqq

  unfold eqF
  simp only [BF.eval, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, i1, i2]
  grind

/-! ## The blocks -/

/-- The arc registers of level `ℓ`: `rL R ℓ … rL R ℓ + 3`. -/
def rL (R ℓ : ℕ) : ℕ := R + 40 + 10 * ℓ

/-- The eight comparisons of level `ℓ`: `a < b`, `a < x`, `x < a`, `a < y`, `y < b`, `x < b`,
`x < y`, `y < x` into `R + 100 … R + 107`. -/
def cmpList (R ℓ : ℕ) : List Cmp :=
  let L := rL R ℓ
  let hx := R + 10 + 2 * ℓ
  let hy := R + 11 + 2 * ℓ
  let z := R + 30
  [(L, L + 1, L + 2, L + 3, R + 100), (L, L + 1, hx, z, R + 101), (hx, z, L, L + 1, R + 102),
    (L, L + 1, hy, z, R + 103), (hy, z, L + 2, L + 3, R + 104), (hx, z, L + 2, L + 3, R + 105),
    (hx, z, hy, z, R + 106), (hy, z, hx, z, R + 107)]

/-- `a < b` by `offCmp` when `a`, `b` are interior positions of one edge. -/
def offCall (R ℓ : ℕ) : Stmt :=
  let L := rL R ℓ
  .seq (block [.copyN 50200 ztvh, .copyN 50201 L, .copyN 50202 ztgt, .copyN 50203 zttz,
      .copyN 50204 ztclr, .copyN 50205 ztgx])
    (.seq offCmp (block [.copyN ztbtq 50210]))

/-- The correction of the bit `a < b`. -/
def offB (R ℓ : ℕ) : Stmt :=
  let L := rL R ℓ
  .ifLtN L zttz .skip (.ifLtN zttz L .skip
    (.ifLtN ztgx ztgt (.ifLtN ztgx ztclr zttuu .skip) .skip))

/-- The six tests of `cutK` into `R + 120`, `R + 140`, …, `R + 220`. -/
def formB (R : ℕ) : Stmt :=
  .seq ((siaF ztnoe ztnoc ztnod).compile ztjlp)
    (.seq ((siaF ztbtq ztnod ztjln).compile ztjlq)
      (.seq ((siaF ztjln zttbn ztjlo).compile ztjlr)
        (.seq ((siaF ztbtq ztnob ztjlo).compile ztjls)
          (.seq ((siaF ztjlo ztnoe ztjln).compile ztjlt)
            ((eqF ztnoc ztnob).compile ztjlu)))))

/-- **The cutting block of level `ℓ`.** -/
def cutB (R ℓ : ℕ) : Stmt :=
  let L := rL R ℓ
  .seq ztzws (.seq ztkbo (.seq ztqmz
    (selB L ztqv ztqw ztgx (L + 10) ztsyw (L + 8) ztkt
      ztnx ztjlp ztjlq ztjlr ztjls ztjlt ztjlu)))

/-! ## Execution: the correction of `a < b` -/

/-- **The caller's register block** `R … R + 299` lies in one band, which is neither band `0`
(the allocator) nor a band of the kernels or the oracles (`oracleBands`). -/
def RegsOK (R : ℕ) : Prop :=
  R % 10000 + 300 ≤ 10000 ∧ R / 10000 ≠ 0 ∧ R / 10000 ≠ 1 ∧ R / 10000 ≠ 3 ∧ R / 10000 ≠ 4 ∧
    R / 10000 ≠ 5 ∧ R / 10000 ≠ 6 ∧ R / 10000 ≠ 12 ∧ R / 10000 ≠ 13 ∧ R / 10000 ≠ 14 ∧
    R / 10000 ≠ 15
theorem bprim_R {R : ℕ} (hR : RegsOK R) {i : ℕ} (hi : i < 300) : Bprim ztly = false := by
  zuhaf
  zudlb
  omega

/-- The registers written by `offB`. -/
def Boff (R : ℕ) (r : ℕ) : Bool := r == R + 100 || Bprim r || decide ztqt
theorem wr_offCmp' (R : ℕ) : wr ztmak offCmp = true :=
  wr_mono wr_offCmp (fun r hr => by simp [Boff, hr])
theorem wr_offCall (R ℓ : ℕ) : wr ztmak zttuu = true := by
  have h := wr_offCmp' R
  simp [offCall, wr, block, wrOK, Boff, h]
theorem wr_offB (R ℓ : ℕ) : wr ztmak ztkbo = true := by
  have h := wr_offCall R ℓ
  simp [offB, wr, h]

/-- Loading the inputs of `offCmp`. -/
theorem offLoad_exec (c : Config) (hw : WordsBounded W c) (cd L z : ℕ)
    (hLr : L + 4 ≤ 50200 ∨ 50206 ≤ L)
    (hz : z < 50200 ∨ 50206 ≤ z) :
    ∃ c₁ k₁, Exec P W
      (block [.copyN 50200 cd, .copyN 50201 L, .copyN 50202 ztgt, .copyN 50203 zttz,
        .copyN 50204 ztclr, .copyN 50205 z]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg 50200 = c.nreg cd ∧ c₁.nreg 50201 = c.nreg L ∧
      c₁.nreg 50202 = c.nreg ztgt ∧ c₁.nreg 50203 = c.nreg zttz ∧
      c₁.nreg 50204 = c.nreg ztclr ∧ c₁.nreg 50205 = c.nreg z ∧
      (∀ r, ¬ (50200 ≤ r ∧ r < 50206) → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.nreg ALLOC = c.nreg ALLOC := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, ?_⟩ <;> (try unfold ALLOC) <;> rsimp

/-- **The correction of `a < b`**: afterwards the bit `R + 100` is the key order of `a`, `b`. -/
theorem offB_exec (hR : RegsOK R) (hℓ : ℓ ≤ 2) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W) {H : Host} {C : Chain}
    (hwf : ChainWF P ztm c.nmem ztwup)
    (hC : ChainDescAt c.nmem ztwup zta H C) (hm : 2 * C.m + 7 ≤ W)
    (hroom : c.nreg ALLOC + 11000 ≤ W) (hz : c.nreg ztgx = 0)
    (ha : NormPos ztc zta P.n ztut)
    (hb : NormPos ztc zta P.n ztre)
    (hae : c.nreg ztbha < (chainModel C).W.n) (hbe : c.nreg ztcaw < (chainModel C).W.n)
    (hbit : BitIs c ztbtq (LexLt ztbagj ztzgc
      ztbagk ztzgd)) :
    ∃ c' k, Exec P W ztkbo c c' k ∧ k ≤ 11100 ∧
      BitIs c' ztbtq ((chainModel C).key zta ztut <
        (chainModel C).key zta ztre) ∧
      FrameB ztmak c c' := by
  zuckh
  zubio
  zuftp
  have hne_of : ¬ ztxku →
      BitIs c ztbtq (M.key zta ztzxv <
        M.key zta ztzxu) := fun hne => by
    have := lexLt_iff_key ha hb hne
    zuhpv

  have wk := wr_offB R ℓ
  unfold offB
  zubi
  zuhsl
  · have ex : ztdjq := .ifLtN_true h1 ztjd
    zqbiv
  zuhsr
  · have ex : ztdjq := .ifLtN_false h1 ztxdj
    zqbiv
  zuhbl

  · have ex : ztdjq :=
      .ifLtN_false h1 ztynx
    zqbiw
  zuhbm

  · have ex : ztdjq :=
      .ifLtN_false h1 ztxuc
    zqbiw
  -- two interior positions of one edge: `offCmp`
  zubdp
  obtain ⟨c₁, k₁, e₁, hk₁, p1, p2, p3, p4, p5, p6, pr, pm, pal⟩ :=
    offLoad_exec (P := P) c hw ztvh L ztgx by_omega by_omega
  zvncr at p6
  zud
  have hn0 : ztbiy := by
    omega
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, -⟩ := offCmp_meets P W c₁ w₁
    ⟨hG, hHW, by_grind, H, C, by_grind,
      by grind, by_grind, by_grind,
      by rw [p2, p3]; exact ha.1, by rw [p4, p5]; exact hb.1,
      fun h => by_omega, fun h => by_omega, hm⟩
    by_grind
  replace hk₂ : k₂ ≤ 11000 := hk₂
  obtain ⟨o1, -⟩ := post₂ H C by_grind
  have F₂ := exec_frameB e₂ wr_offCmp
  have e₃ := Exec.copyN (P := P) e₂.wb_right ztbtq 50210
  have ex : Exec P W ztkbo c _ _ :=
    .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true h3 (.ifLtN_true h4
      (.seq e₁ ztkpr))))
  refine ⟨_, _, ex, by_omega, ztcp, exec_frameB ex wk⟩
  · zumwv; exact o1.1
  · zufb
    rw [o1.2, p2, p3, p4, p5, p6]
    have kx := ha.1.1
    have ky := hb.1.1
    simp only [posR] at kx ky ⊢
    rw [Nat.cast_zero]
    exact (key_lt_iff_off kx ky).symm

/-! ## Execution: the six tests -/
theorem bitIs_toNat {d : ℕ} {b : Bool} {p : Prop} (hv : c.nreg d = b.toNat)
    (hb : b = true ↔ p) : BitIs c d p := by
  zuevy
  simp_all

/-- A compiled `sideInArc` test. -/
theorem siaF_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    {uw uk kw d : ℕ} (h1 : uw < d) (h2 : uk < d) (h3 : kw < d) {u w k : ℝ}
    (b1 : BitIs c uw ztoiz) (b2 : BitIs c uk ztucl) (b3 : BitIs c kw zttqe) :
    ∃ c' k', Exec P W ((siaF uw uk kw).compile d) c c' k' ∧ k' ≤ 48 ∧
      BitIs c' d (sideInArc u w k) ∧ FrameB ((siaF uw uk kw).wset d) c c' := by
  obtain ⟨c', k', ex, hk, hv, hf⟩ := BF.compile_exec (P := P) hW (siaF uw uk kw) d c hw
    ⟨⟨⟨⟨h1, b1.1⟩, ⟨h2, b2.1⟩⟩, ⟨h3, b3.1⟩⟩, ⟨⟨h1, b1.1⟩, ⟨⟨h2, b2.1⟩, ⟨h3, b3.1⟩⟩⟩⟩
  exact ⟨c', k', ex, by_tauto, bitIs_toNat hv (siaF_eval b1 b2 b3), hf⟩

/-- The compiled test `x = a`. -/
theorem eqF_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    {xa ax d : ℕ} (h1 : xa < d) (h2 : ax < d) {x a : ℝ} (b1 : BitIs c xa ztudx)
    (b2 : BitIs c ax zttep) :
    ∃ c' k', Exec P W ((eqF xa ax).compile d) c c' k' ∧ k' ≤ 20 ∧ BitIs c' d (x = a) ∧
      FrameB ((eqF xa ax).wset d) c c' := by
  obtain ⟨c', k', ex, hk, hv, hf⟩ := BF.compile_exec (P := P) hW (eqF xa ax) d c hw
    ⟨⟨h1, b1.1⟩, ⟨h2, b2.1⟩⟩
  exact ⟨c', k', ex, by_tauto, bitIs_toNat hv (eqF_eval b1 b2), hf⟩

/-- The registers written by `formB`. -/
def Bform (R : ℕ) (r : ℕ) : Bool := decide (R + 120 ≤ r ∧ r < R + 240)
theorem bitIs_keep {c c' : Config} {B : ℕ → Bool} {r : ℕ} {p : Prop} (h : BitIs c r p)
    (hf : FrameB B c c') (hr : B r = false) : BitIs c' r p := h.of_eq ztoaq
theorem wset_lt {f : BF} {d r : ℕ} (h : r < d) : f.wset d r = false := by
  simp only [BF.wset, decide_eq_false_iff_not]; omega

/-- **The six tests of `cutK`** from the eight comparison bits. -/
theorem formB_exec (R : ℕ) (c : Config) (hw : WordsBounded W c)
    (hW : 2 ≤ W) {ka kb kx ky : ℝ}
    (bab : BitIs c ztbtq (ka < kb)) (bax : BitIs c ztnob (ka < kx))
    (bxa : BitIs c ztnoc (kx < ka)) (bay : BitIs c ztnod (ka < ky))
    (byb : BitIs c ztjln (ky < kb)) (bxb : BitIs c ztjlo (kx < kb))
    (bxy : BitIs c ztnoe (kx < ky)) (byx : BitIs c zttbn (ky < kx)) :
    ∃ c' k, Exec P W ztqmz c c' k ∧ k ≤ 300 ∧
      BitIs c' ztjlp (sideInArc kx ky ka) ∧ BitIs c' ztjlq (sideInArc ka kb ky) ∧
      BitIs c' ztjlr (sideInArc ky kb kx) ∧ BitIs c' ztjls (sideInArc ka kb kx) ∧
      BitIs c' ztjlt (sideInArc kx kb ky) ∧ BitIs c' ztjlu (kx = ka) ∧
      FrameB ztuws c c' := by
  have fr : ∀ {B : ℕ → Bool} {cc cc' : Config}, FrameB B cc cc' →
      (∀ r, B r = true → R + 120 ≤ r ∧ r < R + 240) → FrameB ztuws cc cc' := fun h h1 =>
    frameB_mono h (fun r hr => by
      have := h1 r hr; simp only [Bform, decide_eq_true_eq]; omega)
  have kp : ∀ {B : ℕ → Bool} {cc cc' : Config} {r : ℕ} {p : Prop}, BitIs cc r p →
      FrameB B cc cc' → B r = false → BitIs cc' r p := bitIs_keep
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := siaF_exec (P := P) c hw hW (d := R + 120)
    by_omega by_omega by_omega bxy bxa bay
  have k1 := fun {r : ℕ} {p : Prop} (h : BitIs c r p) (hr : r < R + 120) =>
    kp h f₁ ztibq
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := siaF_exec (P := P) c₁ e₁.wb_right hW (d := R + 140)
    by_omega by_omega by_omega zttqh (k1 bay by_omega) ztocc
  have k2 := fun {r : ℕ} {p : Prop} (h : BitIs c₁ r p) (hr : r < R + 140) =>
    kp h f₂ ztibq
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃⟩ := siaF_exec (P := P) c₂ e₂.wb_right hW (d := R + 160)
    by_omega by_omega by_omega ztzwm
    (k2 (k1 byx by_omega) by_omega) zthih
  have k3 := fun {r : ℕ} {p : Prop} (h : BitIs c₂ r p) (hr : r < R + 160) =>
    kp h f₃ ztibq
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ := siaF_exec (P := P) c₃ e₃.wb_right hW (d := R + 180)
    by_omega by_omega by_omega (k3 (k2 zttqh by_omega) by_omega)
    ztjzh
    ztzwn
  have k4 := fun {r : ℕ} {p : Prop} (h : BitIs c₃ r p) (hr : r < R + 180) =>
    kp h f₄ ztibq
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, f₅⟩ := siaF_exec (P := P) c₄ e₄.wb_right hW (d := R + 200)
    by_omega by_omega by_omega
    (k4 ztzwn by_omega)
    (k4 (k3 (k2 (k1 bxy by_omega) by_omega) by_omega) by_omega)
    (k4 (k3 ztzwm by_omega) by_omega)
  have k5 := fun {r : ℕ} {p : Prop} (h : BitIs c₄ r p) (hr : r < R + 200) =>
    kp h f₅ ztibq
  obtain ⟨c₆, k₆, e₆, hk₆, v₆, f₆⟩ := eqF_exec (P := P) c₅ e₅.wb_right hW (d := R + 220)
    by_omega by_omega
    (k5 (k4 (k3 (k2 (k1 bxa by_omega) by_omega) by_omega) by_omega) by_omega)
    (k5 (k4 ztjzh by_omega) by_omega)
  have k6 := fun {r : ℕ} {p : Prop} (h : BitIs c₅ r p) (hr : r < R + 220) =>
    kp h f₆ ztibq
  have fz : ∀ {f : BF} {d : ℕ} {cc cc' : Config}, FrameB ztqmw cc cc' → R + 120 ≤ d →
      d + f.size < R + 240 → FrameB _ cc cc' := fun h h1 h2 => fr h (fun r hr => by
    simp only [SweepPrim.BF.wset, decide_eq_true_eq] at hr; omega)
  refine ⟨c₆, _, .seq e₁ ztfv, by_omega,
    k6 by_grind by_omega,
    by grind,
    by grind, by_grind,
    by grind, v₆, ?_⟩
  exact (fz f₁ by_omega ztdgv).trans
    ((fz f₂ by_omega ztdgv).trans
    ((fz f₃ by_omega ztdgv).trans
    ((fz f₄ by_omega ztdgv).trans
    ((fz f₅ by_omega ztdgv).trans
    (fz f₆ by_omega (by rw [eqF_size]; omega))))))

/-! ## The cutting block -/

/-- The registers written by `cutB`. -/
def Bcut (R ℓ : ℕ) (r : ℕ) : Bool :=
  Bouts ztdhc r || Boff R r || Bform R r || decide zthkc

/-- The pieces of the arc of level `ℓ`: `cut1` if the hole is present, else the arc. -/
noncomputable def levPieces (M : Model) (Q : Polygon) (hp : Prop) [Decidable hp] (a b : WPos)
    (x y : ℕ) : List ztqx :=
  if hp then cut1 ztbmb a b ztbrb ztcpb else [ztvk]
theorem cmpList_ok (hℓ : ℓ ≤ 2) : CmpOK ztgx ztdhc := by
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · tauto
  · simp [cmpOuts, cmpList]
  · simp only [cmpList, rL, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [cmpOuts, cmpList, rL, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      omega

/-- **The cutting block of level `ℓ`**: the pieces `levPieces` in the registers of the next
level (`rL R ℓ + 10 …`, `rL R ℓ + 4 …`, their number in `rL R ℓ + 8`). -/
theorem cutB_exec (hR : RegsOK R) (hℓ : ℓ ≤ 2) (c : Config)
    (hw : WordsBounded W c) (hW : 2 ≤ W) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W)
    {H : Host} {C : Chain} (hwf : ChainWF P ztm c.nmem ztwup)
    (hC : ChainDescAt c.nmem ztwup zta H C) (hm : 2 * C.m + 7 ≤ W)
    (hroom : c.nreg ALLOC + 11000 ≤ W) (hz : c.nreg ztgx = 0)
    (ha : NormPos ztc zta P.n ztut)
    (hb : NormPos ztc zta P.n ztre)
    (hae : c.nreg ztbha < (chainModel C).W.n)
    (hbe : c.nreg ztcaw < (chainModel C).W.n) :
    ∃ c' k, Exec P W ztnxh c c' k ∧ k ≤ 11500 ∧
      PiecesAt c' ztkds ztkdt ztsj
        (levPieces ztc zta ztwrw
          ztut ztre
          ztxwe ztxwf) ∧
      FrameB ztgzz c c' := by
  zuckh
  zuftp
  zubio
  zubep
  zubve

  zudog

  -- the comparisons
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := kltSeq_exec (P := P) by_omega ztgx ztdhc c hw
    hz ztvll
  have in₁ : ztfdv := fun r hr =>
    f₁.1 r (by
      simp only [Bouts, cmpOuts, cmpList, List.map_cons, List.map_nil, List.contains_eq_mem,
        List.mem_cons, List.not_mem_nil, or_false, decide_eq_false_iff_not, not_or]
      omega)
  zukij
  simp only [cmpList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mem
  zubfe

  -- the key order
  have vtx : ∀ (u v : WPos), NormPos M Q P.n u → NormPos M Q P.n v → ztojc →
      ztihi :=
    fun u v hu hv h0 => lexLt_iff_key hu hv by_omega
  have kax : ztcpd :=
    ⟨bax.1, bax.2.trans ztyxd⟩
  have kxa : ztcpd :=
    ⟨bxa.1, bxa.2.trans ztywz⟩
  have kay : ztcpd :=
    ⟨bay.1, bay.2.trans ztyxe⟩
  have kyb : ztcpd :=
    ⟨byb.1, byb.2.trans ztyxc⟩
  have kxb : ztcpd :=
    ⟨bxb.1, bxb.2.trans ztyxa⟩
  have kxy : ztcpd :=
    ⟨bxy.1, bxy.2.trans ztywy⟩
  have kyx : ztcpd :=
    ⟨byx.1, byx.2.trans ztyxb⟩
  -- the correction of `a < b`
  have g34 := in₁ ztvh by_omega
  have g30 := in₁ ztgx by_omega
  zuya

  zumbz
  have pa : ztzqp := by
    zughv
  have pb : ztzqo := by
    zughw
  obtain ⟨c₂, k₂, e₂, hk₂, kab, f₂⟩ := offB_exec (P := P) hR hℓ c₁ e₁.wb_right hG hHW
    (H := H) (C := C) by_grind by_grind hm
    by_omega by_omega by_grind by_grind
    by_grind by_grind
    by_grind
  zuimb
  have in₂ := f₂.1
  have o₂ : ∀ r, ztjlm → Boff R r = false := fun r hr => by
    have := bprim_R hR (i := r - R) by_omega
    rw [show R + zthjq = r by omega] at this
    zuhaf
    simp only [Boff, this, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not]
    omega
  have ks := fun {r : ℕ} {p : Prop} (h : BitIs c₁ r p) (hr : R + 100 < r ∧ r < R + 300) =>
    bitIs_keep h f₂ by_grind
  -- the six tests
  obtain ⟨c₃, k₃, e₃, hk₃, t1, t2, t3, t4, t5, t6, f₃⟩ := formB_exec (P := P) R c₂ e₂.wb_right
    hW kab zttrc zttre zttrd zttrh
    zttrf zttrg zttri
  -- registers of `c` read by the selection
  have gsel : ∀ r, (r < R + 100 ∧ bandOf r = bandOf r) → ¬ ztqt →
      Bprim r = false → c₃.nreg r = c.nreg r := fun r hr h5 hp => by
    rw [f₃.1 r ztkuv,
      f₂.1 r (by simp only [Boff, hp, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
        decide_eq_false_iff_not]; omega), in₁ r (Or.inl hr.1)]
  have gR : ztkof := fun i hi => by
    have hp := bprim_R hR (i := i) by_omega
    zuhaf
    exact gsel _ by_omega by_omega hp
  have gR' := fun r h1 h2 => by
    have := gR zthjq by_omega
    zufad
  have z3 : ztbacu := by rw [gR 30 by_omega, hz]
  obtain ⟨c₄, k₄, e₄, hk₄, pc₄, r₄, m₄, rr₄, rm₄, o₄⟩ := selB_exec (P := P) c₃ e₃.wb_right hW
    (L := L) (hx := R + 10 + 2 * ℓ) (hy := R + 11 + 2 * ℓ) (z := R + 30) (N := L + 10)
    (S := L + 4) (Cn := L + 8) (hpA := R + 30 + ℓ) (hpB := R + 9) (c1 := R + 120)
    (c2 := R + 140) (c3 := R + 160) (c4 := R + 180) (c5 := R + 200) (c6 := R + 220)
    ztgqz by_omega by_omega
    by_omega z3 t1.1 t2.1 t3.1 t4.1 t5.1 t6.1
  have ex : Exec P W ztnxh c c₄ _ := .seq e₁ ztcb
  refine ⟨c₄, _, ex, by simp only [cmpList, List.length_cons, List.length_nil] at hk₁; omega,
    ?_, ?_⟩
  · -- the pieces
    have hsel : selPos c₃ L ztqv ztqw ztgx =
        fun tl => tl.map fun e => ztxqp := by
      funext tl
      unfold selPos
      zucr
      funext e
      have ev : ∀ u : End, posR c₃ ztyvf =
          End.val a b ztbrb ztcpb u := by
        zulnl
        cases u <;> zunig
        · zqbiu
        · zqbiu
        · zumab
        · zumab
      zukrg
    zukwe
    have hp3 : ztwur ↔ ztwrw := by
      zufmx
    unfold levPieces
    zudxa
    · have hd : ztbasb := by
        grind
      zudue
      zuhms

      rw [cutK_eq_selT _ _ _ _ a b ztbrb
        ⟨y, 0⟩ (c1 := decide ztbrh) (c2 := decide ztbrh)
        (c3 := decide ztbrh) (c4 := decide ztbrh)
        (c5 := decide ztbrh) (c6 := decide ztbrh)
        ztmcz ztmda
        ztmdb ztmdc
        ztmdd ztmde]
      omega
    · have hd : ztbasa := by
        grind
      zudue
      zuhmr

  · -- the frame
    have f₄ : ztbabu :=
      ⟨fun r hr => r₄ r by_grind
        by_grind
        by_grind,
       by grind, m₄, rm₄, o₄⟩
    have c1 : FrameB ztgzz c c₁ := frameB_mono f₁ ztesq
    have c2 : FrameB ztgzz c₁ c₂ := frameB_mono f₂ ztesq
    have c3 : FrameB ztgzz c₂ c₃ := frameB_mono f₃ ztesq
    have c4 : FrameB ztgzz c₃ c₄ := frameB_mono f₄ (fun r hr => by
      zvmwo at hr; simp [Bcut, ← hL, hr])
    exact c1.trans ztqjk
end
end ShotList
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbfq" : tactic => `(tactic| (have h := hR; unfold RegsOK at h))
local macro "zqbfr" : tactic => `(tactic| obtain ⟨c', k, ex, hk, hbest', fr⟩ := accept c₂ w₂ f₂' hr₂ ztgel)
local macro "zqbfs" : tactic => `(tactic| (rw [k2 _ by_omega by_omega, k2 _ by_omega by_omega]; omega))
local macro "zqbft" : tactic => `(tactic| have ord := ray_lt_iff (p := z) (t := t) (t' := tb) hσ1)
set_option hygiene true

/-!
# Shooting at a list of arcs with holes, part 5: one shot and the running minimum

The **leaf** of the cutting recursion shoots at one piece (level-3 registers `R + 70 … R + 73`)
with the ray shooter `sh` (`ShooterOK`) and keeps the first hit over the pieces shot so far:
flag `R + 20`, position `R + 21`, `R + 22`, and the abscissa record (`absKey`) of its point in
`R + 24 … R + 27`.  Two hits on one ray are compared by abscissa (`absCmp`), in the direction of
the ray (`R + 35`: the bit `σ = 1`).

* `firstHit_union_*`, `noHit_union`: the first hit on a union;
* `BestOK`: the running minimum describes the first hit on the union `S` of the pieces shot;
* `leaf_exec`: one shot extends `S` by the piece.
-/
namespace Chazelle.Core
namespace ShotList
open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
@[expose] public section
variable {A B : Set Point} {p : Point} {σ t : ℝ} {P : Polygon} {c c' : Config} {r r' : ℕ} {W : ℕ} {R : ℕ} {v : ℕ}
theorem noHit_union {σ : ℝ} (hA : NoHit A p σ) (hB : NoHit B p σ) :
    NoHit ztbgp p σ := fun t ht h => h.elim (hA t ht) (hB t ht)
theorem firstHit_union_left (hA : FirstHit A p σ t)
    (hB : NoHit B p σ) : FirstHit ztbgp p σ t :=
  ⟨hA.1, Or.inl hA.2.1, fun t' h1 h2 h => h.elim (hA.2.2 t' h1 h2) (hB t' h1)⟩
theorem firstHit_union_right (hA : NoHit A p σ)
    (hB : FirstHit B p σ t) : FirstHit ztbgp p σ t :=
  ⟨hB.1, Or.inr hB.2.1, fun t' h1 h2 h => h.elim (hA t' h1) (hB.2.2 t' h1 h2)⟩
theorem firstHit_union_le {σ t t' : ℝ} (hA : FirstHit A p σ t)
    (hB : FirstHit B p σ t') (h : t ≤ t') : FirstHit ztbgp p σ t :=
  ⟨hA.1, Or.inl hA.2.1, fun s h1 h2 hs => hs.elim (hA.2.2 s h1 h2)
    (hB.2.2 s h1 by_grind)⟩
theorem firstHit_union_le' {σ t t' : ℝ} (hA : FirstHit A p σ t)
    (hB : FirstHit B p σ t') (h : t' ≤ t) : FirstHit ztbgp p σ t' := by
  have := firstHit_union_le hB hA h
  grind

/-- On a ray, the parameters compare like the abscissae (in the direction of the ray). -/
theorem ray_lt_iff {σ t t' : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    t < t' ↔ (if σ = 1 then (rayPt p σ t).1 < (rayPt p σ t').1
      else (rayPt p σ t').1 < (rayPt p σ t).1) := by
  zur
  · simp
  · simp only [rayPt_fst, show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]; grind

/-! ## Copying records -/

/-- An abscissa record survives a copy of its four words. -/
theorem absRec_copy {x R : ℝ} (h : AbsRec P c r x R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) (h3 : c'.nreg ztkdl = c.nreg ztkdd) :
    AbsRec P c' r' x R := by
  zufk

  · simp_all
  · simp_all
  · zuia

/-- An origin survives a copy of its three words. -/
theorem originIn_copy {o : Origin} (h : OriginIn c r o)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) : OriginIn c' r' o := by
  cases o with
  | sym p => exact NFLoc.symPtIn_copy h h0 h1 h2
  | walk x => exact ⟨h0.trans h.1, h1.trans h.2.1, h2.trans h.2.2⟩

/-! ## The shooter with an edge bound on its hits -/

/-- **`ShooterOK` with the edge of the hit position in range** (spec amendments G9, G10: `ShooterOK`
now states the bound itself, and `shooterOKE_of` gives this contract from it). -/
def ShooterOKE (sh : Stmt) (B : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) : Prop :=
  Meets sh B
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c.nmem ztefx ztm ∧
      rd c bShoot 9 ≤ X.cap P c.nmem ztefx ∧
      ModelDescWF P ztm c.nmem ztbrn ∧
      (c.nmem ztbrn = 0 → ∀ H C, ChainDescAt c.nmem ztfih zta H C →
        HostRegular (Qof P).n H) ∧
      ∃ M, ModelDescAt c.nmem ztbrn zta M ∧ Ok P M ∧
        ProperPos M zta P.n ztnp ∧
        ProperPos M zta P.n ztnq ∧
        rd c bShoot 1 < M.W.n ∧ rd c bShoot 3 < M.W.n ∧
        ztwwl ∧
        ztwwm ∧
        M.arcWt ztwwa
          ztwwb ≤ rd c bShoot 9 ∧
        ∃ o : Origin, o.Lt P.n M ∧ OriginIn c ztbpu o ∧
          (ztbnv ∨ (M.InnerPt ztwle ∧
            ∀ x, o = .walk x → ProperPos M zta P.n x)) ∧
          o.eval M zta ∉ M.arcSet ztwwa
            ztwwb)
    (fun P c c' => ∀ M (o : Origin), ModelDescAt c.nmem ztbrn zta M →
      OriginIn c ztbpu o →
        let A := M.arcSet ztwwa
          ztwwb
        (rd c' bShoot 10 = 1 → ∃ t, FirstHit A ztwle ztbqc t ∧
          ProperPos M zta P.n ztdqv ∧
          rd c' bShoot 11 < M.W.n ∧
          M.pos zta ztdqv =
            Visibility.rayPt ztwle ztbqc t) ∧
        ztbamj)
    ztyvx

/-- **`ShooterOK` gives `ShooterOKE`** (the two contracts coincide since amendment G9). -/
theorem shooterOKE_of {sh : Stmt} {B : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (h : ShooterOK sh B F X Ok) : ShooterOKE sh B F X Ok := h

/-! ## The running minimum -/

/-- **The running minimum** at `R` describes the first hit of the ray from `z` in direction `σ`
on `S` (in the chain model `M` of `C`). -/
def BestOK (P : Polygon) (C : Chain) (R : ℕ) (c : Config) (S : Set Point) (z : Point) (σ : ℝ) :
    Prop :=
  c.nreg ztpa ≤ 1 ∧
    (c.nreg ztpa = 1 → ∃ t, FirstHit S z σ t ∧
      ProperPos ztc zta P.n ztuw ∧
      c.nreg ztbjl < (chainModel C).W.n ∧
      (chainModel C).pos zta ztuw = rayPt z σ t ∧
      AbsRec P c zthce (rayPt z σ t).1 C.radius) ∧
    ztyek

/-! ## The programs -/

/-- The shooter's inputs: model descriptor, the piece, the origin, direction, weight bound and
context. -/
def setList (R : ℕ) : List ztw := [(140000, R), (140001, R + 70), (140002, R + 71),
  (140003, R + 72), (140004, R + 73), (140005, R + 3), (140006, R + 4), (140007, R + 5),
  (140008, R + 6), (140009, R + 7), (140013, R + 8)]

/-- Setting up the shooter. -/
def leafSet (R : ℕ) : Stmt := block (copies ztwdq)

/-- The candidate's position and the inputs of `absKey`. -/
def keyList (R : ℕ) : List ztw := [ztqbw, ztqbx, (50200, R + 34),
  (50201, 140011), (50202, 140012)]

/-- The candidate's abscissa record. -/
def recList (R : ℕ) : List ztw :=
  [(R + 240, 50210), (R + 241, 50211), (R + 242, 50212), (R + 243, 50213)]

/-- The candidate: its position into `R + 244`, `R + 245`, its abscissa record into
`R + 240 … R + 243`. -/
def leafKey (R : ℕ) : Stmt :=
  .seq (block (copies ztvxq)) (.seq absKey (block (copies ztwck)))

/-- The copies accepting the candidate. -/
def accList (R : ℕ) : List ztw := [zthcc, zthcd, (R + 24, R + 240),
  (R + 25, R + 241), (R + 26, R + 242), (R + 27, R + 243)]

/-- Accept the candidate. -/
def leafAcc (R : ℕ) : Stmt := .seq ztyva (block (copies ztvei))

/-- Two abscissa records into the inputs of `absCmp`. -/
def cmpLoad (R u v : ℕ) : List ztw := [(50201, R + u), (50202, R + u + 1),
  (50203, R + u + 2), (50204, R + u + 3), (50205, R + v), (50206, R + v + 1),
  (50207, R + v + 2), (50208, R + v + 3)]

/-- The bits `cand < best` (`R + 246`) and `best < cand` (`R + 247`) of the abscissae. -/
def leafCmp (R : ℕ) : Stmt :=
  .seq (block (copies (cmpLoad R 240 24))) (.seq absCmp (.seq (block [.copyN ztbtr 50210])
    (.seq (block (copies (cmpLoad R 24 240))) (.seq absCmp (block [.copyN ztces 50210])))))

/-- Accept if the candidate comes first along the ray. -/
def leafDec (R : ℕ) : Stmt :=
  .ifLtN ztgx ztbgt (.ifLtN ztgx ztbtr zthyp .skip)
    (.ifLtN ztgx ztces zthyp .skip)

/-- A hit: accept it if there is no minimum yet, else compare. -/
def leafHit (R : ℕ) : Stmt :=
  .seq ztvyc (.ifLtN ztpa zthl zthyp (.seq ztqsv (leafDec R)))

/-- **The leaf**: one shot at the piece of level `3`, and the running minimum. -/
def leaf (sh : Stmt) (R : ℕ) : Stmt :=
  .seq ztqsw (.seq sh (.ifLtN zthl 140010 .skip (.ifLtN 140010 zthl .skip
    ztvyb)))

/-! ## Execution of the blocks -/

/-- A block of copies, with the side conditions of `copies_exec` discharged by `simp`/`omega`. -/
theorem copies_run (l : List ztw) (c : Config) (hw : WordsBounded W c)
    (hd : ∀ p ∈ l, ∀ q ∈ l, p.1 ≠ q.2) (hnd : (l.map Prod.fst).Nodup) :
    ∃ c', Exec P W ztgfh c c' l.length ∧ ztfcu ∧
      FrameB ztloi c c' := by
  obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := copies_exec l c hw hd hnd
  refine ⟨c', e, h1, by_grind, by_grind, h4, h5, h6⟩

/-- **Setting up the shooter.** -/
theorem leafSet_exec (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) :
    ∃ c' k, Exec P W ztqsw c c' k ∧ k = 11 ∧ (∀ p ∈ setList R, c'.nreg p.1 = c.nreg p.2) ∧
      FrameB (fun r => ((setList R).map Prod.fst).contains r) c c' := by
  zqbfq
  obtain ⟨c', e, h1, h2⟩ := copies_run (P := P) ztwdq c hw (by
    simp only [setList, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega)
    (by simp [setList])
  exact ⟨c', _, e, rfl, h1, h2⟩

/-- A register of the caller's block is not written by a primitive. -/
theorem bprim_R' (hR : RegsOK R) {r : ℕ} (h1 : R ≤ r) (h2 : r < R + 300) :
    Bprim r = false := by
  have := bprim_R hR (i := r - R) by_omega
  simp_all

/-- The write set of `leafKey`. -/
def Bkey (R : ℕ) (r : ℕ) : Bool :=
  decide (R + 240 ≤ r ∧ r < R + 246) || Bprim r || decide ztqt

/-- **The abscissa record of the candidate.** -/
theorem leafKey_exec (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W) {H : Host} {C : Chain}
    (hwf : ChainWF P ztm c.nmem ztwup)
    (hC : ChainDescAt c.nmem ztwup zta H C)
    (hreg : ∀ H', HostAt c.nmem ztbasl H' → HostRegular P.n H')
    (he : c.nreg 140011 < (chainModel C).W.n)
    (hp : ProperPos ztc zta P.n ztdqm)
    (hy : |((chainModel C).pos zta ⟨c.nreg 140011, c.nreg 140012⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 16700 ≤ W) :
    ∃ c' k, Exec P W ztvyc c c' k ∧ k ≤ 16720 ∧ c'.nreg ztbme = c.nreg 140011 ∧
      c'.nreg ztbpp = c.nreg 140012 ∧
      AbsRec P c' ztnof ((chainModel C).pos zta ztdqm).1
        C.radius ∧ FrameB (Bkey R) c c' := by
  zqbfq
  obtain ⟨c₁, e₁, v₁, f₁⟩ := copies_run (P := P) ztvxq c hw (by
    simp only [keyList, List.mem_cons, List.not_mem_nil, or_false]
    grind)
    ztnux
  simp only [keyList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₁
  obtain ⟨v44, v45, v00, v01, v02⟩ := v₁
  have k₁ : ∀ r, r ≠ R + 244 → r ≠ R + 245 → ¬ ztdfd → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => f₁.1 r ztnux
  have hA1 : ztdc := k₁ _ ztu
    ztu by_decide
  zumbz
  have hC1 : ztwxu := by_grind
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, -⟩ := absKey_meets P W c₁ e₁.wb_right
    ⟨hG, hHW, by_grind, H, C, hC1,
      ⟨by_omega, by_grind, by_grind⟩,
      by grind⟩ by_grind
  replace hk₂ : k₂ ≤ 16700 := hk₂
  have ar := post₂ H C hC1
  have F₂ := exec_frameB e₂ wr_absKey
  obtain ⟨c₃, e₃, v₃, f₃⟩ := copies_run (P := P) ztwck c₂ e₂.wb_right (by
    simp only [recList, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl) q (rfl | rfl | rfl | rfl) <;> simp <;> omega)
    (by simp [recList])
  simp only [recList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₃
  obtain ⟨w0, w1, w2, w3⟩ := v₃
  have k₃ :=
    fun r hr => f₃.1 r (by simp [recList]; omega)
  have r₂ := F₂.1
  have l1 : (keyList R).length = 5 := rfl
  have l3 : (recList R).length = 4 := rfl
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, ?_, ?_, ?_, ?_⟩
  · rw [k₃ _ by_omega, r₂ _ ztlgi, v44]
  · rw [k₃ _ by_omega, r₂ _ ztlgi, v45]
  · have ar' : AbsRec P c₂ 50210 ((chainModel C).pos _
        ⟨c₁.nreg 50201, c₁.nreg 50202⟩).1 C.radius := ar
    rw [v01, v02] at ar'
    exact absRec_copy ar' w0 ztqfg (by rw [w2]) (by zupbo)
  · refine ((frameB_mono f₁ ztez).trans (frameB_mono F₂ ztez)).trans
      (frameB_mono f₃ ztez)
    · simp [keyList] at hr; simp only [Bkey, Bool.or_eq_true, decide_eq_true_eq]; omega
    · simp only [Bkey, hr, Bool.or_true, Bool.true_or]
    · simp [recList] at hr; simp only [Bkey, Bool.or_eq_true, decide_eq_true_eq]; omega

/-- **Accepting the candidate.** -/
theorem leafAcc_exec (_hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W zthyp c c' k ∧ k = 7 ∧ c'.nreg ztpa = 1 ∧
      c'.nreg ztbjl = c.nreg ztbme ∧ c'.nreg ztbyz = c.nreg ztbpp ∧
      c'.nreg zthce = c.nreg ztnof ∧ c'.nreg (R + 25) = c.nreg (R + 241) ∧
      c'.nreg (R + 26) = c.nreg (R + 242) ∧ c'.nreg (R + 27) = c.nreg (R + 243) ∧
      FrameB ztxxb c c' := by
  zuban

  obtain ⟨c₂, e₂, v₂, f₂⟩ := copies_run (P := P) ztvei c₁ e₁.wb_right (by
    simp only [accList, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl) q (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp)
    (by simp [accList])
  simp only [accList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₂
  obtain ⟨a1, a2, a4, a5, a6, a7⟩ := v₂
  have ex : Exec P W zthyp c c₂ _ := .seq e₁ e₂
  refine ⟨c₂, _, ex, rfl, ?_, by_simp_all, by_simp_all,
    by simp_all, by_simp_all, by_simp_all,
    by simp_all, ?_⟩
  · have g : ((accList R).map Prod.fst).contains ztpa = false := by simp [accList]
    rw [f₂.1 _ g, hc₁]; simp
  · have fa : FrameB ztxxb c c₁ :=
      frameB_mono (exec_frameB e₁ (show wr ztbadw _ = true by
        zumym)) (fun r hr => by zvnih at hr; simp_all)
    have fb : FrameB ztxxb c₁ c₂ :=
      frameB_mono f₂ (fun r hr => by
        simp [accList] at hr; grind)
    exact fa.trans fb

/-- The write set of `leafCmp`. -/
def Bcmp2 (R : ℕ) (r : ℕ) : Bool :=
  decide ztjlv || Bprim r || decide ztqt
theorem cmpLoad_run {R u v : ℕ} (hR : RegsOK R) (hu : u + 4 ≤ 300)
    (hv : v + 4 ≤ 300) (c : Config) (hw : WordsBounded W c) :
    ∃ c', Exec P W (block (copies ztrno)) c c' 8 ∧
      (∀ i, i < 4 → c'.nreg (50201 + i) = c.nreg ztqcb) ∧
      (∀ i, i < 4 → c'.nreg (50205 + i) = c.nreg (R + v + i)) ∧
      FrameB (fun r => decide ztqt) c c' := by
  zqbfq
  obtain ⟨c', e, v', f⟩ := copies_run (P := P) ztrno c hw (by
    simp only [cmpLoad, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega)
    (by simp [cmpLoad])
  simp only [cmpLoad, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v'
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := v'
  refine ⟨c', e, fun i hi => ?_, fun i hi => ?_, frameB_mono f (fun r hr => by
    simp [cmpLoad] at hr; grind)⟩
  · interval_cases i
    · exact a0
    · exact a1
    · exact a2
    omega
  · interval_cases i
    · exact b0
    · exact b1
    · exact b2
    omega

/-- An abscissa record read from `R + u …` into the input slot at `s`. -/
theorem absRec_moved {r s : ℕ} {x R : ℝ} (h : AbsRec P c r x R)
    (hc : ∀ i, i < 4 → c'.nreg ztni = c.nreg (r + i)) : AbsRec P c' s x R :=
  absRec_copy h (by simpa using hc 0 by_omega) by_simp_all by_simp_all
    by_simp_all

/-- **Comparing the abscissae** of the candidate (record at `R + 240`) and of the minimum
(record at `R + 24`). -/
theorem leafCmp_exec (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {xc xb Rd : ℝ}
    (hc : AbsRec P c ztnof xc Rd) (hb : AbsRec P c zthce xb Rd)
    (hroom : c.nreg ALLOC + 600 ≤ W) :
    ∃ c' k, Exec P W ztqsv c c' k ∧ k ≤ 600 ∧ BitIs c' ztbtr ztuel ∧
      BitIs c' ztces (xb < xc) ∧ FrameB ztgdf c c' := by
  zqbfq
  -- first comparison
  obtain ⟨c₁, e₁, a₁, b₁, f₁⟩ := cmpLoad_run (P := P) (u := 240) (v := 24) hR by_omega
    by_omega c hw
  zuhwg
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, -⟩ := absCmp_meets P W c₁ e₁.wb_right
    ⟨hG, hW, xc, xb, Rd, absRec_moved hc ztgjg,
      absRec_moved hb ztgjg⟩ by_grind
  replace hk₂ : k₂ ≤ 260 := hk₂
  have bit₂ := post₂ xc xb Rd (absRec_moved hc by_omega)
    (absRec_moved hb by_omega)
  have F₂ := exec_frameB e₂ wr_absCmp
  have e₃ := Exec.copyN (P := P) e₂.wb_right ztbtr 50210
  zudkz
  zubj
  -- registers of `c` in the band of `R` survive
  have keep3 : ∀ r, R ≤ r → r < R + 300 → r ≠ R + 246 → c₃.nreg r = c.nreg r := fun r h1 h2 h3 => by
    zumwr; simp only [upd, h3, ↓reduceIte]
    rw [F₂.1 r (bprim_R' hR h1 h2), f₁.1 r by_grind]
  have hA3 : ztcke := by
    zumwr; zundi
    rw [F₂.1 _ by_rfl, hA1]
  -- second comparison
  obtain ⟨c₄, e₄, a₄, b₄, f₄⟩ := cmpLoad_run (P := P) (u := 24) (v := 240) hR by_omega
    by_omega c₃ w₃
  have hA4 : ztgul := by rw [f₄.1 _ by_rfl, hA3]
  have mv : ∀ {u : ℕ} {x : ℝ}, u + 4 ≤ 246 → AbsRec P c (R + u) x Rd →
      ∀ {s : ℕ} {cc : Config}, (∀ i, i < 4 → cc.nreg ztni = c₃.nreg ztqcb) →
        AbsRec P cc s x Rd := fun hu hx s cc hcc =>
    absRec_moved hx (fun i hi => by
      grind)
  obtain ⟨c₅, k₅, e₅, hk₅, post₅, -⟩ := absCmp_meets P W c₄ e₄.wb_right
    ⟨hG, hW, xb, xc, Rd, mv by_omega hb a₄, mv by_omega hc b₄⟩
    by_grind
  zuifh
  have bit₅ := post₅ xb xc Rd (mv by_omega hb a₄) (mv by_omega hc b₄)
  have F₅ := exec_frameB e₅ wr_absCmp
  have e₆ := Exec.copyN (P := P) e₅.wb_right ztces 50210
  have ex : Exec P W ztqsv c _ _ :=
    .seq e₁ (.seq e₂ (.seq (Exec.block_cons e₃ (Exec.block_nil w₃))
      (.seq e₄ (.seq e₅ (Exec.block_cons e₆ (Exec.block_nil e₆.wb_right))))))
  refine ztink
  · -- the first bit survives
    have b3 : BitIs c₃ ztbtr ztuel :=
      ⟨by zumwr; zumwv; exact bit₂.1,
        by zumwr; zumwv; exact bit₂.2⟩
    refine b3.of_eq ?_
    · zudcj
      rw [F₅.1 _ ztlgi,
        f₄.1 _ by_grind]
  · exact ⟨by zumwv; exact bit₅.1, by zumwv; exact bit₅.2⟩
  · have g1 : FrameB ztgdf c c₁ := frameB_mono f₁ ztcvo
    have g2 : FrameB ztgdf c₁ c₂ := frameB_mono F₂ ztcvo
    have g3 : FrameB ztgdf c₂ c₃ := frameB_mono (exec_frameB e₃
      (show wr ztbadu _ = true by
        zumym)) (fun r hr => by
          zvnih at hr; subst hr; zupbp)
    have g4 : FrameB ztgdf c₃ c₄ := frameB_mono f₄ ztcvo
    have g5 : FrameB ztgdf c₄ c₅ := frameB_mono F₅ ztcvo
    have g6 : FrameB ztgdf c₅ _ := frameB_mono (exec_frameB e₆
      (show wr ztbadv _ = true by
        zumym)) (fun r hr => by
          zvnih at hr; subst hr; zupbp)
    exact g1.trans (g2.trans (g3.trans (g4.trans (g5.trans g6))))

/-! ## The running minimum after one hit -/

/-- The running minimum depends only on its registers. -/
theorem BestOK.congr {C : Chain} {R : ℕ} {c c' : Config} {S : Set Point} {z : Point}
    {σ : ℝ} (h : BestOK P C R c S z σ) (e0 : c'.nreg ztpa = c.nreg ztpa)
    (e1 : c'.nreg ztbjl = c.nreg ztbjl) (e2 : c'.nreg ztbyz = c.nreg ztbyz)
    (e4 : c'.nreg zthce = c.nreg zthce) (e5 : c'.nreg ztqbt = c.nreg ztqbt)
    (e6 : c'.nreg ztqbu = c.nreg ztqbu)
    (e7 : c'.nreg ztqbv = c.nreg ztqbv) : BestOK P C R c' S z σ := by
  zuboy
  refine ⟨by_omega, fun hf => ?_, by_simp_all⟩
  obtain ⟨t, ht, hp, he, hpos, ha⟩ := h1 by_omega
  exact ⟨t, ht, by_simp_all, by_omega, by_simp_all,
    absRec_copy ha e4 e5 e6 e7⟩
theorem dirOf_eq_one (h : v = 1) : dirOf v = 1 := by zungv
theorem dirOf_ne_one (h : v ≠ 1) : dirOf v = -1 := by zungv

/-- The write set of `leafHit`. -/
def Bhit (R : ℕ) (r : ℕ) : Bool :=
  decide ztbeb || decide ztent || Bprim r ||
    decide ztqt
theorem bhit_range {R r : ℕ} (h : ztbeb ∨ ztent ∨
    ztqt) : Bhit R r = true := by
  unfold Bhit
  grind
theorem bhit_prim {R r : ℕ} (h : Bprim r = true) : Bhit R r = true := by simp [Bhit, h]

/-- **A hit updates the running minimum.** -/
theorem leafHit_exec (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W) {H : Host} {C : Chain}
    (hwf : ChainWF P ztm c.nmem ztwup)
    (hC : ChainDescAt c.nmem ztwup zta H C)
    (hreg : ∀ H', HostAt c.nmem ztbasl H' → HostRegular P.n H')
    {S A : Set Point} {z : Point} {σ t : ℝ} (hA : FirstHit A z σ t)
    (he : c.nreg 140011 < (chainModel C).W.n)
    (hp : ProperPos ztc zta P.n ztdqm)
    (hpos : (chainModel C).pos zta ztdqm = rayPt z σ t)
    (hz : |z.2| < C.radius) (h30 : c.nreg ztgx = 0) (h31 : c.nreg zthl = 1)
    (hσb : BitIs c ztbgt ztwyb) (hσ : σ = dirOf ztxnk)
    (hbest : BestOK P C R c S z σ) (hroom : c.nreg ALLOC + 17400 ≤ W) :
    ∃ c' k, Exec P W ztvyb c c' k ∧ k ≤ 17400 ∧ BestOK P C R c' ztjmc z σ ∧
      FrameB ztpwh c c' := by
  zqbfq
  have hP3 : ztmd := by unfold hostWords at hHW; omega
  have hy : |((chainModel C).pos zta ⟨c.nreg 140011, c.nreg 140012⟩).2| < C.radius := by
    simp_all
  obtain ⟨c₁, k₁, e₁, hk₁, p44, p45, rc, f₁⟩ := leafKey_exec (P := P) hR c hw hG hHW hwf hC
    hreg he hp hy by_omega
  zvnbl at rc
  have k1 : ∀ r, R ≤ r → r < R + 240 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r (by simp only [Bkey, bprim_R' hR h1 by_omega, Bool.or_false, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega)
  have hA1 : ztdc := f₁.1 _ (by
    unfold ALLOC
    simp only [Bkey, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega)
  have best₁ : BestOK P C R c₁ S z σ := hbest.congr by_simp_all
    by_simp_all by_simp_all by_simp_all
    by_grind by_grind by_grind
  zud
  have fB : ∀ {B : ℕ → Bool} {c₀ c' : Config}, FrameB B c₀ c' → (∀ r, B r = true → Bhit R r) →
      FrameB _ c₀ c' := frameB_mono
  have f₁' : ztukw := fB f₁ (fun r hr => by
    simp only [Bkey, Bool.or_eq_true, decide_eq_true_eq] at hr
    zubpr
    · exact bhit_range by_omega
    · exact bhit_prim h
    · exact bhit_range by_omega)
  -- the acceptance
  have accept : ∀ (cc : Config), WordsBounded W cc → FrameB ztpwh c cc →
      (∀ r, R + 240 ≤ r → r < R + 246 → cc.nreg r = c₁.nreg r) →
      ztgeh →
      ∃ c' k, Exec P W zthyp cc c' k ∧ k = 7 ∧ BestOK P C R c' ztjmc z σ ∧
        FrameB ztpwh c c' := by
    intro cc hcc fcc hr hS
    obtain ⟨c', k, ex, hk, a0, a1, a2, a4, a5, a6, a7, fa⟩ := leafAcc_exec (P := P) hR cc hcc
      by_omega
    refine ⟨c', k, ex, hk, ⟨by rw [a0], fun _ => ⟨t, ?_, ?_, ?_, ?_, ?_⟩, fun h' => absurd a0 h'⟩,
      fcc.trans (fB fa (fun r hr => by
        zvmwo at hr; exact bhit_range ztcgw))⟩
    · rcases hS with hS | ⟨tb, htb, hle⟩
      · exact firstHit_union_right hS hA
      · zulfc
    · zundj; exact hp
    · rw [a1, hr _ by_omega by_omega, p44]; exact he
    · zundj; omega
    · exact absRec_copy rc (by rw [a4, hr _ by_omega by_omega])
        (by rw [show R + 24 + 1 = R + 25 by omega, a5, hr _ by_omega by_omega])
        (by rw [show R + 24 + 2 = R + 26 by omega, a6, hr _ by_omega by_omega])
        (by rw [show R + 24 + 3 = R + 27 by omega, a7, hr _ by_omega by_omega])
  have c20 : c₁.nreg _ = c.nreg ztpa := k1 _ by_omega by_omega
  zuefz

  · -- no minimum yet
    zulkw
    obtain ⟨c', k, ex, hk, hb, fr⟩ := accept c₁ w₁ f₁' by_omega ztvcb
    exact ztgoi
  -- compare with the minimum
  zufur
  obtain ⟨tb, htb, hpb, heb, hposb, rb⟩ := best₁.2.1 hf1
  obtain ⟨c₂, k₂, e₂, hk₂, b46, b47, f₂⟩ := leafCmp_exec (P := P) hR c₁ w₁ hG hP3 rc rb
    by_omega
  have k2 : ztgqd := fun r h1 h2 =>
    f₂.1 r (by simp only [Bcmp2, bprim_R' hR h1 by_omega, Bool.or_false, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega)
  have f₂' : ztukx := f₁'.trans (fB f₂ (fun r hr => by
    simp only [Bcmp2, Bool.or_eq_true, decide_eq_true_eq] at hr
    zubpr
    · exact bhit_range by_omega
    · exact bhit_prim h
    · exact bhit_range by_omega))
  -- keeping the minimum
  have keep : tb ≤ t → BestOK P C R c₂ _ z σ := fun hle => by
    refine ⟨by zuogg; omega, fun _ => ⟨tb, ?_, ?_, ?_, ?_, ?_⟩,
      fun h' => absurd ztkua h'⟩
    · zulfb
    · zqbfs
    · zuhmt
    · zqbfs
    · exact absRec_copy rb zthym zthym
        zthym zthym
  have r35 : ztzpw := by
    zufnv
  have r30 : ztbacr := by
    zuemi
  have hr₂ : ∀ r, R + 240 ≤ r → r < R + 246 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    k2 r by_omega h2
  zue
  zubws

  · -- `σ = 1`: accept iff `xc < xb`
    zubob

    zqbft
    zudkf

    · zudze
      zqbfr
      exact ⟨c', _, .seq e₁ ztgws,
        by omega, hbest', fr⟩
    · have hge : ztpqd := by
        zubqk
        zudmn
      exact ⟨c₂, _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_true hs (.ifLtN_false hb
        ztbun)))), by_omega, keep hge, f₂'⟩
  · -- `σ = -1`: accept iff `xb < xc`
    zuuf

    zqbft
    zudke

    · zudzf
      zqbfr
      exact ⟨c', _, .seq e₁ ztgwr,
        by omega, hbest', fr⟩
    · have hge : ztpqd := by
        zubqk
        zudmo
      exact ⟨c₂, _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_false hs (.ifLtN_false hb
        ztbun)))), by_omega, keep hge, f₂'⟩
end
end ShotList
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbix" : tactic => `(tactic| (have hs1 := lt_of_lt_of_le hs.2 ztwth
                                           have hs2 := lt_of_lt_of_le hs.2 ztwti
                                           have hs3 := lt_of_lt_of_le hs.2 ztgh))
local macro "zqbiy" : tactic => `(tactic| (rw [hUR]
                                           rcases hrole with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩))
local macro "zqbiz" : tactic => `(tactic| rcases hrole with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩)
local macro "zqbja" : tactic => `(tactic| (subst hρ1
                                           rcases hrole with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩))
set_option hygiene true

/-!
# The sweep (WP-D), part 8: chains of chords (lemma (E) without uniqueness)

At a walk vertex two chords of an admissible family can be attached at one position (a *tie*,
`FactsTie`): one goes east, one goes west, and one region lies on the same side of both (the
*middle* region, which faces no walk position near the vertex).  A region of `F₂⁺` above a fused
chord can therefore be a middle region at the `C₂` end of that chord, and its label must be found
further along the chain of collinear chords through the tie.

* `SideOf`: the region containing the points just on one side (`ρ = 1`: above, `ρ = -1`: below)
  of every point of a chord in the domain.
* `off_step`, `chord_bound`: the arithmetic of offsets behind the planarity argument: the
  positions facing a region on one side of a chord lie beyond the chord in walk order.
* `local_step`: at a position of the right stretch, the side of a fused chord is faced (and then
  carries a label), or the position is a tie whose other chord continues the chain.
* `half_walk`: walking along the chain in one direction gives a label or a bound.
* `label_side_gen` (**lemma (E)**): the labels of the region on the side `ρ` of a fused chord
  `e ⊆ c ∈ S₂` attached in the right stretch are the region on the side `ρ` of `c`.
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft freeIn regionsIn
  sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Jordan (offset)
open Chazelle.Geometry (lerp)
open WalkEmbed
namespace Sweep
def SideOf (M : Model) (ρ : ℝ) (c U : Set Point) : Prop :=
  ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztdis : Point) ∈ U
variable {M : Model} {c U : Set Point}
theorem sideOf_one_iff : SideOf M 1 c U ↔ M.AboveOf c U := by
  unfold SideOf Model.AboveOf; simp
theorem sideOf_neg_one_iff :
    SideOf M (-1) c U ↔ M.BelowOf c U := by
  unfold SideOf Model.BelowOf; simp [sub_eq_add_neg]

/-- Two regions on the same side of a chord (with a point in the domain) are equal. -/
theorem sideOf_eq {F : Set ztf} {ρ : ℝ} {c U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) (h : SideOf M ρ c U) (h' : SideOf M ρ c U')
    {z : Point} (hz : z ∈ c) (hzD : z ∈ M.D) : U = U' :=
  region_eq_of_side hU hU' (h z hz hzD) (h' z hz hzD)

/-- A region on the side `ρ` of a horizontal chord contains the points just left of the chord
directed so that `ρ` is on its left. -/
theorem left_of_side {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {c U : Set Point}
    (h : SideOf M ρ c U) {a b : Point} (hab : a.2 = b.2) (hmid : lerp a b ztcn ∈ c)
    (hmidD : lerp a b ztcn ∈ M.D) (hpos : 0 < ρ * ztbco) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset a b ztcn δ ∈ U := by
  have hρρ : ρ * ρ = 1 := by_grind
  refine (eventually_mul_pos (h _ hmid hmidD) hpos).mono fun δ hδ => ?_
  rw [offset_mid_ab hab]
  grind

/-! ## Offsets along a chain -/

/-- Offsets of a key outside a closed cyclic arc. -/
theorem off_not_arc {n g a b x : ℝ} (hg : 0 ≤ g) (hgn : g < n) (ha0 : 0 ≤ a) (han : a < n)
    (hb0 : 0 ≤ b) (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) (hab : a ≠ b) (hxa : x ≠ a)
    (hxb : x ≠ b) (h : ¬ sideInArc a b x) :
    (off n g a < off n g b → off n g x < off n g a ∨ off n g b < off n g x) ∧
    (off n g b < off n g a → off n g b < off n g x ∧ off n g x < off n g a) := by
  have hne : ztcrn :=
    fun hu hun hw hwn huw h => huw ztmmt
  refine ⟨fun hlt => ?_, fun hlt => ?_⟩
  · rw [sideInArc_iff_off hg hgn ha0 han hb0 hbn hx0 hxn hlt] at h
    grind
  · rw [Chazelle.Chain.sideInArc_swap hab hxa hxb, not_not,
      sideInArc_iff_off hg hgn hb0 hbn ha0 han hx0 hxn hlt] at h
    zubh

/-- **One step along a chain** (arithmetic).  With `θ = 1`, the key `x` is outside the closed
arc from the far end `F` to the near end `N`; with `θ = -1`, outside the arc from `N` to `F`.
If `x` is in the stretch `(0, L)`, the near end is in the stretch and `x` is beyond the far end
(or the far end is outside the stretch), then `x` is beyond the near end. -/
theorem off_step {L oF oN ox θ : ℝ} (hθ : θ = 1 ∨ θ = -1)
    (h1 : θ = 1 → (oF < oN → ox < oF ∨ oN < ox) ∧ (oN < oF → oN < ox ∧ ox < oF))
    (h2 : θ = -1 → (oN < oF → ox < oN ∨ oF < ox) ∧ (oF < oN → oF < ox ∧ ox < oN))
    (hNF : oN ≠ oF) (hx0 : 0 < ox) (hxL : ox < L) (hN0 : 0 < oN) (hNL : oN < L)
    (hpre : 0 < θ * (ox - oF) ∨ L ≤ oF ∨ oF ≤ 0) : 0 < θ * (ox - oN) := by
  zugaf
  · grind
  grind

/-! ## Faced sides and middle regions at an attachment -/

/-- The faced side of a chord at an attachment: if the chord goes in direction `dir` from the
point of the position, the side `-dir` is faced just after and the side `dir` just before. -/
def FacedSide (M : Model) (p : ℕ) (t ρ dir : ℝ) (U : Set Point) : Prop :=
  (ρ * dir = -1 → AfterFaces M p t U) ∧ (ρ * dir = 1 → BeforeFaces M p t U)

/-- A point of an attached admissible chord in the domain. -/
theorem exists_mem_dom (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ}
    {t : ℝ} (hA : SideAttach M.W c p t) : ∃ z ∈ c, z ∈ M.D := by
  obtain ⟨e, -, -, hce, hopen, -⟩ := hM.attach_other_end hc hA
  refine ⟨lerp _ e ztcn, ?_, hopen _ by_grind⟩
  zujir
  zujus

/-- An attached admissible chord is not vertical: it does not lie on both sides of the point of
its attachment. -/
theorem dir_not_both (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ}
    {t : ℝ} (hA : SideAttach M.W c p t) (h1 : ∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1)
    (h2 : ∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1) : False := by
  obtain ⟨w, hwne, hwy, hce, -⟩ := hM.attach_other_end hc hA
  have hw : ztsmv := by zvnme; exact Geometry.right_mem_segment _ _
  grind

/-- **The regions at an attachment.**  For a chord `e` of a chord family of a good model,
attached at `(p, t)` and going in direction `dir` from its point, and the region `U` on its side
`ρ`:
* if no other chord of the family is attached there, `U` is faced on the side given by
  `FacedSide`;
* if another chord `e'` is attached there (a tie: `t = 0`), then according to the direction of the
  leaving walk edge either `U` is faced as above, or `U` is the middle region, on the same side of
  `e'` (above both chords when the leaving edge goes down, below both when it goes up). -/
theorem faced_or_middle {Q : Polygon} {F : Set ztf} (hGM : GoodModel M)
    (hFam : M.ChordFamily Q F) {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W e p t) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {U : Set Point}
    (hU : U ∈ M.regions F) (hS : SideOf M ρ e U) {dir : ℝ}
    (hdir : ztcqu ∨
      ztcmz) :
    ((∀ e' ∈ F, SideAttach M.W e' p t → e' = e) → FacedSide M p t ρ dir U) ∧
    (∀ e' ∈ F, e' ≠ e → SideAttach M.W e' p t → t = 0 ∧ (M.wb p).2 ≠ (M.wa p).2 ∧
      ((M.wb p).2 < (M.wa p).2 → (ρ = 1 → SideOf M ρ e' U) ∧ (ρ = -1 → FacedSide M p t ρ dir U)) ∧
      ((M.wa p).2 < (M.wb p).2 → (ρ = -1 → SideOf M ρ e' U) ∧ (ρ = 1 → FacedSide M p t ρ dir U))) := by
  zubm
  zubl

  obtain ⟨z₀, hz₀, hz₀D⟩ := exists_mem_dom hM ztesz hA
  have hn0 : ztbiy := by have := hA.1; omega
  refine ⟨fun huniq => ?_, fun e' he' hne hA' => ?_⟩
  · -- a unique attachment: `UpSideSpec`
    obtain ⟨U', V', hU', hV', -, ⟨δ, hδ, hfac⟩, hleft, hright⟩ :=
      upSide M Q F hGM hFam e he p t hA huniq
    have hpt : Geometry.lerp ztpr ztoa t = sidePt M.W p t := rfl
    zvmxe at hleft hright
    have hafter : AfterFaces M p t U' := ⟨δ, hδ, fun s h0 h1 h2 =>
      (hfac p _ hA.1 (by zupbu) h2).1 by_grind⟩
    have hbefore : BeforeFaces M p t V' := by
      refine ⟨min δ 1, lt_min hδ one_pos, fun ht s h0 h1 h2 => ?_, fun ht s h0 h1 => ?_⟩
      · zujyi
        exact (hfac p _ hA.1 by_linarith (by zuoww)).2
          by_grind
      zucfb
      zujyi
      have h1'' : ztdrm := by_grind
      have hs1 : 1 - s < 1 := by_linarith
      refine (hfac _ _ ztjkl by_linarith hs1).2 ?_
      zujda
      · subst hp0
        right
        rw [show (0 + M.W.n - 1) % M.W.n = M.W.n - 1 by
          rw [Nat.mod_eq_of_lt by_grind]; omega,
          Nat.cast_sub by_omega]
        grind
      · left
        rw [prev_mod hA.1 hp0, Nat.cast_sub by_omega]
        grind
    rcases hdir with ⟨rfl, hd⟩ | ⟨rfl, hd⟩
    · obtain ⟨hb, ha⟩ := hleft hd
      zumki
      · zuiax

        rw [sideOf_eq hU hU' hS ztwdz hz₀ hz₀D]; omega
      · zugnn

        rw [sideOf_eq hU hV' hS ztwea hz₀ hz₀D]; omega
    · obtain ⟨ha, hb⟩ := hright hd
      zumki
      · zugnn

        rw [sideOf_eq hU hU' hS ztwea hz₀ hz₀D]; omega
      · zuiax

        rw [sideOf_eq hU hV' hS ztwdz hz₀ hz₀D]; omega
  · -- a tie
    have hne' := Ne.symm hne
    have hnot2 : ∀ {c : Set Point}, c ∈ F → SideAttach M.W c p t →
        ztdqa → ztdqb → False :=
      fun hc hAc h1 h2 => dir_not_both hM ztlz hAc h1 h2
    obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW, hrole⟩ : ∃ ce cw, ce ∈ F ∧ cw ∈ F ∧
        SideAttach M.W ce p t ∧ SideAttach M.W cw p t ∧
        zticb ∧ zticc ∧
        ((dir = 1 ∧ ce = e ∧ cw = e') ∨ (dir = -1 ∧ cw = e ∧ ce = e')) := by
      rcases hM.tie_pair hF he he' hne' hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · grind
      grind
    zudix
    refine ⟨ht0, hhor, fun hdown => ?_, fun hup => ?_⟩
    · obtain ⟨-, U₁, V₁, R, hU₁, hV₁, hR, hbU, hbV, haRe, haRw, ⟨δ₁, hδ₁, hf₁⟩,
        ⟨δ₂, hδ₂, hf₂⟩, -⟩ := hM.tie_down hF hfin hce hcw hAe hAw hE hW hdown
      zudlw
      refine ztlwa
      · subst hρ1
        have hUR : ztmtw := by
          zqbiz
          · exact sideOf_eq hU hR hS (sideOf_one_iff.2 haRe) hz₀ hz₀D
          · exact sideOf_eq hU hR hS (sideOf_one_iff.2 haRw) hz₀ hz₀D
        zqbiy
        · exact sideOf_one_iff.2 haRw
        · exact sideOf_one_iff.2 haRe
      · zqbja
        · refine ztlvu
          rw [sideOf_eq hU hU₁ hS (sideOf_neg_one_iff.2 hbU) hz₀ hz₀D]
          exact ztrfd
        · refine ztlvv
          rw [sideOf_eq hU hV₁ hS (sideOf_neg_one_iff.2 hbV) hz₀ hz₀D]
          exact ztopw
    · obtain ⟨-, U₁, V₁, R, hU₁, hV₁, hR, haU, haV, hbRe, hbRw, ⟨δ₁, hδ₁, hf₁⟩,
        ⟨δ₂, hδ₂, hf₂⟩, -⟩ := hM.tie_up hF hfin hce hcw hAe hAw hE hW hup
      zudlw
      refine ztlwa
      · subst hρ1
        have hUR : ztmtw := by
          zqbiz
          · exact sideOf_eq hU hR hS (sideOf_neg_one_iff.2 hbRe) hz₀ hz₀D
          · exact sideOf_eq hU hR hS (sideOf_neg_one_iff.2 hbRw) hz₀ hz₀D
        zqbiy
        · exact sideOf_neg_one_iff.2 hbRw
        · exact sideOf_neg_one_iff.2 hbRe
      · zqbja
        · refine ztlvv
          rw [sideOf_eq hU hV₁ hS (sideOf_one_iff.2 haV) hz₀ hz₀D]
          exact ztopw
        · refine ztlvu
          rw [sideOf_eq hU hU₁ hS (sideOf_one_iff.2 haU) hz₀ hz₀D]
          exact ztrfd

/-! ## Bounds along a chain -/

/-- The positions inside walk edges, not cuts, facing `G`, with offset (from `g`) in `(0, L)`, lie
beyond the offset `o` in the direction `θ`. -/
def Bound (M : Model) (F : Set ztf) (G : Set Point) (g L θ o : ℝ) : Prop :=
  ∀ (p : ℕ) (t : ℝ), p < M.W.n → t ∈ Ioo (0 : ℝ) 1 → ¬ M.IsCut F ztk → M.Faces p t G →
    0 < off M.W.n g ztk → off M.W.n g ztk < L → 0 < θ * (off M.W.n g ztk - o)

/-- **The bound across one chord.**  Let `f ∈ F` be attached at a near position `N` and a far
position `Fr` (distinct points), `G` on its side `ρ`, oriented by `θ` (`G` is on the left of `f`
directed from `Fr` to `N` if `θ = 1`, from `N` to `Fr` if `θ = -1`).  If the near offset is in
`(0, L)` and every position facing `G` is beyond the far offset (or the far offset is outside
`(0, L)`), then every position facing `G` is beyond the near offset. -/
theorem chord_bound (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {f : Set Point} (hf : f ∈ F) {pn pf : ℕ} {tn tf : ℝ} (hN : SideAttach M.W f pn tn)
    (hFr : SideAttach M.W f pf tf) (hNF : sidePt M.W pn tn ≠ sidePt M.W pf tf) {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point} (hG : G ∈ M.regions F) (hS : SideOf M ρ f G)
    {θ : ℝ} (hθ : θ = 1 ∨ θ = -1)
    (hori : 0 < θ * ρ * ztgwh) {g L : ℝ}
    (hg0 : 0 ≤ g) (hgn : g < M.W.n) (hN0 : 0 < off M.W.n g ztbue)
    (hNL : off M.W.n g ztbue < L)
    (hpre : ∀ (p : ℕ) (t : ℝ), p < M.W.n → t ∈ Ioo (0 : ℝ) 1 → ¬ M.IsCut F ztk →
      M.Faces p t G → 0 < off M.W.n g ztk → off M.W.n g ztk < L →
      0 < θ * (off M.W.n g ztk - off M.W.n g ztbbc) ∨ L ≤ off M.W.n g ztbbc ∨
        off M.W.n g ztbbc ≤ 0) :
    Bound M F G g L θ (off M.W.n g ztbue) := by
  intro p t hp ht hnc hfG h0 hL
  obtain ⟨kN0, kNn⟩ := Corr.key_mem hN.1 hN.2.1 hN.2.2.1
  obtain ⟨kF0, kFn⟩ := Corr.key_mem hFr.1 hFr.2.1 hFr.2.2.1
  obtain ⟨kx0, kxn⟩ := Corr.key_mem hp ht.1.le ht.2
  have hkNF := WalkAx.key_ne_of_pt_ne hN hFr hNF
  have hxN := fun h => hnc ⟨f, hf, pn, tn, hN, h⟩
  have hxF : (p : ℝ) + t ≠ pf + tf := by_grind
  have hoNF : off M.W.n g _ ≠ off M.W.n g _ :=
    fun h => hkNF (off_inj hg0 hgn kN0 kNn kF0 kFn h)
  zudel
  have hmid : ztzjj := by
    zugdw
  zufvn
  have hsym : lerp ztegb ztegc ztcn =
      lerp ztegc ztegb ztcn := by
    zubvj
  refine off_step hθ ztrqk ztrqk hoNF h0 hL hN0 hNL
    by_grind
  · subst hθ1
    have hleft := left_of_side hρ hS hy.symm
      by_grind by_grind by_linarith
    have hnot : ztsnz := fun hin =>
      hM.not_left_of_after hF hf hFr hN ztqax hG hp ht hin hfG hleft
    have := off_not_arc hg0 hgn kF0 kFn kN0 kNn kx0 kxn (Ne.symm hkNF) hxF hxN hnot
    omega
  · subst hθ1
    have hleft := left_of_side hρ hS hy hmid
      hmidD by_linarith
    have hnot : ztsnz := fun hin =>
      hM.not_left_of_after hF hf hN hFr hNF hG hp ht hin hfG hleft
    exact off_not_arc hg0 hgn kN0 kNn kF0 kFn kx0 kxn hkNF hxN hxF hnot

/-! ## Junction facts for the chains -/
section JunctionFacts
variable (J : Merge.Junction)

/-- **`RLabel` from the positions just after a position of the right stretch.** -/
theorem rlabel_after (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {G V : Set Point}
    (hW : AfterFaces ztbm
      ztbn t G)
    (hW₂ : AfterFaces ztj
      ztwmz t V) :
    RLabel J S₂ G V := by
  zuv
  zucte

  obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_after hC.hM hC.hF hC.hfin
    ztwlh).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min ztkaw ztca from
      lt_min ztdvj by_linarith))).exists
  zubqy

/-- **`RLabel` from the positions just before a position of the right stretch.** -/
theorem rlabel_before (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J) {G V : Set Point}
    (hW : BeforeFaces ztbm
      ztbn t G)
    (hW₂ : BeforeFaces ztj
      ztwmz t V) :
    RLabel J S₂ G V := by
  zuv
  zubjl

  · obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
      ztwlh).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min _ t from
        lt_min ztdvj htpos))).exists
    zqbix
    refine ⟨d, hd, t - s, ztomq, ?_, by_grind,
      h2a htpos s hs.1 hs2 hs3⟩
    grind
  · zugij

    zumef
    zudox
    zubdc
    zufpa
    have hPm : ztwoi := by
      zugdg
    zuccz
    have hdq1 : ztxda := by
      have := (hsec rfl).2; unfold dq; split_ifs <;> omega
    have hPm₂ : ztwpj % (chainModel J.right).W.n =
        (ztfw % (chainModel J.right).W.n +
          (chainModel J.right).W.n - 1) % (chainModel J.right).W.n := by
      zuhlo
    obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
      ztcro).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min _ 1 from
        lt_min ztdvj one_pos))).exists
    zqbix
    refine ztfde
    · grind
    · zubii
    grind

/-- **The shared vertex is outside the right stretch** (in offsets). -/
theorem off_shared_out (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ}
    (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hv : sidePt (chainModel J.whole).W p t = J.shared) :
    ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk <
        ((rL1 J + rL2 J : ℕ) : ℝ)) := by
  rintro ⟨h0, hL⟩
  zuv
  obtain ⟨hpd, hoff⟩ := hC.decomp hp ht0 ht1
  set d := dOf (chainModel J.whole).W.n ztve p with hddef
  zueye
  have hdL : ztizq := by
    zuhdh
    zufc
  have hpt := hC.sidePt_eq hdL t
  rw [hpd] at hpt
  zvmxe at hv
  apply hC.noV _ ztfoj t ht0 ht1
  · zujid
    have : d ≤ dq ztns ztpg d := by unfold dq; split_ifs <;> omega
    have : (d : ℝ) ≤ dq ztns ztpg d := by_simp_all
    linarith
  · zujid
    have h1 : dq ztns ztpg d + 1 ≤ rL1 J + rδ J + rL2 J := by
      have := hC.dq_lt hdL; have := hC.hL₂; unfold dq at *; split_ifs at * <;> omega
    have h2 : ((dq ztns ztpg d : ℕ) : ℝ) + 1 ≤ ((rL1 J + rδ J + rL2 J : ℕ) : ℝ) := by
      exact_mod_cast h1
    grind
  · zvmyq; exact (right_vtx0 J).symm

/-- A point of a segment off a set containing its open part, other than its start, is its end. -/
theorem seg_end {D : Set Point} {a b z : Point} (hz : z ∈ Chazelle.segment a b) (hzD : z ∉ D)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ D) (hza : z ≠ a) : z = b := by
  zuje
  zunm
  · zuji
    · simp_all
    simp_all
  · exact absurd (by rw [← hs0, Geometry.lerp_zero]) hza

/-- Two chords of `S₂` containing one chord of `F₂⁺` are equal. -/
theorem s2_eq_of_sub {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {c c' e : Set Point} (hc : c ∈ S₂) (hc' : c' ∈ S₂) (he : e ∈ Merge.augChords J.whole)
    (hec : e ⊆ c) (hec' : e ⊆ c') : c = c' := by
  obtain ⟨y₁, a₁, b₁, hH₁, -, rfl⟩ := he
  zucok
  obtain ⟨y', a', b', hH', -, hc'def, -, -⟩ := Merge.augChords_spec zthxv
  have hab := hH₁.lt
  have hm : (((a₁ + b₁) / 2, y₁) : Point) ∈ Visibility.hseg y₁ a₁ b₁ :=
    ⟨rfl, by_grind, by_grind⟩
  have hmc := hec hm
  have hmc' := hec' hm
  rw [hcdef] at hmc hec ⊢
  rw [hc'def] at hmc' hec' ⊢
  have hl := hec (show (zttff : Point) ∈ Visibility.hseg y₁ a₁ b₁ from ztgpm)
  have hr := hec (show (ztthf : Point) ∈ Visibility.hseg y₁ a₁ b₁ from ztgpl)
  rcases Chain.hchordIn_inter hH hH' hmc hmc' with ⟨rfl, rfl, rfl⟩ | ⟨h1, -⟩
  · rfl
  · exfalso
    obtain ⟨-, hl1, -⟩ := hl
    obtain ⟨-, -, hr1⟩ := hr
    grind
end JunctionFacts

/-! ## The local step at a position of the right stretch -/
section Local
variable (J : Merge.Junction)
end Local

/-! ## Walking along a chain -/
section Walk
variable (J : Merge.Junction)

/-- The chords of `F` with a point beyond `q` in the direction of decreasing `κ x`. -/
def beyond (F : Set ztf) (κ : ℝ) (q : Point) : Set ztf :=
  {h | h ∈ F ∧ ∃ z ∈ h, 0 < κ * zttxc}

/-- Opposite directions of the two chords of a tie. -/
theorem tie_opposite {M : Model} (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {f f' : Set Point} (hf : f ∈ F) (hf' : f' ∈ F) (hne : f' ≠ f) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W f p t) (hA' : SideAttach M.W f' p t) {a b : Point} (ha : a ∈ f)
    (hb : b ∈ f') (ha1 : a.1 ≠ (sidePt M.W p t).1) (hb1 : b.1 ≠ (sidePt M.W p t).1) :
    (a.1 - (sidePt M.W p t).1) * (b.1 - (sidePt M.W p t).1) < 0 := by
  rcases hM.attach_dir ztjxh hA with h | h <;> rcases hM.attach_dir (hF hf') hA' with h' | h'
  · exact absurd (hM.attach_east_unique hF hf' hf hA' hA h' h) hne
  · have := lt_of_le_of_ne by_grind (Ne.symm ha1)
    have := lt_of_le_of_ne by_grind hb1
    nlinarith
  · have := lt_of_le_of_ne by_grind ha1
    have := lt_of_le_of_ne by_grind (Ne.symm hb1)
    nlinarith
  · exact absurd (hM.attach_west_unique hF hf' hf hA' hA h' h) hne

/-- A sign making a nonzero quantity positive. -/
theorem exists_sign {ρ r : ℝ} (hρ : ρ = 1 ∨ ρ = -1) (hr : r ≠ 0) :
    ∃ θ : ℝ, (θ = 1 ∨ θ = -1) ∧ 0 < θ * ρ * r := by
  rcases lt_or_gt_of_ne hr with h | h <;> rcases hρ with rfl | rfl
  · simp_all
  · simp_all
  · simp_all
  simp_all
