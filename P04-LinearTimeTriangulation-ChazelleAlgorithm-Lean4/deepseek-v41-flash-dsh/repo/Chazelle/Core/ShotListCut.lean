module

public import Chazelle.Golf

public import Chazelle.Core.ShotListMath
public import Chazelle.Core.SweepPrimOff

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

/-! ## Normalised positions and the order of their keys -/

/-- A **normalised** walk position: proper, and its height code is `0` exactly when its parameter
is `0`. -/
def NormPos (M : Model) (Q : Polygon) (n : ℕ) (x : WPos) : Prop :=
  ProperPos M Q n x ∧ (x.hgt = 0 ∨ 0 < M.param Q x)

/-- The interior bit of a position (`1` iff its height code is positive). -/
def ibit (x : WPos) : ℕ := if 0 < x.hgt then 1 else 0

theorem param_of_norm {M : Model} {Q : Polygon} {n : ℕ} {x : WPos} (h : NormPos M Q n x) :
    (x.hgt = 0 → M.param Q x = 0) ∧ (0 < x.hgt → 0 < M.param Q x) := by
  refine ⟨fun h0 => by unfold Model.param; rw [h0], fun hp => ?_⟩
  rcases h.2 with h0 | h0
  · omega
  · exact h0

/-- **The order of two normalised keys**, when they are not both inside one edge: lexicographic
in the edge and the interior bit. -/
theorem key_lt_iff {M : Model} {Q : Polygon} {n : ℕ} {x y : WPos} (hx : NormPos M Q n x)
    (hy : NormPos M Q n y) (hne : ¬ (x.edge = y.edge ∧ 0 < x.hgt ∧ 0 < y.hgt)) :
    M.key Q x < M.key Q y ↔ x.edge < y.edge ∨ (x.edge = y.edge ∧ ibit x < ibit y) := by
  have px := param_of_norm hx
  have py := param_of_norm hy
  obtain ⟨⟨hx0, hx1, -⟩, -⟩ := hx
  obtain ⟨⟨hy0, hy1, -⟩, -⟩ := hy
  unfold Model.key ibit
  constructor
  · intro h
    rcases lt_trichotomy x.edge y.edge with he | he | he
    · exact Or.inl he
    · refine Or.inr ⟨he, ?_⟩
      Ξ' he at h
      have hlt : M.param Q x < M.param Q y := ⟡
      by_cases hxh : 0 < x.hgt
      · by_cases hyh : 0 < y.hgt
        · exact absurd ⟨he, hxh, hyh⟩ hne
        · Ξ' py.1 (⋄) at hlt; linarith
      · by_cases hyh : 0 < y.hgt
        · Θ hxh, hyh
        · Ξ' px.1 (⋄), py.1 (⋄) at hlt; exact absurd hlt (lt_irrefl _)
    · exfalso
      have : (y.edge : ℝ) + 1 ≤ x.edge := by exact_mod_cast he
      linarith
  · rintro (he | ⟨he, hi⟩)
    · have : (x.edge : ℝ) + 1 ≤ y.edge := by exact_mod_cast he
      linarith
    · Ξ he
      split_ifs at hi with h1 h2 h2 <;> try omega
      Ξ px.1 (⋄)
      have := py.2 h2
      linarith

/-- The order of two keys is the order of their offsets from `0`. -/
theorem key_lt_iff_off {M : Model} {Q : Polygon} {x y : WPos} (hx0 : 0 ≤ M.param Q x)
    (hy0 : 0 ≤ M.param Q y) :
    M.key Q x < M.key Q y ↔
      WalkEmbed.off M.W.n 0 (M.key Q x) < WalkEmbed.off M.W.n 0 (M.key Q y) := by
  have k0 : (0 : ℝ) ≤ M.key Q x := by
    unfold Model.key; have : (0 : ℝ) ≤ x.edge := Nat.cast_nonneg _; linarith
  have k1 : (0 : ℝ) ≤ M.key Q y := by
    unfold Model.key; have : (0 : ℝ) ≤ y.edge := Nat.cast_nonneg _; linarith
  unfold WalkEmbed.off
  Θ k0, k1

/-! ## The comparison blocks -/

/-- The interior bit of a height code. -/
def ibv (h : ℕ) : ℕ := if 0 < h then 1 else 0

/-- Lexicographic order of (edge, interior bit) pairs. -/
def LexLt (e i e' i' : ℕ) : Prop := e < e' ∨ (e = e' ∧ i < i')

/-- `d := 1` if `(eu, ibv hu) < (ev, ibv hv)` lexicographically, else `0` (`z` holds `0`). -/
def kltB (eu hu ev hv d z : ℕ) : Stmt :=
  .ifLtN eu ev (.instr (.constN d 1))
    (.ifLtN ev eu (.instr (.constN d 0))
      (.ifLtN z hu (.instr (.constN d 0))
        (.ifLtN z hv (.instr (.constN d 1)) (.instr (.constN d 0)))))

/-- The registers `kltB` writes. -/
def Bone (d : ℕ) (r : ℕ) : Bool := r == d

theorem wr_kltB (eu hu ev hv d z : ℕ) : wr (Bone d) (kltB eu hu ev hv d z) = true := by
  Θ wr, kltB, wrOK, Bone

theorem kltB_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    (eu hu ev hv d z : ℕ) (hz : c.nreg z = 0) :
    ∃ c' k, Exec P W (kltB eu hu ev hv d z) c c' k ∧ k ≤ 9 ∧
      BitIs c' d (LexLt (c.nreg eu) (ibv (c.nreg hu)) (c.nreg ev) (ibv (c.nreg hv))) ∧
      FrameB (Bone d) c c' := by
  have e1 := Exec.constN (P := P) hw d 1 hW
  have e0 := Exec.constN (P := P) hw d 0 (⋄)
  have wk := wr_kltB eu hu ev hv d z
  have v1 : ∀ p : Prop, p → BitIs { c with nreg := upd c.nreg d 1 } d p :=
    fun p hp => ⟨✓, ⊚ hp⟩
  have v0 : ∀ p : Prop, ¬ p → BitIs { c with nreg := upd c.nreg d 0 } d p :=
    fun p hp => ⟨✓, ⊚ hp⟩
  unfold LexLt ibv
  by_cases h1 : c.nreg eu < c.nreg ev
  · have ex : Exec P W (kltB eu hu ev hv d z) c _ _ := .ifLtN_true h1 e1
    exact ⟨_, _, ex, ⋄, v1 _ (Or.inl h1), exec_frameB ex wk⟩
  by_cases h2 : c.nreg ev < c.nreg eu
  · have ex : Exec P W (kltB eu hu ev hv d z) c _ _ := .ifLtN_false h1 (.ifLtN_true h2 e0)
    exact ⟨_, _, ex, ⋄, v0 _ (⋄), exec_frameB ex wk⟩
  by_cases h3 : c.nreg z < c.nreg hu
  · have ex : Exec P W (kltB eu hu ev hv d z) c _ _ :=
      .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true h3 e0))
    refine ⟨_, _, ex, ⋄, v0 _ ?_, exec_frameB ex wk⟩
    Ξ' hz at h3; simp only [h3, ↓reduceIte]; split_ifs <;> omega
  by_cases h4 : c.nreg z < c.nreg hv
  · have ex : Exec P W (kltB eu hu ev hv d z) c _ _ :=
      .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_false h3 (.ifLtN_true h4 e1)))
    refine ⟨_, _, ex, ⋄, v1 _ ?_, exec_frameB ex wk⟩
    Ξ' hz at h3 h4; simp only [h4, ↓reduceIte, show ¬ 0 < c.nreg hu from h3]; omega
  · have ex : Exec P W (kltB eu hu ev hv d z) c _ _ :=
      .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_false h3 (.ifLtN_false h4 e0)))
    refine ⟨_, _, ex, ⋄, v0 _ ?_, exec_frameB ex wk⟩
    Ξ' hz at h3 h4
    simp only [show ¬ 0 < c.nreg hv from h4, show ¬ 0 < c.nreg hu from h3, ↓reduceIte]; omega

/-! ## The selection of the pieces -/

/-- The four ends of an arc and a hole. -/
inductive End where
  | A | B | X | Y
  deriving DecidableEq

/-- **The pieces selected by the bits**: `hp` the hole is present, `c1 … c6` the tests of
`cutK` (`(x, y) ∋ a`, `(a, b) ∋ y`, `(y, b) ∋ x`, `(a, b) ∋ x`, `(x, b) ∋ y`, `x = a`). -/
def selT (hp c1 c2 c3 c4 c5 c6 : Bool) : List (End × End) :=
  if !hp then [(.A, .B)]
  else if c1 then (if c2 then (if c3 then [(.Y, .X)] else [(.Y, .B)]) else [])
  else if c4 then (.A, .X) :: (if c5 then [(.Y, .B)] else [])
  else if c6 then (if c2 then [(.Y, .B)] else [])
  else [(.A, .B)]

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
  ϴ Bool.not_true, Bool.false_eq_true, ↓reduceIte
  by_cases q1 : sideInArc kx ky ka
  · have := h1.2 q1
    ϴ q1, this, ↓reduceIte
    by_cases q2 : sideInArc ka kb ky
    · have := h2.2 q2
      ϴ q2, this, ↓reduceIte
      by_cases q3 : sideInArc ky kb kx
      · Θ q3, h3.2 q3, End.val
      · have : c3 = false := by cases c3 <;> simp_all
        Θ q3, this, End.val
    · have : c2 = false := by cases c2 <;> simp_all
      Θ q2, this
  · have e1 : c1 = false := by cases c1 <;> simp_all
    ϴ q1, e1, ↓reduceIte, Bool.false_eq_true
    by_cases q4 : sideInArc ka kb kx
    · ϴ q4, h4.2 q4, ↓reduceIte
      by_cases q5 : sideInArc kx kb ky
      · Θ q5, h5.2 q5, End.val
      · have : c5 = false := by cases c5 <;> simp_all
        Θ q5, this, End.val
    · have e4 : c4 = false := by cases c4 <;> simp_all
      ϴ q4, e4, ↓reduceIte, Bool.false_eq_true
      by_cases q6 : kx = ka
      · ϴ q6, ↓reduceIte, h6.2 q6
        by_cases q2 : sideInArc ka kb ky
        · Θ q2, h2.2 q2, End.val
        · have : c2 = false := by cases c2 <;> simp_all
          Θ q2, this
      · have e6 : c6 = false := by cases c6 <;> simp_all
        Θ q6, e6, End.val

/-- The register pair of an end: `A = (L, L + 1)`, `B = (L + 2, L + 3)`, `X = (hx, z)`,
`Y = (hy, z)`. -/
def End.regs (L hx hy z : ℕ) : End → ℕ × ℕ
  | .A => (L, L + 1)
  | .B => (L + 2, L + 3)
  | .X => (hx, z)
  | .Y => (hy, z)

/-- Write the piece with ends `u`, `v` into `d … d + 3`. -/
def putPiece (d : ℕ) (u v : ℕ × ℕ) : List Instr :=
  [.copyN d u.1, .copyN (d + 1) u.2, .copyN (d + 2) v.1, .copyN (d + 3) v.2]

/-- The leaves of the selection tree: the pieces into `N …` and `S …`, their number into `Cn`. -/
def selLeaf (L hx hy z N S Cn : ℕ) : List (End × End) → Stmt
  | [] => block [.constN Cn 0]
  | [p] => .seq (block (putPiece N (End.regs L hx hy z p.1) (End.regs L hx hy z p.2)))
      (block [.constN Cn 1])
  | p :: q :: _ => .seq (block (putPiece N (End.regs L hx hy z p.1) (End.regs L hx hy z p.2)))
      (.seq (block (putPiece S (End.regs L hx hy z q.1) (End.regs L hx hy z q.2)))
        (block [.constN Cn 2]))

/-- **The selection tree** on the bit registers `hpA < hpB` (hole present) and `c1 … c6`
(tested against the zero register `z`). -/
def selB (L hx hy z N S Cn hpA hpB c1 c2 c3 c4 c5 c6 : ℕ) : Stmt :=
  let lf := selLeaf L hx hy z N S Cn
  .ifLtN hpA hpB
    (.ifLtN z c1
      (.ifLtN z c2 (.ifLtN z c3 (lf [(.Y, .X)]) (lf [(.Y, .B)])) (lf []))
      (.ifLtN z c4 (.ifLtN z c5 (lf [(.A, .X), (.Y, .B)]) (lf [(.A, .X)]))
        (.ifLtN z c6 (.ifLtN z c2 (lf [(.Y, .B)]) (lf [])) (lf [(.A, .B)]))))
    (lf [(.A, .B)])

/-- The walk position in the registers `e`, `h`. -/
def posR (c : Config) (r : ℕ × ℕ) : WPos := ⟨c.nreg r.1, c.nreg r.2⟩

/-- The piece in the registers `d … d + 3`. -/
def pieceR (c : Config) (d : ℕ) : WPos × WPos := (posR c (d, d + 1), posR c (d + 2, d + 3))

/-- **The pieces in the registers**: their number in `Cn`, the first in `N …`, the second in
`S …`. -/
def PiecesAt (c : Config) (N S Cn : ℕ) (ps : List (WPos × WPos)) : Prop :=
  c.nreg Cn = ps.length ∧ ps.length ≤ 2 ∧ (∀ p, ps[0]? = some p → pieceR c N = p) ∧
    (∀ p, ps[1]? = some p → pieceR c S = p)

/-- The output registers of the selection avoid the input registers. -/
def SelDisj (L hx hy z N S Cn : ℕ) : Prop :=
  ∀ e : End, ∀ o, (o = Cn ∨ (N ≤ o ∧ o < N + 4) ∨ (S ≤ o ∧ o < S + 4)) →
    (End.regs L hx hy z e).1 ≠ o ∧ (End.regs L hx hy z e).2 ≠ o

/-- **Writing a piece**: the ends read from `u`, `v` (not overwritten before they are read). -/
theorem putPiece_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {d : ℕ}
    {u v : ℕ × ℕ} (hu : u.2 ≠ d) (hv1 : v.1 ≠ d ∧ v.1 ≠ d + 1)
    (hv2 : v.2 ≠ d ∧ v.2 ≠ d + 1 ∧ v.2 ≠ d + 2) :
    ∃ c' k, Exec P W (block (putPiece d u v)) c c' k ∧ k = 4 ∧
      pieceR c' d = (posR c u, posR c v) ∧
      (∀ r, ¬ (d ≤ r ∧ r < d + 4) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  simp only at hu hv1 hv2
  unfold putPiece
  exec_block
  refine ⟨⋄, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · ϴ pieceR, posR, Prod.mk.injEq, WPos.mk.injEq
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [upd] <;> split_ifs <;> first | rfl | omega
  · simp only [upd]; split_ifs <;> first | rfl | omega

theorem selLeaf_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    {L hx hy z N S Cn : ℕ} (hd : SelDisj L hx hy z N S Cn) (hNS : N + 4 ≤ S ∨ S + 4 ≤ N)
    (hC : Cn < N ∨ N + 4 ≤ Cn) (hC' : Cn < S ∨ S + 4 ≤ Cn) (tl : List (End × End))
    (htl : tl.length ≤ 2) :
    ∃ c' k, Exec P W (selLeaf L hx hy z N S Cn tl) c c' k ∧ k ≤ 9 ∧
      PiecesAt c' N S Cn (tl.map fun e => (posR c (End.regs L hx hy z e.1),
        posR c (End.regs L hx hy z e.2))) ∧
      (∀ r, r ≠ Cn → ¬ (N ≤ r ∧ r < N + 4) → ¬ (S ≤ r ∧ r < S + 4) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ne : ∀ e : End, ∀ o, (o = Cn ∨ (N ≤ o ∧ o < N + 4) ∨ (S ≤ o ∧ o < S + 4)) →
      (End.regs L hx hy z e).1 ≠ o ∧ (End.regs L hx hy z e).2 ≠ o := hd
  match tl, htl with
  | [], _ =>
    unfold selLeaf
    exec_block
    · omega
    · refine ⟨⋄, ⟨by simp, by simp, by simp, by simp⟩, fun r h1 _ _ => by simp [upd, h1],
        rfl, rfl, rfl, rfl⟩
  | [p], _ =>
    obtain ⟨u, v⟩ := p
    obtain ⟨c₁, k₁, e₁, hk₁, p₁, r₁, m₁, rr₁, rm₁, o₁⟩ := putPiece_exec (P := P) c hw (d := N)
      (u := End.regs L hx hy z u) (v := End.regs L hx hy z v)
      (ne u N (Or.inr (Or.inl ⟨le_refl _, ⋄⟩))).2
      ⟨(ne v N (Or.inr (Or.inl ⟨le_refl _, ⋄⟩))).1,
        (ne v (N + 1) (Or.inr (Or.inl ⟨⋄, by omega⟩))).1⟩
      ⟨(ne v N (Or.inr (Or.inl ⟨le_refl _, ⋄⟩))).2,
        (ne v (N + 1) (Or.inr (Or.inl ⟨⋄, by omega⟩))).2,
        (ne v (N + 2) (Or.inr (Or.inl ⟨⋄, by omega⟩))).2⟩
    have e₂ := Exec.constN (P := P) e₁.wb_right Cn 1 (⋄)
    refine ⟨_, _, .seq e₁ (Exec.block_cons e₂ (Exec.block_nil e₂.wb_right)), ⋄,
      ⟨✓, by simp, fun q hq => ?_, by simp⟩, fun r h1 h2 _ => ?_, m₁, rr₁, rm₁, o₁⟩
    · simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hq
      subst hq
      Ξ ← p₁
      ϴ pieceR, posR
      have : Cn ≠ N ∧ Cn ≠ N + 1 ∧ Cn ≠ N + 2 ∧ Cn ≠ N + 3 := ⋄
      Θ upd, this.1.symm, this.2.1.symm, this.2.2.1.symm, this.2.2.2.symm
    · ϴ upd, h1, ↓reduceIte
      exact r₁ r h2
  | [p, q], _ =>
    obtain ⟨u, v⟩ := p
    obtain ⟨u', v'⟩ := q
    obtain ⟨c₁, k₁, e₁, hk₁, p₁, r₁, m₁, rr₁, rm₁, o₁⟩ := putPiece_exec (P := P) c hw (d := N)
      (u := End.regs L hx hy z u) (v := End.regs L hx hy z v)
      (ne u N (Or.inr (Or.inl ⟨le_refl _, ⋄⟩))).2
      ⟨(ne v N (Or.inr (Or.inl ⟨le_refl _, ⋄⟩))).1,
        (ne v (N + 1) (Or.inr (Or.inl ⟨⋄, by omega⟩))).1⟩
      ⟨(ne v N (Or.inr (Or.inl ⟨le_refl _, ⋄⟩))).2,
        (ne v (N + 1) (Or.inr (Or.inl ⟨⋄, by omega⟩))).2,
        (ne v (N + 2) (Or.inr (Or.inl ⟨⋄, by omega⟩))).2⟩
    obtain ⟨c₂, k₂, e₂, hk₂, p₂, r₂, m₂, rr₂, rm₂, o₂⟩ := putPiece_exec (P := P) c₁ e₁.wb_right
      (d := S) (u := End.regs L hx hy z u') (v := End.regs L hx hy z v')
      (ne u' S (Or.inr (Or.inr ⟨le_refl _, ⋄⟩))).2
      ⟨(ne v' S (Or.inr (Or.inr ⟨le_refl _, ⋄⟩))).1,
        (ne v' (S + 1) (Or.inr (Or.inr ⟨⋄, by omega⟩))).1⟩
      ⟨(ne v' S (Or.inr (Or.inr ⟨le_refl _, ⋄⟩))).2,
        (ne v' (S + 1) (Or.inr (Or.inr ⟨⋄, by omega⟩))).2,
        (ne v' (S + 2) (Or.inr (Or.inr ⟨⋄, by omega⟩))).2⟩
    have e₃ := Exec.constN (P := P) e₂.wb_right Cn 2 (⋄)
    have keep : ∀ e : End, posR c₁ (End.regs L hx hy z e) = posR c (End.regs L hx hy z e) := by
      intro e
      have h1 := ne e N (Or.inr (Or.inl ⟨le_refl _, ⋄⟩))
      have h2 := ne e (N + 1) (Or.inr (Or.inl ⟨⋄, ⋄⟩))
      have h3 := ne e (N + 2) (Or.inr (Or.inl ⟨⋄, ⋄⟩))
      have h4 := ne e (N + 3) (Or.inr (Or.inl ⟨⋄, ⋄⟩))
      ϴ posR, WPos.mk.injEq
      exact ⟨r₁ _ (⋄), r₁ _ (by omega)⟩
    refine ⟨_, _, .seq e₁ (.seq e₂ (Exec.block_cons e₃ (Exec.block_nil e₃.wb_right))),
      ⋄, ⟨by simp, by simp, fun q hq => ?_, fun q hq => ?_⟩, fun r h1 h2 h3 => ?_,
      m₂.trans m₁, rr₂.trans rr₁, rm₂.trans rm₁, o₂.trans o₁⟩
    · simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hq
      subst hq
      Ξ ← p₁
      ϴ pieceR, posR, Prod.mk.injEq, WPos.mk.injEq
      have : Cn ≠ N ∧ Cn ≠ N + 1 ∧ Cn ≠ N + 2 ∧ Cn ≠ N + 3 := ⋄
      simp only [upd, ↓reduceIte, this.1.symm, this.2.1.symm, this.2.2.1.symm,
        this.2.2.2.symm]
      refine ⟨⟨r₂ _ (⋄), r₂ _ (by omega)⟩, r₂ _ (by omega), r₂ _ (by omega)⟩
    · simp only [List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hq
      subst hq
      Ξ ← keep u', ← keep v', ← p₂
      ϴ pieceR, posR, Prod.mk.injEq, WPos.mk.injEq
      have : Cn ≠ S ∧ Cn ≠ S + 1 ∧ Cn ≠ S + 2 ∧ Cn ≠ S + 3 := ⋄
      simp only [upd, ↓reduceIte, this.1.symm, this.2.1.symm, this.2.2.1.symm,
        this.2.2.2.symm, and_self]
    · ϴ upd, h1, ↓reduceIte
      Ξ r₂ r h3, r₁ r h2

/-- The pieces of the selection, as walk positions read in `c`. -/
def selPos (c : Config) (L hx hy z : ℕ) (tl : List (End × End)) : List (WPos × WPos) :=
  tl.map fun e => (posR c (End.regs L hx hy z e.1), posR c (End.regs L hx hy z e.2))

/-- **The selection tree** computes the pieces of `selT` at the bits of its registers. -/
theorem selB_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    {L hx hy z N S Cn hpA hpB c1 c2 c3 c4 c5 c6 : ℕ} (hd : SelDisj L hx hy z N S Cn)
    (hNS : N + 4 ≤ S ∨ S + 4 ≤ N) (hC : Cn < N ∨ N + 4 ≤ Cn) (hC' : Cn < S ∨ S + 4 ≤ Cn)
    (hz : c.nreg z = 0) (b1 : c.nreg c1 ≤ 1) (b2 : c.nreg c2 ≤ 1) (b3 : c.nreg c3 ≤ 1)
    (b4 : c.nreg c4 ≤ 1) (b5 : c.nreg c5 ≤ 1) (b6 : c.nreg c6 ≤ 1) :
    ∃ c' k, Exec P W (selB L hx hy z N S Cn hpA hpB c1 c2 c3 c4 c5 c6) c c' k ∧ k ≤ 24 ∧
      PiecesAt c' N S Cn (selPos c L hx hy z (selT (decide (c.nreg hpA < c.nreg hpB))
        (decide (c.nreg c1 = 1)) (decide (c.nreg c2 = 1)) (decide (c.nreg c3 = 1))
        (decide (c.nreg c4 = 1)) (decide (c.nreg c5 = 1)) (decide (c.nreg c6 = 1)))) ∧
      (∀ r, r ≠ Cn → ¬ (N ≤ r ∧ r < N + 4) → ¬ (S ≤ r ∧ r < S + 4) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have leaf := fun (tl : List (End × End)) (htl : tl.length ≤ 2) =>
    selLeaf_exec (P := P) c hw hW hd hNS hC hC' tl htl
  have t : ∀ {r : ℕ}, c.nreg r ≤ 1 → (c.nreg z < c.nreg r ↔ c.nreg r = 1) := fun h => ⋄
  unfold selB
  simp only
  by_cases hp : c.nreg hpA < c.nreg hpB
  · have hpd : decide (c.nreg hpA < c.nreg hpB) = true := ⊚ hp
    Ξ hpd
    by_cases q1 : c.nreg c1 = 1
    · have d1 : decide (c.nreg c1 = 1) = true := ⊚ q1
      by_cases q2 : c.nreg c2 = 1
      · have d2 : decide (c.nreg c2 = 1) = true := ⊚ q2
        by_cases q3 : c.nreg c3 = 1
        · have d3 : decide (c.nreg c3 = 1) = true := ⊚ q3
          obtain ⟨c', k, ex, hk, h⟩ := leaf [(.Y, .X)] (✓)
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_true ((t b1).2 q1) (.ifLtN_true ((t b2).2 q2)
            (.ifLtN_true ((t b3).2 q3) ex))), ⋄, ?_⟩
          rw [d1, d2, d3]; exact h
        · have d3 : decide (c.nreg c3 = 1) = false := ⊚ q3
          obtain ⟨c', k, ex, hk, h⟩ := leaf [(.Y, .B)] (✓)
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_true ((t b1).2 q1) (.ifLtN_true ((t b2).2 q2)
            (.ifLtN_false (fun h' => q3 ((t b3).1 h')) ex))), ⋄, ?_⟩
          rw [d1, d2, d3]; exact h
      · have d2 : decide (c.nreg c2 = 1) = false := ⊚ q2
        obtain ⟨c', k, ex, hk, h⟩ := leaf [] (✓)
        refine ⟨c', _, .ifLtN_true hp (.ifLtN_true ((t b1).2 q1)
          (.ifLtN_false (fun h' => q2 ((t b2).1 h')) ex)), ⋄, ?_⟩
        rw [d1, d2]; exact h
    · have d1 : decide (c.nreg c1 = 1) = false := ⊚ q1
      have n1 : ¬ c.nreg z < c.nreg c1 := fun h' => q1 ((t b1).1 h')
      by_cases q4 : c.nreg c4 = 1
      · have d4 : decide (c.nreg c4 = 1) = true := ⊚ q4
        by_cases q5 : c.nreg c5 = 1
        · have d5 : decide (c.nreg c5 = 1) = true := ⊚ q5
          obtain ⟨c', k, ex, hk, h⟩ := leaf [(.A, .X), (.Y, .B)] (✓)
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_true ((t b4).2 q4)
            (.ifLtN_true ((t b5).2 q5) ex))), ⋄, ?_⟩
          rw [d1, d4, d5]; exact h
        · have d5 : decide (c.nreg c5 = 1) = false := ⊚ q5
          obtain ⟨c', k, ex, hk, h⟩ := leaf [(.A, .X)] (✓)
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_true ((t b4).2 q4)
            (.ifLtN_false (fun h' => q5 ((t b5).1 h')) ex))), ⋄, ?_⟩
          rw [d1, d4, d5]; exact h
      · have d4 : decide (c.nreg c4 = 1) = false := ⊚ q4
        have n4 : ¬ c.nreg z < c.nreg c4 := fun h' => q4 ((t b4).1 h')
        by_cases q6 : c.nreg c6 = 1
        · have d6 : decide (c.nreg c6 = 1) = true := ⊚ q6
          by_cases q2 : c.nreg c2 = 1
          · have d2 : decide (c.nreg c2 = 1) = true := ⊚ q2
            obtain ⟨c', k, ex, hk, h⟩ := leaf [(.Y, .B)] (✓)
            refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_false n4
              (.ifLtN_true ((t b6).2 q6) (.ifLtN_true ((t b2).2 q2) ex)))), ⋄, ?_⟩
            rw [d1, d4, d6, d2]; exact h
          · have d2 : decide (c.nreg c2 = 1) = false := ⊚ q2
            obtain ⟨c', k, ex, hk, h⟩ := leaf [] (✓)
            refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_false n4
              (.ifLtN_true ((t b6).2 q6) (.ifLtN_false (fun h' => q2 ((t b2).1 h')) ex)))),
              ⋄, ?_⟩
            rw [d1, d4, d6, d2]; exact h
        · have d6 : decide (c.nreg c6 = 1) = false := ⊚ q6
          obtain ⟨c', k, ex, hk, h⟩ := leaf [(.A, .B)] (✓)
          refine ⟨c', _, .ifLtN_true hp (.ifLtN_false n1 (.ifLtN_false n4
            (.ifLtN_false (fun h' => q6 ((t b6).1 h')) ex))), ⋄, ?_⟩
          rw [d1, d4, d6]; exact h
  · have hpd : decide (c.nreg hpA < c.nreg hpB) = false := ⊚ hp
    Ξ hpd
    obtain ⟨c', k, ex, hk, h⟩ := leaf [(.A, .B)] (✓)
    exact ⟨c', _, .ifLtN_false hp ex, ⋄, h⟩

/-! ## A sequence of comparisons -/

/-- A comparison `(eu, hu, ev, hv, d)`: `d := [(eu, ibv hu) < (ev, ibv hv)]`. -/
abbrev Cmp := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The comparisons one after the other. -/
def kltSeq (z : ℕ) : List Cmp → Stmt
  | [] => .skip
  | (eu, hu, ev, hv, d) :: t => .seq (kltB eu hu ev hv d z) (kltSeq z t)

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

theorem kltSeq_exec {P : Polygon} {W : ℕ} (hW : 1 ≤ W) (z : ℕ) :
    ∀ (ts : List Cmp) (c : Config), WordsBounded W c → c.nreg z = 0 → CmpOK z ts →
      ∃ c' k, Exec P W (kltSeq z ts) c c' k ∧ k ≤ 9 * ts.length ∧
        (∀ t ∈ ts, BitIs c' t.2.2.2.2 (LexLt (c.nreg t.1) (ibv (c.nreg t.2.1))
          (c.nreg t.2.2.1) (ibv (c.nreg t.2.2.2.1)))) ∧ FrameB (Bouts ts) c c'
  | [], c, hw, _, _ => ⟨c, 0, .skip hw, ✓, ✓, FrameB.refl _ _⟩
  | (eu, hu, ev, hv, d) :: t, c, hw, hz, ⟨hzo, hnd, hin⟩ => by
    have hd : d ∉ cmpOuts t := by
      ϴ' cmpOuts, List.map_cons, List.nodup_cons at hnd; exact hnd.1
    have hok : CmpOK z t := by
      refine ⟨fun h => hzo ?_, (List.nodup_cons.1 hnd).2, fun u hu' => ?_⟩
      · ϴ' cmpOuts, List.map_cons, List.mem_cons at h ⊢
        exact Or.inr h
      · obtain ⟨a1, a2, a3, a4⟩ := hin u (List.mem_cons_of_mem _ hu')
        ϴ' cmpOuts, List.map_cons, List.mem_cons, not_or at a1 a2 a3 a4 ⊢
        exact ⟨a1.2, a2.2, a3.2, a4.2⟩
    obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := kltB_exec (P := P) c hw hW eu hu ev hv d z hz
    have hzd : z ≠ d := by
      intro h; apply hzo; rw [h]; Θ cmpOuts
    have z₁ : c₁.nreg z = 0 := by
      have g : Bone d z = false := ⊚ Bone, hzd
      rw [f₁.1 z g]; exact hz
    obtain ⟨c₂, k₂, e₂, hk₂, b₂, f₂⟩ := kltSeq_exec hW z t c₁ e₁.wb_right z₁ hok
    have keep1 : ∀ r, r ∉ cmpOuts ((eu, hu, ev, hv, d) :: t) → c₂.nreg r = c.nreg r := by
      intro r hr
      ϴ' cmpOuts, List.map_cons, List.mem_cons, not_or at hr
      have g2 : Bouts t r = false := by
        simp only [Bouts, List.contains_eq_mem, decide_eq_false_iff_not]; exact hr.2
      have g1 : Bone d r = false := ⊚ Bone, hr.1
      Ξ f₂.1 r g2, f₁.1 r g1
    refine ⟨c₂, _, .seq e₁ e₂, by simp only [List.length_cons]; omega, fun u hu' => ?_, ?_⟩
    · rcases List.mem_cons.1 hu' with rfl | hu'
      · refine b₁.of_eq (f₂.1 _ ?_)
        simp only [Bouts, List.contains_eq_mem, decide_eq_false_iff_not]; exact hd
      · have := b₂ u hu'
        obtain ⟨a1', a2', a3', a4'⟩ := hin u (List.mem_cons_of_mem _ hu')
        ϴ' cmpOuts, List.map_cons, List.mem_cons, not_or at a1' a2' a3' a4'
        rwa [f₁.1 _ (⊚ Bone, a1'.1), f₁.1 _ (⊚ Bone, a2'.1),
          f₁.1 _ (⊚ Bone, a3'.1), f₁.1 _ (⊚ Bone, a4'.1)] at this
    · refine ⟨fun r hr => ?_, fun r hr => ?_, f₂.2.2.1.trans f₁.2.2.1,
        f₂.2.2.2.1.trans f₁.2.2.2.1, f₂.2.2.2.2.trans f₁.2.2.2.2⟩
      · ϴ' Bouts, List.contains_eq_mem, decide_eq_false_iff_not at hr
        exact keep1 r hr
      · simp only [Bouts, List.contains_eq_mem, decide_eq_false_iff_not, cmpOuts,
          List.map_cons, List.mem_cons, not_or] at hr
        have g2 : Bouts t r = false := by
          simp only [Bouts, List.contains_eq_mem, decide_eq_false_iff_not]; exact hr.2
        have g1 : Bone d r = false := ⊚ Bone, hr.1
        Ξ f₂.2.1 r g2, f₁.2.1 r g1

end

end ShotList

end Chazelle.Core
