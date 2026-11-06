module

public import Chazelle.Core.SweepPrimDir

/-!
# Sweep RAM primitives (WP-D2), part 6: `leftSec`

`leftSec` (design-merge-v2 §9.6 item 3): for a walk position `x = (e, h)` of `chainModel C` and a
direction code `σ`, the bit of `sideLeft W e (param x) (rayPt (pos x) (dirOf σ) 1)` — the ray
direction points into the open left sector of the walk at `x` (the query precondition, and the
sector test of `leave_cases`).

Cases (`leftSec_math`):

* **inside an edge** (`0 < param x`): the left sector is the open left half-plane of the edge,
  so the bit is the sign test `dirOf σ · (y_b - y_a) < 0` of the edge direction
  (`sideLeft_interior`), i.e. `turnCode (dirCode e) σ = 1` (`interior_bit`);
* **at a walk vertex** (`param x = 0`, which the machine decides by the height code, the edge
  direction and one height comparison: `param_eq_zero_iff`): the sector procedure `secAt` of
  the tour vertex `e - 6`.

Positions on the box block are inside their edge because the point is strictly inside the height
range of the box (`box_param_pos`, from the input condition `|y| < radius`).
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf sidePt)

@[expose] public section

/-! ## Mathematics -/

/-- The point of a walk position is the walk point at its parameter. -/
theorem pos_eq_sidePt (M : Model) (Q : Polygon) (x : WPos) :
    M.pos Q x = sidePt M.W x.edge (M.param Q x) := rfl

/-- **When the parameter vanishes**: height code `0`, a horizontal edge, or the height of the start
vertex. -/
theorem param_eq_zero_iff (M : Model) (Q : Polygon) (x : WPos) :
    M.param Q x = 0 ↔ (x.hgt = 0 ∨ (M.wa x.edge).2 = (M.wb x.edge).2 ∨
      (Q.vtx (x.hgt - 1)).2 = (M.wa x.edge).2) := by
  unfold Model.param
  rcases x with ⟨e, h⟩
  cases h with
  | zero => simp
  | succ h =>
    simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or]
    split_ifs with hh
    · simp [hh]
    · rw [div_eq_zero_iff, sub_eq_zero, sub_eq_zero]
      constructor
      · rintro (h1 | h1)
        · exact Or.inr h1
        · exact absurd h1.symm hh
      · rintro (h1 | h1)
        · exact absurd h1 hh
        · exact Or.inl h1

/-- A positive parameter lies on a non-horizontal edge. -/
theorem ne_of_param_pos {M : Model} {Q : Polygon} {x : WPos} (h : 0 < M.param Q x) :
    (M.wa x.edge).2 ≠ (M.wb x.edge).2 := fun he =>
  (ne_of_gt h) ((param_eq_zero_iff M Q x).2 (Or.inr (Or.inl he)))

/-- **The left sector inside an edge** for a horizontal direction. -/
theorem sideLeft_interior {W : Polygon} {p : ℕ} {t s : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hne : (W.vtx p).2 ≠ (W.vtx ((p + 1) % W.n)).2) :
    sideLeft W p t (Visibility.rayPt (sidePt W p t) s 1) ↔
      s * ((W.vtx ((p + 1) % W.n)).2 - (W.vtx p).2) < 0 := by
  have hne' : W.vtx p ≠ W.vtx ((p + 1) % W.n) := fun h => hne (by rw [h])
  rw [Chazelle.Chain.sideLeft_edge hne' ⟨ht, ht1⟩]
  unfold sidePt
  simp only [det, Visibility.rayPt, Geometry.lerp_fst, Geometry.lerp_snd]
  constructor <;> intro h <;> nlinarith

/-- The interior sign test is the turning code `1`. -/
theorem interior_bit (M : Model) (e σ : ℕ) :
    dirOf σ * ((M.W.vtx ((e + 1) % M.W.n)).2 - (M.W.vtx e).2) < 0 ↔
      turnCode (dirCode M e) σ = 1 := by
  unfold turnCode dirCode Model.wa Model.wb dirOf
  split_ifs <;> first
    | (constructor <;> intro h <;> first | rfl | omega | (exfalso; linarith) | linarith)
    | (constructor <;> intro h <;> (exfalso; first | omega | linarith))

/-- **Positions on the box block are inside their edge** when the point is strictly inside the
height range of the box. -/
theorem box_param_pos (C : Chain) {Q : Polygon} {x : WPos} (he : x.edge < 6)
    (hp : 0 ≤ (chainModel C).param Q x)
    (hy : |((chainModel C).pos Q x).2| < C.radius) : 0 < (chainModel C).param Q x := by
  rcases hp.lt_or_eq with h | h
  · exact h
  exfalso
  rw [pos_eq_sidePt, ← h] at hy
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := C.sidePt_box C.sideBeta 0
  have hR := C.radius_pos
  have hw : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [hw] at hy
  rcases x with ⟨e, k⟩
  simp only at he hy
  interval_cases e
  · rw [h0] at hy; simp [abs_of_pos hR] at hy
  · rw [h1] at hy; simp [abs_of_pos hR] at hy
  · rw [h2] at hy; simp [abs_of_pos hR] at hy
  · rw [h3] at hy; simp [abs_of_pos hR] at hy
  · rw [h4] at hy; simp [abs_of_pos hR] at hy
  · rw [h5] at hy; simp [abs_of_pos hR] at hy

/-! ## The machine -/

/-- The interior bit: `50210 := [turnCode (10502) (50203) = 1]`. -/
def intOut : Stmt :=
  .seq turnOut (.ifLtN 50210 50032 (.instr (.constN 50210 0))
    (.ifLtN 50032 50210 (.instr (.constN 50210 0)) (.instr (.constN 50210 1))))

theorem intOut_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    (h32 : c.nreg 50032 = 1) (hd : c.nreg 10502 ≤ 2) :
    ∃ c' k, Exec P W intOut c c' k ∧ k ≤ 14 ∧
      BitIs c' 50210 (turnCode (c.nreg 10502) (c.nreg 50203) = 1) ∧
      ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := by
  obtain ⟨c₁, k₁, e₁, hk₁, o₁, r₁⟩ := turnOut_exec (P := P) c hw hW h32 hd
  have w₁ := e₁.wb_right
  have p₁ : c₁.nreg 50032 = 1 := by rw [r₁ _ (by decide), h32]
  set t := turnCode (c.nreg 10502) (c.nreg 50203)
  have fin : ∀ v, v ≤ 1 → (v = 1 ↔ t = 1) → ∃ c' k, Exec P W (.instr (.constN 50210 v)) c₁ c' k ∧
      k = 1 ∧ BitIs c' 50210 (t = 1) ∧ ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := fun v hv hvt =>
    ⟨_, 1, Exec.constN w₁ _ _ (by omega), rfl, ⟨by simp [hv], by simp [hvt]⟩,
      fun r hr => by simp [hr, r₁ r hr]⟩
  by_cases h0 : t < 1
  · obtain ⟨c', k, e, hk, h1, h2⟩ := fin 0 (by omega) (by omega)
    exact ⟨c', _, .seq e₁ (.ifLtN_true (by rwa [o₁, p₁]) e), by omega, h1, h2⟩
  by_cases h2 : 1 < t
  · obtain ⟨c', k, e, hk, h1, h3⟩ := fin 0 (by omega) (by omega)
    exact ⟨c', _, .seq e₁ (.ifLtN_false (by rwa [o₁, p₁])
      (.ifLtN_true (by rwa [o₁, p₁]) e)), by omega, h1, h3⟩
  · obtain ⟨c', k, e, hk, h1, h3⟩ := fin 1 le_rfl (by omega)
    exact ⟨c', _, .seq e₁ (.ifLtN_false (by rwa [o₁, p₁])
      (.ifLtN_false (by rwa [o₁, p₁]) e)), by omega, h1, h3⟩

/-- The vertex case: the sector procedure at the tour vertex `e - 6`, answer copied. -/
def vtxOut : Stmt :=
  .seq (.instr (.subN 50121 50201 50081)) (.seq secAt (.instr (.copyN 50210 50110)))

/-- **`leftSec`**: edge in `50201`, height code in `50202`, direction code in `50203`; answer bit
in `50210`. -/
def leftSecCore : Stmt :=
  .seq (.instr (.copyN 50002 50201)) (.seq dirAt
    (.ifLtN 50201 50081 intOut
      (.ifLtN 50202 50032 vtxOut
        (.ifLtN 10502 50032 vtxOut
          (.seq (.instr (.subN 50120 50201 50081)) (.seq (tvLoad 50133)
            (.seq (block [.constN 50160 0, .subN 50161 50202 50032])
              (.seq (kbit 50133 50160 50133 1 50170) (.seq (kbit 50160 50133 50160 1 50171)
                (.ifLtN 50170 50032 (.ifLtN 50171 50032 vtxOut intOut) intOut))))))))))

/-- **The primitive `leftSec`.** -/
def leftSec : Stmt := .seq pHead leftSecCore

theorem wr_leftSec : wr Bprim leftSec = true := by decide

/-- The vertex case of `leftSec`. -/
theorem vtxOut_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e : ℕ} (h01 : c.nreg 50201 = e) (he6 : 6 ≤ e)
    (he : e < 2 * C.m + 7) :
    ∃ c' k, Exec P W vtxOut c c' k ∧ k ≤ 81 * H.length + 3202 ∧
      BitIs c' 50210 (sideLeft (chainModel C).W e 0
        (Visibility.rayPt ((chainModel C).W.vtx e) (dirOf (c.nreg 50203)) 1)) := by
  have e₁ := Exec.subN (P := P) hE.wb 50121 50201 50081
  set c₁ : Config := { c with nreg := upd c.nreg 50121 (c.nreg 50201 - c.nreg 50081) } with hc₁
  have hE₁ : CEnv P W H C c₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50121)
    (by decide)) e₁.wb_right (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, -, b₂⟩ := secAt_exec c₁ hE₁ (i := e - 6)
    (by rw [hc₁]; simp [h01, hE.r81]) (by omega)
  have e₃ := Exec.copyN (P := P) e₂.wb_right 50210 50110
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), by omega, ?_⟩
  have s₁ : c₁.nreg 50203 = c.nreg 50203 := by rw [hc₁]; simp
  rw [s₁, show e - 6 + 6 = e by omega] at b₂
  exact b₂.of_eq (by simp)

/-- The input condition of `leftSec`: a proper position of the walk whose point is strictly
inside the height range of the box. -/
def LeftIn (P : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop :=
  c.nreg 50201 < (chainModel C).W.n ∧
    ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg 50201, c.nreg 50202⟩ ∧
    |((chainModel C).pos (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩).2| < C.radius

/-- The output condition of `leftSec`. -/
def LeftOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  BitIs c' 50210 (sideLeft (chainModel C).W (c.nreg 50201)
    ((chainModel C).param (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩)
    (Visibility.rayPt ((chainModel C).pos (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩)
      (dirOf (c.nreg 50203)) 1))

/-- **Contract of `leftSec`** (at most `17400` steps): the bit of "the direction `dirOf σ` points
into the open left sector of the walk at the position `(e, h)`". -/
theorem leftSec_meets : Meets leftSec primBands (PrimPre LeftIn) (PrimPost LeftOut)
    (fun _ _ => 17400) := by
  refine prim_meets (K := 16600) (fun r h => h) wr_leftSec ?_
  intro P W H C c₀ c _hC hE ⟨hen, ⟨hp0, hp1, hhn⟩, hy⟩ hinp
  have i01 := hinp 50201 (by norm_num) (by norm_num)
  have i02 := hinp 50202 (by norm_num) (by norm_num)
  unfold LeftOut
  set e := c₀.nreg 50201
  set hc := c₀.nreg 50202
  set σ := c₀.nreg 50203
  set M := chainModel C
  set x : WPos := ⟨e, hc⟩ with hx
  have hn : M.W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hlen := hE.hlen
  have hW := hE.hW
  -- the edge direction
  have e₁ := Exec.copyN (P := P) hE.wb 50002 50201
  set c₁ : Config := { c with nreg := upd c.nreg 50002 (c.nreg 50201) } with hc₁
  have hE₁ : CEnv P W H C c₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50002)
    (by decide)) e₁.wb_right (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, d₂⟩ := dirAt_exec c₁ hE₁ (e := e)
    (by rw [hc₁]; simp [i01]) (by omega)
  have w₂ := e₂.wb_right
  have g₂ : ∀ r, 50200 ≤ r → r < 50210 → c₂.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [f₂.1 r (by simp only [Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
      hc₁]
    simp only
    rw [upd_other _ _ _ (by omega), hinp r h1 h2]
  have q01 := g₂ 50201 (by norm_num) (by norm_num)
  have q02 := g₂ 50202 (by norm_num) (by norm_num)
  have q03 := g₂ 50203 (by norm_num) (by norm_num)
  have hd2 : c₂.nreg 10502 ≤ 2 := by rw [d₂]; exact dirCode_le_two _ _
  -- the interior case, shared
  have interior : ∀ c₃ : Config, CEnv P W H C c₃ → c₃.nreg 10502 = dirCode M e →
      c₃.nreg 50203 = σ → 0 < M.param (Qof P) x →
      ∃ c' k, Exec P W intOut c₃ c' k ∧ k ≤ 14 ∧
        BitIs c' 50210 (sideLeft M.W e (M.param (Qof P) x)
          (Visibility.rayPt (M.pos (Qof P) x) (dirOf σ) 1)) := by
    intro c₃ hE₃ d₃ s₃ hpos
    obtain ⟨c', k, ex, hk, b, -⟩ := intOut_exec (P := P) c₃ hE₃.wb (by omega) hE₃.r32
      (by rw [d₃]; exact dirCode_le_two _ _)
    refine ⟨c', k, ex, hk, b.congr ?_⟩
    rw [d₃, s₃, ← interior_bit, pos_eq_sidePt]
    exact (sideLeft_interior hpos hp1 (ne_of_param_pos hpos)).symm
  -- the vertex case, shared
  have vertex : ∀ c₃ : Config, CEnv P W H C c₃ → c₃.nreg 50201 = e → c₃.nreg 50203 = σ →
      6 ≤ e → M.param (Qof P) x = 0 →
      ∃ c' k, Exec P W vtxOut c₃ c' k ∧ k ≤ 81 * H.length + 3202 ∧
        BitIs c' 50210 (sideLeft M.W e (M.param (Qof P) x)
          (Visibility.rayPt (M.pos (Qof P) x) (dirOf σ) 1)) := by
    intro c₃ hE₃ e₃ s₃ h6 h0
    obtain ⟨c', k, ex, hk, b⟩ := vtxOut_exec c₃ hE₃ e₃ h6 (by omega)
    refine ⟨c', k, ex, hk, ?_⟩
    rwa [h0, pos_eq_sidePt, h0, Chazelle.Chain.sidePt_zero, ← s₃]
  by_cases hsm : e < 6
  · -- the box block
    have hpos : 0 < M.param (Qof P) x := box_param_pos C hsm hp0 hy
    obtain ⟨c', k, ex, hk, b⟩ := interior c₂ hE₂ d₂ q03 hpos
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_true (by rwa [q01, hE₂.r81]) ex)),
      by omega, b⟩
  have t1 : ¬ c₂.nreg 50201 < c₂.nreg 50081 := by rwa [q01, hE₂.r81]
  by_cases hh0 : hc < 1
  · obtain ⟨c', k, ex, hk, b⟩ := vertex c₂ hE₂ q01 q03 (by omega)
      ((param_eq_zero_iff _ _ _).2 (Or.inl (by simp [hx]; omega)))
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_true
      (by rwa [q02, hE₂.r32]) ex))), by omega, b⟩
  have t2 : ¬ c₂.nreg 50202 < c₂.nreg 50032 := by rwa [q02, hE₂.r32]
  by_cases hd0 : c₂.nreg 10502 < 1
  · have hdir : dirCode M e = 0 := by rw [← d₂]; omega
    have hhor : (M.wa x.edge).2 = (M.wb x.edge).2 := by
      unfold dirCode at hdir
      split_ifs at hdir with h1 h2
      exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    obtain ⟨c', k, ex, hk, b⟩ := vertex c₂ hE₂ q01 q03 (by omega)
      ((param_eq_zero_iff _ _ _).2 (Or.inr (Or.inl hhor)))
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true
      (by rwa [hE₂.r32]) ex)))), by omega, b⟩
  have t3 : ¬ c₂.nreg 10502 < c₂.nreg 50032 := by rwa [hE₂.r32]
  -- the start vertex of the edge and the height vertex
  have e₃ := Exec.subN (P := P) w₂ 50120 50201 50081
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 (c₂.nreg 50201 - c₂.nreg 50081) }
    with hc₃
  have hE₃ : CEnv P W H C c₃ := hE₂.frame (exec_frameB e₃ (B := fun r => r == 50120)
    (by decide)) e₃.wb_right (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sa, ia, la, va, -⟩ := tvLoad_exec c₃ hE₃ (i := e - 6)
    (by rw [hc₃]; simp only [upd_same]; rw [q01, hE₂.r81]) (by omega)
    (dst := 50133) (by norm_num)
  have w₄ := e₄.wb_right
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.constN 50160 0,
      .subN 50161 50202 50032]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 50160 = 0 ∧
        c₅.nreg 50161 = hc - 1 ∧ ∀ r, r ≠ 50160 → r ≠ 50161 → c₅.nreg r = c₄.nreg r) := by
    exec_block
    · omega
    · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 => by simp [h1, h2]⟩
      config_simp
      rw [f₄.1 50202 (by decide), f₄.1 50032 (by decide), hc₃]
      simp only
      rw [upd_other _ _ _ (by decide), upd_other _ _ _ (by decide), q02, hE₂.r32]
  obtain ⟨q60, q61, r₅⟩ := q
  have w₅ := e₅.wb_right
  have ih : SymPtIn c₅ 50160 (.vtx (hc - 1)) := ⟨q60, q61⟩
  have hhn' : hc ≤ P.n := hhn
  have lh : (SymPt.vtx (hc - 1)).Lt P.n := by show hc - 1 < P.n; omega
  have ia₅ : SymPtIn c₅ 50133 sa := symPtIn_of_eq ia fun j h1 h2 => r₅ j (by omega) (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b₆, t₆⟩ := kbit_exec (op := 1) (dst := 50170) hE.hG hW c₅ w₅
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) la lh la ia₅ ih ia₅
  have ia₆ := symPtIn_keep ia₅ f₆ (by intro j h1 h2; interval_cases j <;> decide)
  have ih₆ := symPtIn_keep ih f₆ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b₇, t₇⟩ := kbit_exec (op := 1) (dst := 50171) hE.hG hW c₆
    e₆.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lh la lh
    ih₆ ia₆ ih₆
  have w₇ := e₇.wb_right
  have hE₅ : CEnv P W H C c₅ := hE₄.keep w₅ (exec_frameB e₅ (B := fun r => r == 50160 ||
    r == 50161) (by decide)).2.2.1 (fun r hr => r₅ r (by intro h; subst h; revert hr; decide)
      (by intro h; subst h; revert hr; decide))
  have hE₆ := hE₅.frame f₆ e₆.wb_right (by decide)
  have hE₇ := hE₆.frame f₇ w₇ (by decide)
  -- registers kept since `c₂`
  have g₇ : ∀ r, r = 50201 ∨ r = 50203 ∨ r = 10502 → c₇.nreg r = c₂.nreg r := by
    intro r hr
    rw [f₇.1 r (by rcases hr with rfl | rfl | rfl <;> decide),
      f₆.1 r (by rcases hr with rfl | rfl | rfl <;> decide),
      r₅ r (by omega) (by omega), f₄.1 r (by rcases hr with rfl | rfl | rfl <;> decide), hc₃]
    simp only
    rw [upd_other _ _ _ (by omega)]
  have b70 : BitIs c₇ 50170 ((SymPt.eval (Qof P) sa).2 < ((SymPt.vtx (hc - 1)).eval (Qof P)).2) :=
    BitIs.keep ⟨b₆, t₆⟩ f₇ (by decide)
  have b71 : BitIs c₇ 50171 (((SymPt.vtx (hc - 1)).eval (Qof P)).2 < (SymPt.eval (Qof P) sa).2) :=
    ⟨b₇, t₇⟩
  rw [va, show e - 6 + 6 = e by omega] at b70 b71
  have hwa : M.wa x.edge = M.W.vtx e := rfl
  have hQ : ((SymPt.vtx (hc - 1)).eval (Qof P)) = (Qof P).vtx (x.hgt - 1) := rfl
  rw [hQ] at b70 b71
  by_cases hlt : c₇.nreg 50170 < c₇.nreg 50032
  · rw [hE₇.r32] at hlt
    have n70 : ¬ (M.W.vtx e).2 < ((Qof P).vtx (x.hgt - 1)).2 := fun h => by
      have := b70.2.2 h; omega
    by_cases hlt2 : c₇.nreg 50171 < c₇.nreg 50032
    · rw [hE₇.r32] at hlt2
      have n71 : ¬ ((Qof P).vtx (x.hgt - 1)).2 < (M.W.vtx e).2 := fun h => by
        have := b71.2.2 h; omega
      have heq : ((Qof P).vtx (x.hgt - 1)).2 = (M.wa x.edge).2 := by
        rw [hwa]; linarith [not_lt.1 n70, not_lt.1 n71]
      obtain ⟨c', k, ex, hk, b⟩ := vertex c₇ hE₇ (by rw [g₇ _ (Or.inl rfl), q01])
        (by rw [g₇ _ (Or.inr (Or.inl rfl)), q03]) (by omega)
        ((param_eq_zero_iff _ _ _).2 (Or.inr (Or.inr heq)))
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true (by rwa [hE₇.r32])
          (.ifLtN_true (by rwa [hE₇.r32]) ex))))))))))), by omega, b⟩
    · have p71 : ((Qof P).vtx (x.hgt - 1)).2 < (M.W.vtx e).2 := b71.2.1 (by
        have := b71.1; rw [hE₇.r32] at hlt2; omega)
      have hpos : 0 < M.param (Qof P) x := lt_of_le_of_ne hp0 (fun h => by
        rcases (param_eq_zero_iff _ _ _).1 h.symm with h' | h' | h'
        · simp [hx] at h'; omega
        · exact hd0 (by rw [d₂]; unfold dirCode; rw [ite_eq_right (by rw [h']; exact lt_irrefl _),
            ite_eq_right (by rw [h']; exact lt_irrefl _)]; omega)
        · rw [hwa] at h'; linarith)
      obtain ⟨c', k, ex, hk, b⟩ := interior c₇ hE₇ (by rw [g₇ _ (Or.inr (Or.inr rfl)), d₂])
        (by rw [g₇ _ (Or.inr (Or.inl rfl)), q03]) hpos
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true (by rwa [hE₇.r32])
          (.ifLtN_false hlt2 ex))))))))))), by omega, b⟩
  · have p70 : (M.W.vtx e).2 < ((Qof P).vtx (x.hgt - 1)).2 := b70.2.1 (by
      have := b70.1; rw [hE₇.r32] at hlt; omega)
    have hpos : 0 < M.param (Qof P) x := lt_of_le_of_ne hp0 (fun h => by
      rcases (param_eq_zero_iff _ _ _).1 h.symm with h' | h' | h'
      · simp [hx] at h'; omega
      · exact hd0 (by rw [d₂]; unfold dirCode; rw [ite_eq_right (by rw [h']; exact lt_irrefl _),
          ite_eq_right (by rw [h']; exact lt_irrefl _)]; omega)
      · rw [hwa] at h'; linarith)
    obtain ⟨c', k, ex, hk, b⟩ := interior c₇ hE₇ (by rw [g₇ _ (Or.inr (Or.inr rfl)), d₂])
      (by rw [g₇ _ (Or.inr (Or.inl rfl)), q03]) hpos
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
      (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_false hlt ex)))))))))), by omega, b⟩

end

end SweepPrim

end Chazelle.Core
