module

public import Chazelle.Core.SweepPrimSec

/-!
# Sweep RAM primitives (WP-D2), part 4: the left sector at a tour vertex on the RAM

`secAt` decides, for the vertex `6 + i` (`i ≤ 2m`, register `50121`) of the walk of the chain
model `chainModel C` and the direction code `σ` (register `50203`, `dirOf σ = ±1`), whether the
point `rayPt v (dirOf σ) 1` lies in the open left sector of the walk at the vertex
(`secAt_exec`); the answer bit goes to `50110`.

The neighbours of the vertex are tour vertices (`secGen`, `1 ≤ i < 2m`), or the top of the slit
(`secFirst`, `i = 0`, before the vertex; `secLast`, `i = 2m`, after it).  The top of the slit is
not a symbolic point; it lies straight above the vertex (the top of the chain), so its comparison
bits are constants and the orientation bits are comparison bits of the other neighbour.  The ten
sign bits and the direction bit are combined by the compiled formula `secBF`
(`SweepPrimBool`, `SweepPrimSec`).

Registers: slots `50130` (before), `50133` (vertex), `50136` (after); bits `50140 … 50150`
(direction, the four comparison bits of the next vertex, of the previous vertex, orientation);
the formula at `50300 …`.
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf)

@[expose] public section

/-! ## Bits -/

/-- Register `r` holds the bit of `p`. -/
def BitIs (c : Config) (r : ℕ) (p : Prop) : Prop := c.nreg r ≤ 1 ∧ (c.nreg r = 1 ↔ p)

theorem BitIs.of_eq {c c' : Config} {r r' : ℕ} {p : Prop} (h : BitIs c r p)
    (he : c'.nreg r' = c.nreg r) : BitIs c' r' p := by
  unfold BitIs at *; rw [he]; exact h

theorem BitIs.congr {c : Config} {r : ℕ} {p q : Prop} (h : BitIs c r p) (hpq : p ↔ q) :
    BitIs c r q := ⟨h.1, h.2.trans hpq⟩

theorem BitIs.dec {c : Config} {r : ℕ} {p : Prop} (h : BitIs c r p) :
    decide (c.nreg r = 1) = true ↔ p := by rw [decide_eq_true_iff]; exact h.2

theorem BitIs.const_one {c : Config} {r : ℕ} {p : Prop} (h : c.nreg r = 1) (hp : p) :
    BitIs c r p := ⟨by omega, fun _ => hp, fun _ => h⟩

theorem BitIs.const_zero {c : Config} {r : ℕ} {p : Prop} (h : c.nreg r = 0) (hp : ¬ p) :
    BitIs c r p := ⟨by omega, fun h' => by omega, fun h' => absurd h' hp⟩

theorem bk_false {r : ℕ} (h : 10500 ≤ r) : Bk r = false := by
  simp only [Bk, decide_eq_false_iff_not, not_and, not_lt]; omega

/-! ## Four comparison bits -/

/-- The four comparison bits of the point of slot `x` with the point of slot `v`: heights
`v < x`, `x < v`, abscissae `v < x`, `x < v`, into `base … base + 3`. -/
def cmp4 (v x base : ℕ) : Stmt :=
  .seq (kbit v x v 1 base) (.seq (kbit x v x 1 (base + 1))
    (.seq (kbit v x v 0 (base + 2)) (kbit x v x 0 (base + 3))))

/-- The registers written by `cmp4 _ _ base`. -/
def B4 (base r : ℕ) : Bool := Bk r || decide (base ≤ r ∧ r < base + 4)

theorem wr_cmp4 (v x base : ℕ) : wr (B4 base) (cmp4 v x base) = true := by
  have h := fun (a b d op dst : ℕ) (hd : base ≤ dst ∧ dst < base + 4) =>
    wr_mono (wr_kbit a b d op dst) (B' := B4 base) (fun r hr => by
      simp only [Bkb, Bool.or_eq_true, beq_iff_eq] at hr
      simp only [B4, Bool.or_eq_true, decide_eq_true_eq]
      rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr hd)
  simp only [cmp4, wr, h _ _ _ _ _ (by omega : base ≤ base ∧ base < base + 4),
    h _ _ _ _ _ (by omega : base ≤ base + 1 ∧ base + 1 < base + 4),
    h _ _ _ _ _ (by omega : base ≤ base + 2 ∧ base + 2 < base + 4),
    h _ _ _ _ _ (by omega : base ≤ base + 3 ∧ base + 3 < base + 4), Bool.and_self]

/-- The height of a symbolic point of `Qof P`. -/
noncomputable abbrev Ys (P : Polygon) (s : SymPt) : ℝ := (s.eval (Qof P)).2
/-- The abscissa of a symbolic point of `Qof P`. -/
noncomputable abbrev Xs (P : Polygon) (s : SymPt) : ℝ := (s.eval (Qof P)).1

/-- **Four comparison bits** (at most `964` steps). -/
theorem cmp4_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {v x base : ℕ} (hv : 10500 ≤ v) (hx : 10500 ≤ x)
    (hvb : v + 3 ≤ base) (hxb : x + 3 ≤ base) {sv sx : SymPt} (hlv : sv.Lt P.n)
    (hlx : sx.Lt P.n) (hsv : SymPtIn c v sv) (hsx : SymPtIn c x sx) :
    ∃ c' k, Exec P W (cmp4 v x base) c c' k ∧ k ≤ 964 ∧ FrameB (B4 base) c c' ∧
      BitIs c' base (Ys P sv < Ys P sx) ∧ BitIs c' (base + 1) (Ys P sx < Ys P sv) ∧
      BitIs c' (base + 2) (Xs P sv < Xs P sx) ∧ BitIs c' (base + 3) (Xs P sx < Xs P sv) := by
  have keep : ∀ {c₁ c₂ : Config} {dst : ℕ}, FrameB (Bkb dst) c₁ c₂ → base ≤ dst →
      ∀ {r : ℕ} {s : SymPt}, 10500 ≤ r → r + 3 ≤ base → SymPtIn c₁ r s → SymPtIn c₂ r s :=
    fun hf hd r s hr hrb hs => symPtIn_of_eq hs fun j h1 h2 => hf.1 j (by
      simp only [Bkb, bk_false (show 10500 ≤ j by omega), Bool.false_or, beq_eq_false_iff_ne]
      omega)
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := kbit_exec (op := 1) (dst := base) hG hW c hw hv hx hv (by omega) (by norm_num)
    hlv hlx hlv hsv hsx hsv
  have sv₁ := keep f₁ le_rfl hv hvb hsv
  have sx₁ := keep f₁ le_rfl hx hxb hsx
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, t₂⟩ := kbit_exec (op := 1) (dst := base + 1) hG hW c₁ e₁.wb_right hx hv hx (by omega)
    (by norm_num) hlx hlv hlx sx₁ sv₁ sx₁
  have sv₂ := keep f₂ (by omega) hv hvb sv₁
  have sx₂ := keep f₂ (by omega) hx hxb sx₁
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, t₃⟩ := kbit_exec (op := 0) (dst := base + 2) hG hW c₂ e₂.wb_right hv hx hv (by omega)
    (by norm_num) hlv hlx hlv sv₂ sx₂ sv₂
  have sv₃ := keep f₃ (by omega) hv hvb sv₂
  have sx₃ := keep f₃ (by omega) hx hxb sx₂
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, t₄⟩ := kbit_exec (op := 0) (dst := base + 3) hG hW c₃ e₃.wb_right hx hv hx (by omega)
    (by norm_num) hlx hlv hlx sx₃ sv₃ sx₃
  have ex : Exec P W (cmp4 v x base) c c₄ (k₁ + (k₂ + (k₃ + k₄))) :=
    .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have kp : ∀ {c₁ c₂ : Config} {dst : ℕ}, FrameB (Bkb dst) c₁ c₂ → ∀ {r : ℕ}, 10500 ≤ r →
      r ≠ dst → c₂.nreg r = c₁.nreg r := fun hf r hr hne => hf.1 r (by
        simp only [Bkb, bk_false hr, Bool.false_or, beq_eq_false_iff_ne]; exact hne)
  refine ⟨c₄, _, ex, by omega, exec_frameB ex (wr_cmp4 v x base), ?_, ?_, ?_, ⟨b₄, t₄⟩⟩
  · refine BitIs.of_eq ⟨b₁, t₁⟩ ?_
    rw [kp f₄ (by omega) (by omega), kp f₃ (by omega) (by omega), kp f₂ (by omega) (by omega)]
  · refine BitIs.of_eq ⟨b₂, t₂⟩ ?_
    rw [kp f₄ (by omega) (by omega), kp f₃ (by omega) (by omega)]
  · exact BitIs.of_eq ⟨b₃, t₃⟩ (kp f₄ (by omega) (by omega))


/-! ## Frames and preservation -/

theorem symPtIn_keep {B : ℕ → Bool} {c c' : Config} {r : ℕ} {s : SymPt} (hs : SymPtIn c r s)
    (hf : FrameB B c c') (hB : ∀ j, r ≤ j → j < r + 3 → B j = false) : SymPtIn c' r s :=
  symPtIn_of_eq hs fun j h1 h2 => hf.1 j (hB j h1 h2)

theorem BitIs.keep {B : ℕ → Bool} {c c' : Config} {r : ℕ} {p : Prop} (h : BitIs c r p)
    (hf : FrameB B c c') (hB : B r = false) : BitIs c' r p := h.of_eq (hf.1 r hB)

/-- The registers the sector procedure may write. -/
def Bsec (r : ℕ) : Bool :=
  Bk r || Bhost r || Btvi r || decide (50100 ≤ r ∧ r < 50200 ∧ r ≠ 50121) ||
    decide (50300 ≤ r ∧ r < 51000)

/-- **The ten sign bits of a corner** `a → v → b` in `50141 … 50150`. -/
def BitsOK (c : Config) (a v b : Point) : Prop :=
  BitIs c 50141 (v.2 < b.2) ∧ BitIs c 50142 (b.2 < v.2) ∧ BitIs c 50143 (v.1 < b.1) ∧
    BitIs c 50144 (b.1 < v.1) ∧ BitIs c 50145 (v.2 < a.2) ∧ BitIs c 50146 (a.2 < v.2) ∧
    BitIs c 50147 (v.1 < a.1) ∧ BitIs c 50148 (a.1 < v.1) ∧ BitIs c 50149 (0 < det a v b) ∧
    BitIs c 50150 (det a v b = 0)

/-- One index instruction keeps the environment. -/
theorem CEnv.step {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {c : Config} (hE : CEnv P W H C c)
    {i : Instr} {c' : Config} (e : Exec P W (.instr i) c c' 1)
    (hi : wr (fun r => r == 50120) (.instr i) = true) : CEnv P W H C c' :=
  hE.frame (exec_frameB e hi) e.wb_right (by decide)

/-! ## The general corner -/

/-- Three tour vertices `i - 1, i, i + 1` and their ten sign bits. -/
def secGen : Stmt :=
  .seq (.instr (.subN 50120 50121 50032)) (.seq (tvLoad 50130)
    (.seq (.instr (.copyN 50120 50121)) (.seq (tvLoad 50133)
      (.seq (.instr (.addN 50120 50121 50032)) (.seq (tvLoad 50136)
        (.seq (cmp4 50133 50136 50141) (.seq (cmp4 50133 50130 50145)
          (.seq (kbit 50130 50133 50136 2 50149) (kbit 50130 50133 50136 3 50150)))))))))

theorem wr_secGen : wr Bsec secGen = true := by decide

/-- **The ten bits at an inner tour vertex** (`1 ≤ i < 2m`). -/
theorem secGen_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {i : ℕ} (h121 : c.nreg 50121 = i) (hi1 : 1 ≤ i) (hi : i < 2 * C.m) :
    ∃ c' k, Exec P W secGen c c' k ∧ k ≤ 81 * H.length + 2600 ∧ FrameB Bsec c c' ∧
      CEnv P W H C c' ∧ BitsOK c' ((chainModel C).W.vtx ((i - 1) + 6))
        ((chainModel C).W.vtx (i + 6)) ((chainModel C).W.vtx ((i + 1) + 6)) := by
  have hG := hE.hG
  have hW := hE.hW
  -- previous vertex
  have e₁ := Exec.subN (P := P) hE.wb 50120 50121 50032
  have hE₁ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sa, ia, la, va, -⟩ := tvLoad_exec _ hE₁
    (i := i - 1) (by simp [h121, hE.r32]) (by omega) (dst := 50130) (by norm_num)
  have r121₂ : c₂.nreg 50121 = i := by rw [f₂.1 _ (by decide)]; simp [h121]
  -- the vertex
  have e₃ := Exec.copyN (P := P) e₂.wb_right 50120 50121
  have hE₃ := hE₂.step e₃ (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sv, iv, lv, vv, -⟩ := tvLoad_exec _ hE₃
    (i := i) (by simp [r121₂]) (by omega) (dst := 50133) (by norm_num)
  have ia₄ : SymPtIn c₄ 50130 sa := symPtIn_keep (symPtIn_of_eq ia fun j h1 h2 => by
    simp only [upd]; rw [ite_eq_right (by omega)]) f₄ (by intro j h1 h2; interval_cases j <;> decide)
  have r121₄ : c₄.nreg 50121 = i := by rw [f₄.1 _ (by decide)]; simp [r121₂]
  -- the next vertex
  have e₅ := Exec.addN (P := P) e₄.wb_right 50120 50121 50032
    (by rw [r121₄, hE₄.r32]; have := hE₄.NW; have := C.m_lt; have := hE₄.n_eq; omega)
  have hE₅ := hE₄.step e₅ (by decide)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, hE₆, sb, ib, lb, vb, -⟩ := tvLoad_exec _ hE₅
    (i := i + 1) (by simp [r121₄, hE₄.r32]) (by omega) (dst := 50136) (by norm_num)
  have ia₆ : SymPtIn c₆ 50130 sa := symPtIn_keep (symPtIn_of_eq ia₄ fun j h1 h2 => by
    simp only [upd]; rw [ite_eq_right (by omega)]) f₆ (by intro j h1 h2; interval_cases j <;> decide)
  have iv₆ : SymPtIn c₆ 50133 sv := symPtIn_keep (symPtIn_of_eq iv fun j h1 h2 => by
    simp only [upd]; rw [ite_eq_right (by omega)]) f₆ (by intro j h1 h2; interval_cases j <;> decide)
  -- the bits
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b1, b2, b3, b4⟩ := cmp4_exec (base := 50141) hG hW c₆
    e₆.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) lv lb iv₆ ib
  have ia₇ := symPtIn_keep ia₆ f₇ (by intro j h1 h2; interval_cases j <;> decide)
  have iv₇ := symPtIn_keep iv₆ f₇ (by intro j h1 h2; interval_cases j <;> decide)
  have ib₇ := symPtIn_keep ib f₇ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, b5, b6, b7, b8⟩ := cmp4_exec (base := 50145) hG hW c₇
    e₇.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) lv la iv₇ ia₇
  have ia₈ := symPtIn_keep ia₇ f₈ (by intro j h1 h2; interval_cases j <;> decide)
  have iv₈ := symPtIn_keep iv₇ f₈ (by intro j h1 h2; interval_cases j <;> decide)
  have ib₈ := symPtIn_keep ib₇ f₈ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, b9, t9⟩ := kbit_exec (op := 2) (dst := 50149) hG hW c₈
    e₈.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) la lv lb
    ia₈ iv₈ ib₈
  have ia₉ := symPtIn_keep ia₈ f₉ (by intro j h1 h2; interval_cases j <;> decide)
  have iv₉ := symPtIn_keep iv₈ f₉ (by intro j h1 h2; interval_cases j <;> decide)
  have ib₉ := symPtIn_keep ib₈ f₉ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, f₁₀, b10, t10⟩ := kbit_exec (op := 3) (dst := 50150) hG hW c₉
    e₉.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) la lv lb
    ia₉ iv₉ ib₉
  have ex : Exec P W secGen c c₁₀
      (1 + (k₂ + (1 + (k₄ + (1 + (k₆ + (k₇ + (k₈ + (k₉ + k₁₀))))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉ e₁₀))))))))
  have hE₇ := hE₆.frame f₇ e₇.wb_right (by decide)
  have hE₈ := hE₇.frame f₈ e₈.wb_right (by decide)
  have hE₉ := hE₈.frame f₉ e₉.wb_right (by decide)
  have hE₁₀ := hE₉.frame f₁₀ e₁₀.wb_right (by decide)
  have hlen := hE.hlen
  refine ⟨c₁₀, _, ex, by omega, exec_frameB ex wr_secGen, hE₁₀, ?_⟩
  simp only [Ys, Xs, va, vv, vb] at b1 b2 b3 b4 b5 b6 b7 b8
  have t9' := t9; have t10' := t10
  simp only [SignTest, va, vv, vb] at t9' t10'
  refine ⟨((b1.keep f₈ (by decide)).keep f₉ (by decide)).keep f₁₀ (by decide),
    ((b2.keep f₈ (by decide)).keep f₉ (by decide)).keep f₁₀ (by decide),
    ((b3.keep f₈ (by decide)).keep f₉ (by decide)).keep f₁₀ (by decide),
    ((b4.keep f₈ (by decide)).keep f₉ (by decide)).keep f₁₀ (by decide),
    (b5.keep f₉ (by decide)).keep f₁₀ (by decide), (b6.keep f₉ (by decide)).keep f₁₀ (by decide),
    (b7.keep f₉ (by decide)).keep f₁₀ (by decide), (b8.keep f₉ (by decide)).keep f₁₀ (by decide),
    BitIs.keep ⟨b9, t9'⟩ f₁₀ (by decide), ⟨b10, t10'⟩⟩


/-! ## The corners at the top of the chain -/

theorem BitIs.of_bf {c : Config} {r : ℕ} {f : BF} {v : ℕ → Bool} {p : Prop}
    (h : c.nreg r = (f.eval v).toNat) (hv : f.eval v = true ↔ p) : BitIs c r p := by
  refine ⟨by rw [h]; exact Bool.toNat_le _, ?_⟩
  rw [h, ← hv]; cases f.eval v <;> simp

/-- The orientation at the first top corner (`slitTop → top → b`). -/
theorem det_slitTop_first (C : Chain) (b : Point) :
    det C.slitTop C.top b = (C.radius - C.top.2) * (b.1 - C.top.1) := by
  simp only [det, Chain.slitTop]; ring

/-- The orientation at the last top corner (`a → top → slitTop`). -/
theorem det_slitTop_last (C : Chain) (a : Point) :
    det a C.top C.slitTop = (C.radius - C.top.2) * (C.top.1 - a.1) := by
  simp only [det, Chain.slitTop]; ring

theorem walk_vtx_six (C : Chain) : (chainModel C).W.vtx 6 = C.top := C.sideWalk_vtx_six _

theorem walk_vtx_last (C : Chain) : (chainModel C).W.vtx (2 * C.m + 6) = C.top := by
  rw [walk_vtx_tour C le_rfl, ← Chain.sideTour, C.sideTour_two_m]

/-- The tour vertices `0` (the top) and `1`, the slit top before them. -/
def secFirst : Stmt :=
  .seq (.instr (.copyN 50120 50121)) (.seq (tvLoad 50133)
    (.seq (.instr (.addN 50120 50121 50032)) (.seq (tvLoad 50136)
      (.seq (cmp4 50133 50136 50141)
        (.seq (block [.constN 50145 1, .constN 50146 0, .constN 50147 0, .constN 50148 0,
            .copyN 50149 50143])
          ((BF.and (.not (.var 50143)) (.not (.var 50144))).compile 50150))))))

theorem wr_secFirst : wr Bsec secFirst = true := by decide

/-- **The ten bits at the first visit of the top** (`i = 0`). -/
theorem secFirst_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (h121 : c.nreg 50121 = 0) :
    ∃ c' k, Exec P W secFirst c c' k ∧ k ≤ 54 * H.length + 1100 ∧ FrameB Bsec c c' ∧
      CEnv P W H C c' ∧ BitsOK c' C.slitTop C.top ((chainModel C).W.vtx (1 + 6)) := by
  have hG := hE.hG
  have hW := hE.hW
  have hm1 := C.one_le
  have e₁ := Exec.copyN (P := P) hE.wb 50120 50121
  have hE₁ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sv, iv, lv, vv, -⟩ := tvLoad_exec _ hE₁
    (i := 0) (by simp [h121]) (by omega) (dst := 50133) (by norm_num)
  have r121₂ : c₂.nreg 50121 = 0 := by rw [f₂.1 _ (by decide)]; simp [h121]
  have e₃ := Exec.addN (P := P) e₂.wb_right 50120 50121 50032
    (by rw [r121₂, hE₂.r32]; omega)
  have hE₃ := hE₂.step e₃ (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sb, ib, lb, vb, -⟩ := tvLoad_exec _ hE₃
    (i := 1) (by simp [r121₂, hE₂.r32]) (by omega) (dst := 50136) (by norm_num)
  have iv₄ : SymPtIn c₄ 50133 sv := symPtIn_keep (symPtIn_of_eq iv fun j h1 h2 => by
    simp only [upd]; rw [ite_eq_right (by omega)]) f₄ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, b1, b2, b3, b4⟩ := cmp4_exec (base := 50141) hG hW c₄
    e₄.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) lv lb iv₄ ib
  have w₅ := e₅.wb_right
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W (block [.constN 50145 1, .constN 50146 0,
      .constN 50147 0, .constN 50148 0, .copyN 50149 50143]) c₅ c₆ k₆ ∧ k₆ = 5 ∧
      (c₆.nreg 50145 = 1 ∧ c₆.nreg 50146 = 0 ∧ c₆.nreg 50147 = 0 ∧ c₆.nreg 50148 = 0 ∧
        c₆.nreg 50149 = c₅.nreg 50143 ∧
        ∀ r, r ≠ 50145 → r ≠ 50146 → r ≠ 50147 → r ≠ 50148 → r ≠ 50149 →
          c₆.nreg r = c₅.nreg r) := by
    exec_block
    all_goals try omega
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      fun r h1 h2 h3 h4 h5 => by simp [h1, h2, h3, h4, h5]⟩
  obtain ⟨q45, q46, q47, q48, q49, qr⟩ := q
  have w₆ := e₆.wb_right
  have f₆ := exec_frameB e₆ (B := fun r => decide (50145 ≤ r ∧ r < 50150)) (by decide)
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, f₇⟩ := BF.compile_exec (P := P) (by omega)
    (BF.and (.not (.var 50143)) (.not (.var 50144))) 50150 c₆ w₆
    (by simp only [BF.VarsOK]; refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩
        · rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact b3.1
        · rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact b4.1)
  have ex : Exec P W secFirst c c₇ (1 + (k₂ + (1 + (k₄ + (k₅ + (k₆ + k₇)))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  have hE₅ := hE₄.frame f₅ e₅.wb_right (by decide)
  have hE₆ := hE₅.frame f₆ w₆ (by decide)
  have hE₇ := hE₆.frame f₇ e₇.wb_right (by decide)
  have hlen := hE.hlen
  have hsz : (BF.and (.not (.var 50143)) (.not (.var 50144))).size = 5 := rfl
  refine ⟨c₇, _, ex, by rw [hsz] at hk₇; omega, exec_frameB ex wr_secFirst, hE₇, ?_⟩
  have v6 : (chainModel C).W.vtx (0 + 6) = C.top := walk_vtx_six C
  simp only [Ys, Xs, vv, v6, vb] at b1 b2 b3 b4
  have hR := C.top_snd_lt_radius
  have k₆₇ : ∀ r, r < 50150 → c₇.nreg r = c₆.nreg r := fun r hr =>
    f₇.1 r (by simp only [BF.wset, decide_eq_false_iff_not]; omega)
  have k₅₇ : ∀ r, r < 50145 → c₇.nreg r = c₅.nreg r := fun r hr => by
    rw [k₆₇ r (by omega), qr r (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hb3 := b3.dec
  have hb4 := b4.dec
  refine ⟨b1.of_eq (k₅₇ _ (by norm_num)), b2.of_eq (k₅₇ _ (by norm_num)),
    b3.of_eq (k₅₇ _ (by norm_num)), b4.of_eq (k₅₇ _ (by norm_num)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BitIs.const_one (by rw [k₆₇ _ (by norm_num), q45]) (by simp [Chain.slitTop]; exact hR)
  · exact BitIs.const_zero (by rw [k₆₇ _ (by norm_num), q46])
      (by simp only [Chain.slitTop]; exact not_lt.2 hR.le)
  · exact BitIs.const_zero (by rw [k₆₇ _ (by norm_num), q47]) (by simp [Chain.slitTop])
  · exact BitIs.const_zero (by rw [k₆₇ _ (by norm_num), q48]) (by simp [Chain.slitTop])
  · refine (b3.of_eq (by rw [k₆₇ _ (by norm_num), q49])).congr ?_
    rw [det_slitTop_first]
    have hd : 0 < C.radius - C.top.2 := by linarith
    set x := ((chainModel C).W.vtx (1 + 6)).1
    constructor
    · intro h; exact mul_pos hd (by linarith)
    · intro h; by_contra h'; push Not at h'
      have : (C.radius - C.top.2) * (x - C.top.1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hd.le (by linarith)
      linarith
  · refine BitIs.of_bf v₇ ?_
    simp only [BF.eval, Bool.and_eq_true, Bool.not_eq_true']
    rw [det_slitTop_first]
    have hd : 0 < C.radius - C.top.2 := by linarith
    set x := ((chainModel C).W.vtx (1 + 6)).1
    have e3 : (decide (c₆.nreg 50143 = 1)) = false ↔ ¬ (C.top.1 < x) := by
      rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), ← hb3]; simp
    have e4 : (decide (c₆.nreg 50144 = 1)) = false ↔ ¬ (x < C.top.1) := by
      rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), ← hb4]; simp
    rw [e3, e4]
    constructor
    · rintro ⟨h1, h2⟩
      have : x - C.top.1 = 0 := by push Not at h1 h2; linarith
      rw [this, mul_zero]
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · linarith
      · constructor <;> intro h' <;> linarith


/-- The tour vertices `2m - 1` and `2m` (the top), the slit top after them. -/
def secLast : Stmt :=
  .seq (.instr (.subN 50120 50121 50032)) (.seq (tvLoad 50130)
    (.seq (.instr (.copyN 50120 50121)) (.seq (tvLoad 50133)
      (.seq (cmp4 50133 50130 50145)
        (.seq (block [.constN 50141 1, .constN 50142 0, .constN 50143 0, .constN 50144 0,
            .copyN 50149 50148])
          ((BF.and (.not (.var 50147)) (.not (.var 50148))).compile 50150))))))

theorem wr_secLast : wr Bsec secLast = true := by decide

/-- **The ten bits at the last visit of the top** (`i = 2m`). -/
theorem secLast_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (h121 : c.nreg 50121 = 2 * C.m) :
    ∃ c' k, Exec P W secLast c c' k ∧ k ≤ 54 * H.length + 1100 ∧ FrameB Bsec c c' ∧
      CEnv P W H C c' ∧ BitsOK c' ((chainModel C).W.vtx ((2 * C.m - 1) + 6)) C.top C.slitTop := by
  have hG := hE.hG
  have hW := hE.hW
  have hm1 := C.one_le
  have e₁ := Exec.subN (P := P) hE.wb 50120 50121 50032
  have hE₁ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sa, ia, la, va, -⟩ := tvLoad_exec _ hE₁
    (i := 2 * C.m - 1) (by simp [h121, hE.r32]) (by omega) (dst := 50130) (by norm_num)
  have r121₂ : c₂.nreg 50121 = 2 * C.m := by rw [f₂.1 _ (by decide)]; simp [h121]
  have e₃ := Exec.copyN (P := P) e₂.wb_right 50120 50121
  have hE₃ := hE₂.step e₃ (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sv, iv, lv, vv, -⟩ := tvLoad_exec _ hE₃
    (i := 2 * C.m) (by simp [r121₂]) le_rfl (dst := 50133) (by norm_num)
  have ia₄ : SymPtIn c₄ 50130 sa := symPtIn_keep (symPtIn_of_eq ia fun j h1 h2 => by
    simp only [upd]; rw [ite_eq_right (by omega)]) f₄ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, b5, b6, b7, b8⟩ := cmp4_exec (base := 50145) hG hW c₄
    e₄.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) lv la iv ia₄
  have w₅ := e₅.wb_right
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W (block [.constN 50141 1, .constN 50142 0,
      .constN 50143 0, .constN 50144 0, .copyN 50149 50148]) c₅ c₆ k₆ ∧ k₆ = 5 ∧
      (c₆.nreg 50141 = 1 ∧ c₆.nreg 50142 = 0 ∧ c₆.nreg 50143 = 0 ∧ c₆.nreg 50144 = 0 ∧
        c₆.nreg 50149 = c₅.nreg 50148 ∧
        ∀ r, r ≠ 50141 → r ≠ 50142 → r ≠ 50143 → r ≠ 50144 → r ≠ 50149 →
          c₆.nreg r = c₅.nreg r) := by
    exec_block
    all_goals try omega
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      fun r h1 h2 h3 h4 h5 => by simp [h1, h2, h3, h4, h5]⟩
  obtain ⟨q41, q42, q43, q44, q49, qr⟩ := q
  have w₆ := e₆.wb_right
  have f₆ := exec_frameB e₆ (B := fun r => decide (50141 ≤ r ∧ r < 50150)) (by decide)
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, f₇⟩ := BF.compile_exec (P := P) (by omega)
    (BF.and (.not (.var 50147)) (.not (.var 50148))) 50150 c₆ w₆
    (by simp only [BF.VarsOK]; refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩
        · rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact b7.1
        · rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact b8.1)
  have ex : Exec P W secLast c c₇ (1 + (k₂ + (1 + (k₄ + (k₅ + (k₆ + k₇)))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  have hE₅ := hE₄.frame f₅ e₅.wb_right (by decide)
  have hE₆ := hE₅.frame f₆ w₆ (by decide)
  have hE₇ := hE₆.frame f₇ e₇.wb_right (by decide)
  have hlen := hE.hlen
  have hsz : (BF.and (.not (.var 50147)) (.not (.var 50148))).size = 5 := rfl
  refine ⟨c₇, _, ex, by rw [hsz] at hk₇; omega, exec_frameB ex wr_secLast, hE₇, ?_⟩
  have vl : (chainModel C).W.vtx (2 * C.m + 6) = C.top := walk_vtx_last C
  simp only [Ys, Xs, vv, vl, va] at b5 b6 b7 b8
  have hR := C.top_snd_lt_radius
  have k₆₇ : ∀ r, r < 50150 → c₇.nreg r = c₆.nreg r := fun r hr =>
    f₇.1 r (by simp only [BF.wset, decide_eq_false_iff_not]; omega)
  have hb7 := b7.dec
  have hb8 := b8.dec
  refine ⟨?_, ?_, ?_, ?_, b5.of_eq (by rw [k₆₇ _ (by norm_num), qr _ (by decide) (by decide)
    (by decide) (by decide) (by decide)]), b6.of_eq (by rw [k₆₇ _ (by norm_num), qr _ (by decide)
    (by decide) (by decide) (by decide) (by decide)]), b7.of_eq (by rw [k₆₇ _ (by norm_num),
    qr _ (by decide) (by decide) (by decide) (by decide) (by decide)]), b8.of_eq (by
    rw [k₆₇ _ (by norm_num), qr _ (by decide) (by decide) (by decide) (by decide) (by decide)]),
    ?_, ?_⟩
  · exact BitIs.const_one (by rw [k₆₇ _ (by norm_num), q41]) (by simp [Chain.slitTop]; exact hR)
  · exact BitIs.const_zero (by rw [k₆₇ _ (by norm_num), q42])
      (by simp only [Chain.slitTop]; exact not_lt.2 hR.le)
  · exact BitIs.const_zero (by rw [k₆₇ _ (by norm_num), q43]) (by simp [Chain.slitTop])
  · exact BitIs.const_zero (by rw [k₆₇ _ (by norm_num), q44]) (by simp [Chain.slitTop])
  · refine (b8.of_eq (by rw [k₆₇ _ (by norm_num), q49])).congr ?_
    rw [det_slitTop_last]
    have hd : 0 < C.radius - C.top.2 := by linarith
    set x := ((chainModel C).W.vtx ((2 * C.m - 1) + 6)).1
    constructor
    · intro h; exact mul_pos hd (by linarith)
    · intro h; by_contra h'; push Not at h'
      have : (C.radius - C.top.2) * (C.top.1 - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hd.le (by linarith)
      linarith
  · refine BitIs.of_bf v₇ ?_
    simp only [BF.eval, Bool.and_eq_true, Bool.not_eq_true']
    rw [det_slitTop_last]
    have hd : 0 < C.radius - C.top.2 := by linarith
    set x := ((chainModel C).W.vtx ((2 * C.m - 1) + 6)).1
    have e7 : (decide (c₆.nreg 50147 = 1)) = false ↔ ¬ (C.top.1 < x) := by
      rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), ← hb7]; simp
    have e8 : (decide (c₆.nreg 50148 = 1)) = false ↔ ¬ (x < C.top.1) := by
      rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), ← hb8]; simp
    rw [e7, e8]
    constructor
    · rintro ⟨h1, h2⟩
      have : C.top.1 - x = 0 := by push Not at h1 h2; linarith
      rw [this, mul_zero]
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · linarith
      · constructor <;> intro h' <;> linarith


/-! ## The sector procedure -/

theorem SecProp_congr {sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n sp' oP' oZ' b2p' b2n' b1p' b1n'
    a2p' a2n' a1p' a1n' : Prop} (h1 : sp ↔ sp') (h2 : oP ↔ oP') (h3 : oZ ↔ oZ') (h4 : b2p ↔ b2p')
    (h5 : b2n ↔ b2n') (h6 : b1p ↔ b1p') (h7 : b1n ↔ b1n') (h8 : a2p ↔ a2p') (h9 : a2n ↔ a2n')
    (h10 : a1p ↔ a1p') (h11 : a1n ↔ a1n') :
    SecProp sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n ↔
      SecProp sp' oP' oZ' b2p' b2n' b1p' b1n' a2p' a2n' a1p' a1n' := by
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- The direction bit: `50140 := [σ = 1]`. -/
def spBit : Stmt :=
  .seq (.instr (.constN 50140 0))
    (.ifLtN 50203 50032 .skip (.ifLtN 50032 50203 .skip (.instr (.constN 50140 1))))

/-- The sector formula over the bit registers. -/
def secF : BF := secBF 50140 50149 50150 50141 50142 50143 50144 50145 50146 50147 50148

/-- **The left sector at the tour vertex `6 + i`** (`i` in `50121`, direction code in `50203`;
answer bit in `50110`). -/
def secAt : Stmt :=
  .seq (.instr (.addN 50123 50053 50053))
    (.seq (.ifLtN 50121 50032 secFirst (.ifLtN 50121 50123 secGen secLast))
      (.seq spBit (.seq (secF.compile 50300) (.instr (.copyN 50110 50300)))))

theorem wr_secAt : wr Bsec secAt = true := by decide

/-- The neighbours of the tour vertex `6 + i` on the walk. -/
theorem sideLeft_tour_iff (C : Chain) {i : ℕ} (hi : i ≤ 2 * C.m) (x : Point) :
    sideLeft (chainModel C).W (i + 6) 0 x ↔
      sideLeftOf (if i = 0 then C.slitTop else (chainModel C).W.vtx ((i - 1) + 6))
        ((chainModel C).W.vtx (i + 6))
        (if i = 2 * C.m then C.slitTop else (chainModel C).W.vtx ((i + 1) + 6)) x := by
  have hm := C.one_le
  rw [Chazelle.Chain.sideLeft_zero]
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  by_cases h0 : i = 0
  · subst h0
    rw [ite_eq_left rfl, ite_eq_right (by omega), hW, C.sideWalk_prev_six, C.sideWalk_next_tour _ (by omega),
      C.sideWalk_vtx_five]
  · rw [ite_eq_right h0]
    by_cases h2 : i = 2 * C.m
    · rw [ite_eq_left h2, hW, C.sideWalk_prev_tour _ (by omega) hi]
      subst h2
      rw [C.sideWalk_next_last, C.sideWalk_vtx_zero]
    · rw [ite_eq_right h2, hW, C.sideWalk_prev_tour _ (by omega) hi, C.sideWalk_next_tour _ (by omega)]

theorem dirOf_cases (σ : ℕ) : dirOf σ = 1 ∨ dirOf σ = -1 := by
  unfold dirOf; split_ifs <;> simp

theorem dirOf_eq_one_iff (σ : ℕ) : dirOf σ = 1 ↔ σ = 1 := by
  unfold dirOf; split_ifs with h <;> simp [h]; norm_num

/-- **The left sector at a tour vertex** (at most `81 |H| + 3200` steps): the answer bit is the
truth of `rayPt v (dirOf σ) 1 ∈` the open left sector of the walk at the vertex `v = 6 + i`. -/
theorem secAt_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {i : ℕ} (h121 : c.nreg 50121 = i) (hi : i ≤ 2 * C.m) :
    ∃ c' k, Exec P W secAt c c' k ∧ k ≤ 81 * H.length + 3200 ∧ FrameB Bsec c c' ∧
      CEnv P W H C c' ∧ BitIs c' 50110 (sideLeft (chainModel C).W (i + 6) 0
        (Visibility.rayPt ((chainModel C).W.vtx (i + 6)) (dirOf (c.nreg 50203)) 1)) := by
  have hm1 := C.one_le
  have hlen := hE.hlen
  have hW := hE.hW
  set σ := c.nreg 50203 with hσ
  have e₁ := Exec.addN (P := P) hE.wb 50123 50053 50053
    (by rw [hE.r53]; have := hE.NW; have := C.m_lt; have := hE.n_eq; omega)
  set c₁ : Config := { c with nreg := upd c.nreg 50123 (c.nreg 50053 + c.nreg 50053) } with hc₁
  have hE₁ : CEnv P W H C c₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50123)
    (by decide)) e₁.wb_right (by decide)
  have q121 : c₁.nreg 50121 = i := by rw [hc₁]; simp [h121]
  have q123 : c₁.nreg 50123 = 2 * C.m := by rw [hc₁]; simp [hE.r53]; ring
  have q32 : c₁.nreg 50032 = 1 := hE₁.r32
  -- the ten bits
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, a, b, hab, hbits⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 50121 50032 secFirst (.ifLtN 50121 50123 secGen secLast)) c₁ c₂ k₂ ∧
      k₂ ≤ 81 * H.length + 2610 ∧ FrameB Bsec c₁ c₂ ∧ CEnv P W H C c₂ ∧
      ∃ a b : Point, (∀ x, sideLeft (chainModel C).W (i + 6) 0 x ↔
        sideLeftOf a ((chainModel C).W.vtx (i + 6)) b x) ∧
        BitsOK c₂ a ((chainModel C).W.vtx (i + 6)) b := by
    by_cases h0 : i = 0
    · subst h0
      obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, hb⟩ := secFirst_exec c₁ hE₁ q121
      refine ⟨c₂, _, .ifLtN_true (by rw [q121, q32]; omega) e₂, by omega, f₂, hE₂, C.slitTop,
        (chainModel C).W.vtx (1 + 6), fun x => ?_, by rw [walk_vtx_six]; exact hb⟩
      rw [sideLeft_tour_iff C (by omega), ite_eq_left rfl, ite_eq_right (by omega)]
    · by_cases h2 : i < 2 * C.m
      · obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, hb⟩ := secGen_exec c₁ hE₁ q121 (by omega) h2
        refine ⟨c₂, _, .ifLtN_false (by rw [q121, q32]; omega)
          (.ifLtN_true (by rw [q121, q123]; exact h2) e₂), by omega, f₂, hE₂, _, _,
          fun x => ?_, hb⟩
        rw [sideLeft_tour_iff C hi, ite_eq_right h0, ite_eq_right (by omega)]
      · have hi2 : i = 2 * C.m := by omega
        obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, hb⟩ := secLast_exec c₁ hE₁ (by rw [q121, hi2])
        refine ⟨c₂, _, .ifLtN_false (by rw [q121, q32]; omega)
          (.ifLtN_false (by rw [q121, q123]; exact h2) e₂), by omega, f₂, hE₂,
          (chainModel C).W.vtx ((2 * C.m - 1) + 6), C.slitTop, fun x => ?_,
          by rw [hi2, walk_vtx_last]; exact hb⟩
        rw [sideLeft_tour_iff C hi, ite_eq_right h0, ite_eq_left hi2]
        subst hi2; rfl
  have w₂ := e₂.wb_right
  have s₂ : c₂.nreg 50203 = σ := by
    rw [f₂.1 _ (by decide), hc₁]; simp [hσ]
  have p₂ : c₂.nreg 50032 = 1 := hE₂.r32
  -- the direction bit
  obtain ⟨c₃, k₃, e₃, hk₃, b₃, r₃⟩ : ∃ c₃ k₃, Exec P W spBit c₂ c₃ k₃ ∧ k₃ ≤ 6 ∧
      BitIs c₃ 50140 (σ = 1) ∧ ∀ r, r ≠ 50140 → c₃.nreg r = c₂.nreg r := by
    have e := Exec.constN (P := P) w₂ 50140 0 (by omega)
    have w := e.wb_right
    unfold spBit
    refine spec_seq ⟨_, 1, e, ?_⟩
    by_cases hl : σ < 1
    · refine spec_ifLtN_true (by simp [s₂, p₂, hl]) (spec_skip w ⟨by omega, ?_, ?_⟩)
      · exact BitIs.const_zero (by simp) (by omega)
      · intro r hr; simp [hr]
    · refine spec_ifLtN_false (by simp [s₂, p₂, hl]) ?_
      by_cases hg : 1 < σ
      · refine spec_ifLtN_true (by simp [s₂, p₂, hg]) (spec_skip w ⟨by omega, ?_, ?_⟩)
        · exact BitIs.const_zero (by simp) (by omega)
        · intro r hr; simp [hr]
      · refine spec_ifLtN_false (by simp [s₂, p₂, hg])
          (spec_instr (Exec.constN w _ _ (by omega)) fun _ => ⟨by omega, ?_, ?_⟩)
        · exact BitIs.const_one (by simp) (by omega)
        · intro r hr; simp [hr]
  have w₃ := e₃.wb_right
  obtain ⟨h41, h42, h43, h44, h45, h46, h47, h48, h49, h50⟩ := hbits
  have k3 : ∀ {r : ℕ} {p : Prop}, r ≠ 50140 → BitIs c₂ r p → BitIs c₃ r p :=
    fun hr h => h.of_eq (r₃ _ hr)
  -- the formula
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ := BF.compile_exec (P := P) (by have := hE.hW; omega) secF
    50300 c₃ w₃ (secBF_vars (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by norm_num, b₃.1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h49).1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h50).1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h41).1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h42).1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h43).1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h44).1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h45).1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h46).1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h47).1⟩
      · exact ⟨by norm_num, (k3 (by norm_num) h48).1⟩))
  have w₄ := e₄.wb_right
  have e₅ := Exec.copyN (P := P) w₄ 50110 50300
  have ex : Exec P W secAt c _ (1 + (k₂ + (k₃ + (k₄ + 1)))) := .seq e₁ (.seq e₂ (.seq e₃
    (.seq e₄ e₅)))
  have hszF : secF.size = 101 := rfl
  have hE₃ : CEnv P W H C c₃ := hE₂.keep w₃ (by
    have := exec_frameB e₃ (B := fun r => r == 50140) (by decide); exact this.2.2.1)
    (fun r hr => r₃ r (by intro h; subst h; revert hr; decide))
  have hE₄ : CEnv P W H C c₄ := hE₃.frame f₄ w₄ (by decide)
  refine ⟨_, _, ex, by rw [hszF] at hk₄; omega, exec_frameB ex wr_secAt,
    hE₄.keep e₅.wb_right rfl (fun r hr => by
      simp only [upd]; rw [ite_eq_right]; intro h; subst h; revert hr; decide), ?_⟩
  refine BitIs.of_bf (f := secF) (v := fun r => decide (c₃.nreg r = 1)) (by simp [v₄]) ?_
  rw [secF, secBF_eval, hab, sideLeftOf_horiz_iff _ _ _ (dirOf_cases σ)]
  exact SecProp_congr (by rw [b₃.dec, dirOf_eq_one_iff]) (k3 (by norm_num) h49).dec
    (k3 (by norm_num) h50).dec (k3 (by norm_num) h41).dec (k3 (by norm_num) h42).dec
    (k3 (by norm_num) h43).dec (k3 (by norm_num) h44).dec (k3 (by norm_num) h45).dec
    (k3 (by norm_num) h46).dec (k3 (by norm_num) h47).dec (k3 (by norm_num) h48).dec

end

end SweepPrim

end Chazelle.Core
