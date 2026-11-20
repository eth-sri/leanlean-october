module

public import Chazelle.Core.BruteRam7

/-!
# WP-K on the RAM, part 8: the loop body and the loop

`bodyS = idxS ; cornerS ; emitB 0 ; emitB 1 ; advS` and `loopS` (`loopS_exec`): from the
set-up state, the loop over the tour positions writes the list `bruteList C` at `A₀ + 10`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

open Classical

/-- The loop body. -/
def bodyS : Stmt := .seq idxS (.seq cornerS (.seq (emitB 0) (.seq (emitB 1) advS)))

/-- The loop. -/
def loopS : Stmt :=
  .seq (block [.constN 180030 0, .constN 180033 0, .copyN 180031 180015])
    (.seq (.ifLtN 180031 180012 .skip (.instr (.constN 180031 0)))
      (.whileLtN 180030 180025 bodyS))

/-- The write set of the body: the kernel, `180030 … 180089`, `180019`, `180024`. -/
def Bbd (r : ℕ) : Bool := Bk r || decide (180030 ≤ r ∧ r < 180090) || decide (r = 180019 ∨ r = 180024)

theorem ctx_of_bbd {P : Polygon} {C : Chain} {γ A₀ : ℕ} {c c' : Config} (h : Ctx P C γ A₀ c)
    (hk : ∀ r, Bbd r = false → c'.nreg r = c.nreg r) : Ctx P C γ A₀ c' :=
  h.keep fun r hr => hk r (by
    unfold CtxReg at hr; unfold Bbd Bk
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)

/-- **The loop invariant** at the head of the loop. -/
def LI (P : Polygon) (C : Chain) (γ A₀ : ℕ) (M : ℕ → ℕ) (c₀ d : Config) : Prop :=
  Ctx P C γ A₀ d ∧ d.nreg 180030 ≤ 2 * C.m + 1 ∧
    (d.nreg 180030 ≤ 2 * C.m → d.nreg 180031 = (tS C + d.nreg 180030) % (2 * C.m)) ∧
    d.nreg 180033 ≤ C.m ∧
    (0 < d.nreg 180030 → d.nreg 180033 = C.sideIdx C.sideBeta (d.nreg 180030 - 1)) ∧
    d.nreg 180019 = (pre C (d.nreg 180030)).length ∧
    d.nreg 180024 = A₀ + 10 + 3 * (pre C (d.nreg 180030)).length ∧
    ChordListAt d.nmem (A₀ + 10) (pre C (d.nreg 180030)) ∧
    (∀ x, x < A₀ + 10 → d.nmem x = M x) ∧
    (∀ r, Bbd r = false → d.nreg r = c₀.nreg r) ∧ (∀ r, Bbd r = false → d.rreg r = c₀.rreg r) ∧
    d.rmem = c₀.rmem ∧ d.output = c₀.output

theorem bbd_of_lp {c c' : Config} (F : FrameB Blp c c') : ∀ r, Bbd r = false → c'.nreg r = c.nreg r :=
  fun r hr => F.1 r (by
    unfold Bbd Bk at hr; unfold Blp
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega)

theorem bbd_of_co {c c' : Config} (F : FrameB Bco c c') : ∀ r, Bbd r = false → c'.nreg r = c.nreg r :=
  fun r hr => F.1 r (by
    unfold Bbd at hr; unfold Bco
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; exact ⟨hr.1.1, by omega⟩)

theorem bbd_of_em {c c' : Config} (h : ∀ r, Bem r = false → c'.nreg r = c.nreg r) :
    ∀ r, Bbd r = false → c'.nreg r = c.nreg r :=
  fun r hr => h r (by
    unfold Bbd at hr; unfold Bem Bsc
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
    exact ⟨⟨hr.1.1, by omega⟩, by omega⟩)

set_option maxHeartbeats 4000000 in
/-- **One iteration of the loop.** -/
theorem bodyS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) {C : Chain} (hW : P.n + 2 * C.m + 8 ≤ W)
    (hW4 : 4 * P.n ≤ W) (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n)
    {γ A₀ : ℕ} {M : ℕ → ℕ} (hroom : A₀ + 10 + 6 * (2 * C.m + 1) + 3 ≤ W) {c₀ : Config}
    (c : Config) (hw : WordsBounded W c) (hI : LI P C γ A₀ M c₀ c) (hlt : c.nreg 180030 < 2 * C.m + 1) :
    ∃ c' k, Exec P W bodyS c c' k ∧ k ≤ 3300 * C.m + 1400 ∧
      3 * (pre C (c.nreg 180030 + 1)).length ≤ 3 * (pre C (c.nreg 180030)).length + k ∧
      LI P C γ A₀ M c₀ c' ∧
      c'.nreg 180030 = c.nreg 180030 + 1 := by
  obtain ⟨hX, -, h31, h33b, h33, h19, h24, hL, hM, hR, hRR, hRM, hO⟩ := hI
  obtain ⟨x0, x1, x2, x10, x11, x12, x13, x15, x16, x17, x18, x23, x25, x26, x27, x28⟩ := hX
  set i := c.nreg 180030 with hid
  have hi : i ≤ 2 * C.m := by omega
  have hk := C.sideIdx_le C.sideBeta i
  -- indices
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, q32, q33, q35, q36, q37, q44, q30, q31⟩ := idxS_exec (P := P) (C := C) c hw
    hsn hW hi x0 x1 x11 x12 x27 rfl (h31 hi) rfl h33b
  have K₁ := bbd_of_lp F₁
  have X₁ : Ctx P C γ A₀ c₁ := ctx_of_bbd ⟨x0, x1, x2, x10, x11, x12, x13, x15, x16, x17, x18, x23,
    x25, x26, x27, x28⟩ K₁
  -- the corner
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b41, b42, t41, t42⟩ := cornerS_exec (P := P) hG (by omega) hC hsn hi
    c₁ e₁.wb_right X₁.2.2.2.2.1 X₁.2.2.2.2.2.1 X₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 q30 q35
    (fun h => by rw [q36, h33 h]) (fun _ => q37)
  have K₂ := bbd_of_co F₂
  have X₂ : Ctx P C γ A₀ c₂ := ctx_of_bbd X₁ K₂
  have c35 : c₂.nreg 180035 = C.s + C.sideIdx C.sideBeta i := by rw [F₂.1 _ (by decide), q35]
  have c44 : c₂.nreg 180044 = i + 6 := by rw [F₂.1 _ (by decide), q44]
  have c24 : c₂.nreg 180024 = A₀ + 10 + 3 * (pre C i).length := by
    rw [F₂.1 _ (by decide), F₁.1 _ (by decide), h24]
  have c19 : c₂.nreg 180019 = (pre C i).length := by rw [F₂.1 _ (by decide), F₁.1 _ (by decide), h19]
  have m₂ : c₂.nmem = c.nmem := by rw [F₂.2.2.1, F₁.2.2.1]
  have hlen := pre_length_le C i
  -- east
  obtain ⟨c₃, k₃, e₃, hk₃, lb₃, p24, p19, pL, pM, R₃, RR₃, RM₃, O₃⟩ := emitB_exec (P := P) (d := 0) hG
    (by omega) hW4 hC hsn (by omega) hi c₂ e₂.wb_right
    ⟨X₂.1, X₂.2.1, X₂.2.2.2.2.1, c35⟩ ⟨X₂.2.2.2.2.2.1, X₂.2.2.2.2.2.2.2.1, X₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    b41 t41 c44 (L := A₀ + 10) (l := pre C i) (M := M) c24 c19 (by rw [m₂]; exact hL) (by intro x hx; rw [m₂]; exact hM x hx)
    (by omega)
  have K₃ := bbd_of_em R₃
  have X₃ : Ctx P C γ A₀ c₃ := ctx_of_bbd X₂ K₃
  have d35 : c₃.nreg 180035 = C.s + C.sideIdx C.sideBeta i := by rw [R₃ _ (by decide), c35]
  have d44 : c₃.nreg 180044 = i + 6 := by rw [R₃ _ (by decide), c44]
  have d42 : c₃.nreg 180042 = c₂.nreg 180042 := R₃ _ (by decide)
  set l₁ := pre C i ++ (if Emit C i 0 then [trip C i 0] else []) with hl₁
  have hl₁len : l₁.length ≤ 2 * i + 1 := by
    rw [hl₁, List.length_append]; have : (if Emit C i 0 then [trip C i 0] else []).length ≤ 1 := by
      split_ifs <;> simp
    omega
  -- west
  obtain ⟨c₄, k₄, e₄, hk₄, lb₄, r24, r19, rL, rM, R₄, RR₄, RM₄, O₄⟩ := emitB_exec (P := P) (d := 1) hG
    (by omega) hW4 hC hsn (by omega) hi c₃ e₃.wb_right
    ⟨X₃.1, X₃.2.1, X₃.2.2.2.2.1, d35⟩ ⟨X₃.2.2.2.2.2.1, X₃.2.2.2.2.2.2.2.1, X₃.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    (by rw [d42]; exact b42) (by rw [d42]; exact t42) d44 (l := l₁) (L := A₀ + 10) (M := M) p24 p19
    pL pM (by omega)
  have K₄ := bbd_of_em R₄
  have X₄ : Ctx P C γ A₀ c₄ := ctx_of_bbd X₃ K₄
  -- advance
  have e30 : c₄.nreg 180030 = i := by
    rw [R₄ _ (by decide), R₃ _ (by decide), F₂.1 _ (by decide), q30]
  have e31 : c₄.nreg 180031 = (tS C + i) % (2 * C.m) := by
    rw [R₄ _ (by decide), R₃ _ (by decide), F₂.1 _ (by decide), q31]
    exact h31 hi
  have e32 : c₄.nreg 180032 = C.sideIdx C.sideBeta i := by
    rw [R₄ _ (by decide), R₃ _ (by decide), F₂.1 _ (by decide), q32]
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, s33, s30, s31⟩ := advS_exec (P := P) (C := C) c₄ e₄.wb_right
    (by omega) hi X₄.2.2.2.2.1 X₄.2.2.2.2.2.1 e30 e31
  have K₅ := bbd_of_lp F₅
  have X₅ : Ctx P C γ A₀ c₅ := ctx_of_bbd X₄ K₅
  have ex : Exec P W bodyS c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have hpre : pre C (i + 1) = l₁ ++ (if Emit C i 1 then [trip C i 1] else []) := by
    rw [pre_succ, hl₁, List.append_assoc]
  have hlb : 3 * (pre C (i + 1)).length ≤ 3 * (pre C i).length + (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) := by
    rw [hpre]; omega
  refine ⟨c₅, _, ex, by omega, hlb, ⟨X₅, by rw [s30]; omega, fun h => by rw [s30]; exact s31 (by omega),
    by rw [s33, e32]; exact hk, fun _ => by rw [s33, e32, s30]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    s30⟩
  · rw [F₅.1 _ (by decide), r19, s30, hpre]
  · rw [F₅.1 _ (by decide), r24, s30, hpre]
  · rw [F₅.2.2.1, s30, hpre]; exact rL
  · intro x hx; rw [F₅.2.2.1]; exact rM x hx
  · intro r hr; rw [K₅ r hr, K₄ r hr, K₃ r hr, K₂ r hr, K₁ r hr, hR r hr]
  · intro r hr
    have hb : Bsc r = false := by
      unfold Bbd at hr; unfold Bsc
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; exact ⟨hr.1.1, by omega⟩
    have hc : Bco r = false := by
      unfold Bbd at hr; unfold Bco
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; exact ⟨hr.1.1, by omega⟩
    have hl : Blp r = false := by
      unfold Bbd at hr; unfold Blp
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega
    rw [F₅.2.1 r hl, RR₄ r hb, RR₃ r hb, F₂.2.1 r hc, F₁.2.1 r hl, hRR r hr]
  · rw [F₅.2.2.2.1, RM₄, RM₃, F₂.2.2.2.1, F₁.2.2.2.1, hRM]
  · rw [F₅.2.2.2.2, O₄, O₃, F₂.2.2.2.2, F₁.2.2.2.2, hO]

/-- A loop rule with a bounded body, a decreasing measure and a lower bound on the cost in
terms of a potential `g` (each iteration costs at least the growth of `g`). -/
theorem whileLtN_lb {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (μ : Config → ℕ) (B : ℕ) (g : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c ∧ g c' ≤ g c + k) :
    ∀ n c, μ c = n → I c → ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧
      ¬ c'.nreg a < c'.nreg b ∧ k ≤ (B + 2) * μ c + 2 ∧ g c' ≤ g c + k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hn hc
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, e₁, hI₁, hk₁, hμ, hg⟩ := hbody c hc ht
      obtain ⟨c', k₂, e₂, hI', hex, hk₂, hg'⟩ := ih (μ c₁) (by omega) c₁ rfl hI₁
      refine ⟨c', _, .whileLtN_true ht e₁ e₂, hI', hex, ?_, by omega⟩
      have : (B + 2) * (μ c₁ + 1) ≤ (B + 2) * μ c := Nat.mul_le_mul_left _ hμ
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, by omega, by omega⟩

set_option maxHeartbeats 1000000 in
/-- **The main loop**: from the set-up state, the list `bruteList C` is written at `A₀ + 10`. -/
theorem loopS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) {C : Chain} (hW : P.n + 2 * C.m + 8 ≤ W)
    (hW4 : 4 * P.n ≤ W) (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {γ A₀ : ℕ}
    (hroom : A₀ + 10 + 6 * (2 * C.m + 1) + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    (hX : Ctx P C γ A₀ c) (h19 : c.nreg 180019 = 0) (h24 : c.nreg 180024 = A₀ + 10) :
    ∃ c' k, Exec P W loopS c c' k ∧ k ≤ (3300 * C.m + 1402) * (2 * C.m + 1) + 10 ∧
      3 * (bruteList C).length ≤ k ∧
      Ctx P C γ A₀ c' ∧ c'.nreg 180019 = (bruteList C).length ∧
      c'.nreg 180024 = A₀ + 10 + 3 * (bruteList C).length ∧
      ChordListAt c'.nmem (A₀ + 10) (bruteList C) ∧ (∀ x, x < A₀ + 10 → c'.nmem x = c.nmem x) ∧
      (∀ r, Bbd r = false → c'.nreg r = c.nreg r) ∧ (∀ r, Bbd r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hm := C.two_m_pos
  have hS := C.sideS_lt C.sideBeta
  obtain ⟨c₁, k₁, e₁, hk₁, q30, q33, q31, R₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 180030 0, .constN 180033 0, .copyN 180031 180015]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 180030 = 0 ∧ c₁.nreg 180033 = 0 ∧ c₁.nreg 180031 = tS C ∧
      FrameB Blp c c₁ := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        exact hX.2.2.2.2.2.2.2.1
      · unfold Blp at hr; simp only [decide_eq_false_iff_not] at hr
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  have K₁ := bbd_of_lp R₁
  have X₁ := ctx_of_bbd hX K₁
  have w₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, q31', R₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 180031 180012 .skip (.instr (.constN 180031 0))) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 180031 = (tS C + 0) % (2 * C.m) ∧ FrameB (fun r => decide (r = 180031)) c₁ c₂ := by
    have hts : tS C ≤ 2 * C.m := hS
    by_cases hlt : tS C < 2 * C.m
    · exact ⟨c₁, _, .ifLtN_true (by rw [q31, X₁.2.2.2.2.2.1]; exact hlt) (.skip w₁), by omega,
        by rw [q31, add_zero, Nat.mod_eq_of_lt hlt], FrameB.refl _ _⟩
    · refine ⟨_, _, .ifLtN_false (by rw [q31, X₁.2.2.2.2.2.1]; exact hlt)
        (Exec.constN w₁ 180031 0 (by omega)), le_refl _, ?_, ⟨fun r hr => ?_, fun _ _ => rfl,
        rfl, rfl, rfl⟩⟩
      · simp only [Config.nreg_mk, upd_same]
        rw [add_zero, show tS C = 2 * C.m by omega, Nat.mod_self]
      · simp only [decide_eq_false_iff_not] at hr; simp [hr]
  have K₂ : ∀ r, Bbd r = false → c₂.nreg r = c₁.nreg r := fun r hr => R₂.1 r (by
    unfold Bbd at hr; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega)
  have X₂ := ctx_of_bbd X₁ K₂
  have hI : LI P C γ A₀ c.nmem c c₂ := by
    have e30 : c₂.nreg 180030 = 0 := by rw [R₂.1 _ (by decide), q30]
    refine ⟨X₂, by omega, fun _ => by rw [e30]; exact q31', by rw [R₂.1 _ (by decide), q33]; omega,
      fun h => by omega, ?_, ?_, ?_, ?_, fun r hr => by rw [K₂ r hr, K₁ r hr], fun r hr => ?_, ?_, ?_⟩
    · rw [e30, R₂.1 _ (by decide), R₁.1 _ (by decide), h19]; rfl
    · rw [e30, R₂.1 _ (by decide), R₁.1 _ (by decide), h24]; rfl
    · rw [e30]; intro j hj; simp [pre] at hj
    · intro x _; rw [R₂.2.2.1, R₁.2.2.1]
    · have h31 : r ≠ 180031 := by
        unfold Bbd at hr; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; omega
      rw [R₂.2.1 r (by simpa using h31), R₁.2.1 r (by
        unfold Blp; unfold Bbd at hr
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega)]
    · rw [R₂.2.2.2.1, R₁.2.2.2.1]
    · rw [R₂.2.2.2.2, R₁.2.2.2.2]
  obtain ⟨c₃, k₃, e₃, ⟨w₃, hI₃⟩, hex, hk₃, hg₃⟩ :=
    whileLtN_lb (P := P) (W := W) (a := 180030) (b := 180025) (body := bodyS)
      (fun d => WordsBounded W d ∧ LI P C γ A₀ c.nmem c d)
      (fun d => 2 * C.m + 1 - d.nreg 180030) (3300 * C.m + 1400)
      (fun d => 3 * (pre C (d.nreg 180030)).length) (fun d hd => hd.1)
      (by
        intro d ⟨wd, Id⟩ hlt
        rw [Id.1.2.2.2.2.2.2.2.2.2.2.2.2.1] at hlt
        obtain ⟨d', k', e', hk', lb', I', q'⟩ := bodyS_exec hG hW hW4 hC hsn hroom d wd Id hlt
        exact ⟨d', k', e', ⟨e'.wb_right, I'⟩, hk', by omega, by show 3 * (pre C (d'.nreg 180030)).length ≤ 3 * (pre C (d.nreg 180030)).length + k'; rw [q']; exact lb'⟩)
      _ c₂ rfl ⟨e₂.wb_right, hI⟩
  obtain ⟨X₃, l30, -, -, -, s19, s24, sL, sM, sR, sRR, sRM, sO⟩ := hI₃
  rw [X₃.2.2.2.2.2.2.2.2.2.2.2.2.1] at hex
  have e30 : c₃.nreg 180030 = 2 * C.m + 1 := by omega
  rw [e30, pre_full] at s19 s24 sL
  have : c₂.nreg 180030 = 0 := by rw [R₂.1 _ (by decide), q30]
  have hg' : 3 * (pre C (c₃.nreg 180030)).length ≤ 3 * (pre C (c₂.nreg 180030)).length + k₃ := hg₃
  rw [this, e30, pre_full] at hg'
  have hp0 : (pre C 0).length = 0 := by simp [pre]
  rw [hp0] at hg'
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ?_, by omega, X₃, s19, s24, sL, sM, sR,
    sRR, sRM, sO⟩
  rw [this, Nat.sub_zero] at hk₃
  have e1 : (3300 * C.m + 1400 + 2) * (2 * C.m + 1) = (3300 * C.m + 1402) * (2 * C.m + 1) := by ring
  rw [e1] at hk₃
  omega

end

end Brute

end Chazelle.Core
