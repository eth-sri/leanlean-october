module

public import Chazelle.Core.BruteSig

/-!
# WP-K on the RAM, part 1: constants and the top index

Registers of band `bBrute = 18` (`180000 + i`):

| reg | content |
|---|---|
| `180000, 180001, 180002` | inputs `a`, `m`, `γ`; `180003` the output |
| `180010` | `n` |
| `180011` | `1` |
| `180012` | `2m` |
| `180013` | the top index `T` (computed by `topS`) |
| `180014` | the orientation bit |
| `180015` | the tour start `S` |
| `180016, 180017, 180018` | the allocator at entry `A₀`, the model descriptor `A₀ + 4`, the chord list `A₀ + 10` |
| `180019, 180024` | the number of triples written and the next address |
| `180020 … 180022` | the top-index scan |
| `180023, 180025` | `m + 1`, `2m + 1` |
| `180026, 180027, 180028` | the constants `3`, `6`, `0` |
| `180030 …` | the main loop and the far-end scan |

`initS` sets the constants; `topS` scans the chain for the highest vertex (`topS_exec`: the
result is `C.topIdx`, by distinct heights).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- A chain vertex is the vertex `s + k` of the host (no wrap-around). -/
theorem vertex_eq {C : Chain} {k : ℕ} (hk : C.s + k < C.P.n) : C.vertex k = C.P.vtx (C.s + k) := by
  unfold Chain.vertex Chain.edgeIdx; rw [Nat.mod_eq_of_lt hk]

theorem edgeIdx_eq {C : Chain} {k : ℕ} (hk : C.s + k < C.P.n) : C.edgeIdx k = C.s + k := by
  unfold Chain.edgeIdx; rw [Nat.mod_eq_of_lt hk]

/-- The write set of the brute-force procedure's own statements: the kernel's registers and
band `18`. -/
def Bm (r : ℕ) : Bool := Bk r || decide (180000 ≤ r ∧ r < 190000)

theorem frameB_mono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B' r = false → B r = false) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r (hB r hr), fun r hr => h.2.1 r (hB r hr), h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ## Constants -/

/-- The constants. -/
def initS : Stmt :=
  block [.inputSize 180010, .constN 180011 1, .addN 180012 180001 180001, .copyN 180016 9999,
    .constN 180026 3, .constN 180027 6, .constN 180028 0, .addN 180023 180001 180011,
    .addN 180025 180012 180011]

theorem initS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (hW : P.n + 2 * c.nreg 180001 + 7 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k = 9 ∧ c'.nreg 180010 = P.n ∧ c'.nreg 180011 = 1 ∧
      c'.nreg 180012 = 2 * c.nreg 180001 ∧ c'.nreg 180016 = c.nreg 9999 ∧
      c'.nreg 180026 = 3 ∧ c'.nreg 180027 = 6 ∧ c'.nreg 180028 = 0 ∧
      c'.nreg 180023 = c.nreg 180001 + 1 ∧ c'.nreg 180025 = 2 * c.nreg 180001 + 1 ∧
      FrameB (fun r => decide (180010 ≤ r ∧ r < 180030)) c c' := by
  unfold initS
  exec_block
  · omega
  · omega
  · config_simp; omega
  · omega
  · omega
  · omega
  · config_simp; omega
  · config_simp; omega
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
    all_goals first
      | (simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]; omega)
      | simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
      | skip
    simp only [decide_eq_false_iff_not] at hr
    simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]


/-! ## Boolean operations on bit registers (`180011` holds `1`) -/

/-- `d := x ∧ y` (`x + y - 1`). -/
def andS (d x y : ℕ) : Stmt := block [.addN d x y, .subN d d 180011]

/-- `d := x ∨ y` (`x + y - (x + y - 1)`), with scratch `t`. -/
def orS (d x y t : ℕ) : Stmt := block [.addN d x y, .subN t d 180011, .subN d d t]

/-- `d := ¬ x` (`1 - x`). -/
def notS (d x : ℕ) : Stmt := block [.subN d 180011 x]

theorem andS_exec {P : Polygon} {W : ℕ} (hW : 2 ≤ W) (c : Config) (hw : WordsBounded W c)
    {d x y : ℕ} (hd : d ≠ 180011) (h1 : c.nreg 180011 = 1) (hx : c.nreg x ≤ 1)
    (hy : c.nreg y ≤ 1) :
    ∃ c' k, Exec P W (andS d x y) c c' k ∧ k = 2 ∧ c'.nreg d = c.nreg x + c.nreg y - 1 ∧
      FrameB (fun r => decide (r = d)) c c' := by
  unfold andS
  exec_block
  · config_simp; omega
  · refine ⟨rfl, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
    · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
      rw [h1]
    · simp only [decide_eq_false_iff_not] at hr
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]

theorem orS_exec {P : Polygon} {W : ℕ} (hW : 2 ≤ W) (c : Config) (hw : WordsBounded W c)
    {d x y t : ℕ} (hd : d ≠ 180011) (ht : t ≠ 180011) (hdt : d ≠ t) (h1 : c.nreg 180011 = 1)
    (hx : c.nreg x ≤ 1) (hy : c.nreg y ≤ 1) :
    ∃ c' k, Exec P W (orS d x y t) c c' k ∧ k = 3 ∧
      c'.nreg d = (c.nreg x + c.nreg y) - (c.nreg x + c.nreg y - 1) ∧
      FrameB (fun r => decide (r = d ∨ r = t)) c c' := by
  unfold orS
  exec_block
  · config_simp; omega
  · refine ⟨rfl, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
    · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
      rw [h1]
    · simp only [decide_eq_false_iff_not, not_or] at hr
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]

theorem notS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    {d x : ℕ} (_hd : d ≠ 180011) (h1 : c.nreg 180011 = 1) :
    ∃ c' k, Exec P W (notS d x) c c' k ∧ k = 1 ∧ c'.nreg d = 1 - c.nreg x ∧
      FrameB (fun r => decide (r = d)) c c' := by
  unfold notS
  exec_block
  refine ⟨rfl, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
  · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
    rw [h1]
  · simp only [decide_eq_false_iff_not] at hr
    simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]

/-! ## The top index -/

/-- One step of the top-index scan: compare `v_best` with `v_k`, keep the higher. -/
def topBody : Stmt :=
  .seq (block [.addN 180021 180000 180013, .addN 180022 180000 180020])
    (.seq (testS 1 (.v 180021) (.v 180022) (.v 180021) 180029)
      (.seq (.ifLtN 180029 180011 .skip (.instr (.copyN 180013 180020)))
        (.instr (.addN 180020 180020 180011))))

/-- The top-index scan. -/
def topS : Stmt :=
  .seq (block [.constN 180013 0, .constN 180020 1]) (.whileLtN 180020 180023 topBody)

/-- The write set of the scan. -/
def Btop (r : ℕ) : Bool :=
  Bk r || decide (r = 180013 ∨ (180020 ≤ r ∧ r < 180023) ∨ r = 180029)

theorem topBody_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {a b k : ℕ} (h0 : c.nreg 180000 = a) (h11 : c.nreg 180011 = 1)
    (h13 : c.nreg 180013 = b) (h20 : c.nreg 180020 = k) (hb : a + b < P.n) (hk : a + k < P.n) :
    ∃ c' k', Exec P W topBody c c' k' ∧ k' ≤ 253 ∧ FrameB Btop c c' ∧
      c'.nreg 180020 = k + 1 ∧
      c'.nreg 180013 = if ((Qof P).vtx (a + b)).2 < ((Qof P).vtx (a + k)).2 then k else b := by
  obtain ⟨c₁, k₁, e₁, hk₁, q21, q22, R₁, R₁'⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 180021 180000 180013, .addN 180022 180000 180020]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 180021 = a + b ∧ c₁.nreg 180022 = a + k ∧ FrameB Btop c c₁ ∧
      ∀ r, r ≠ 180021 → r ≠ 180022 → c₁.nreg r = c.nreg r := by
    exec_block
    · config_simp; rw [h0, h13]; omega
    · config_simp; rw [h0, h20]; omega
    · refine ⟨rfl, ?_, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩, fun r h1 h2 => ?_⟩
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [h0, h13]
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [h0, h20]
      · unfold Btop at hr
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, bit₂, sig₂⟩ := testS_exec (P := P) hG hW (op := 1) (by omega)
    (x := .v 180021) (y := .v 180022) (z := .v 180021) (d := 180029) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) c₁ e₁.wb_right
    (by simp only [Src.pt, SymPt.Lt]; omega) (by simp only [Src.pt, SymPt.Lt]; omega)
    (by simp only [Src.pt, SymPt.Lt]; omega)
  simp only [Src.pt, SymPt.eval, SignTest, q21, q22] at sig₂
  have k2 : ∀ r, Bt 180029 r = false → c₂.nreg r = c₁.nreg r := F₂.1
  have c11 : c₂.nreg 180011 = 1 := by
    rw [k2 _ (by decide), R₁' _ (by decide) (by decide), h11]
  have c13 : c₂.nreg 180013 = b := by rw [k2 _ (by decide), R₁' _ (by decide) (by decide), h13]
  have c20 : c₂.nreg 180020 = k := by rw [k2 _ (by decide), R₁' _ (by decide) (by decide), h20]
  have w₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, q13, q20, R₃⟩ : ∃ c₃ k₃, Exec P W
      (.ifLtN 180029 180011 .skip (.instr (.copyN 180013 180020))) c₂ c₃ k₃ ∧ k₃ ≤ 3 ∧
      c₃.nreg 180013 = (if ((Qof P).vtx (a + b)).2 < ((Qof P).vtx (a + k)).2 then k else b) ∧
      c₃.nreg 180020 = k ∧ FrameB Btop c₂ c₃ := by
    by_cases ht : ((Qof P).vtx (a + b)).2 < ((Qof P).vtx (a + k)).2
    · have h1 : c₂.nreg 180029 = 1 := sig₂.2 ht
      refine ⟨_, _, .ifLtN_false (by rw [h1, c11]; omega) (Exec.copyN w₂ 180013 180020), le_refl _,
        ?_, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
      · simp [ht, c20]
      · simp [c20]
      · unfold Btop at hr
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
    · have h1 : c₂.nreg 180029 = 0 := by have := mt sig₂.1 ht; omega
      exact ⟨_, _, .ifLtN_true (by rw [h1, c11]; omega) (.skip w₂), by omega,
        by rw [ite_eq_right ht, c13], c20, FrameB.refl _ _⟩
  have e₄ := Exec.addN (P := P) e₃.wb_right 180020 180020 180011 (by
    rw [q20, R₃.1 _ (by decide), c11]; omega)
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_, ?_, ?_⟩
  · refine (R₁.trans (frameB_mono F₂ ?_)).trans (R₃.trans ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩)
    · intro r hr
      unfold Btop at hr; unfold Bt
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
      exact ⟨hr.1, by omega⟩
    · unfold Btop at hr
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  · simp only [Config.nreg_mk, Machine.upd_same]
    rw [q20, R₃.1 _ (by decide), c11]
  · simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
    exact q13

/-- **The top-index scan**: register `180013` receives the index of the highest vertex among
`v_a, …, v_{a+m}` (at most `254 m + 256` steps). -/
theorem topS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {a m : ℕ} (h0 : c.nreg 180000 = a) (h11 : c.nreg 180011 = 1)
    (h23 : c.nreg 180023 = m + 1) (ham : a + m < P.n) :
    ∃ c' k', Exec P W topS c c' k' ∧ k' ≤ 255 * m + 257 ∧ FrameB Btop c c' ∧
      c'.nreg 180013 ≤ m ∧
      ∀ i, i ≤ m → ((Qof P).vtx (a + i)).2 ≤ ((Qof P).vtx (a + c'.nreg 180013)).2 := by
  obtain ⟨c₁, k₁, e₁, hk₁, q13, q20, R₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 180013 0, .constN 180020 1]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 180013 = 0 ∧ c₁.nreg 180020 = 1 ∧ FrameB Btop c c₁ := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
      unfold Btop at hr
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  let I : Config → Prop := fun d => WordsBounded W d ∧ FrameB Btop c d ∧
    1 ≤ d.nreg 180020 ∧ d.nreg 180020 ≤ m + 1 ∧ d.nreg 180013 < d.nreg 180020 ∧
    ∀ i, i < d.nreg 180020 → ((Qof P).vtx (a + i)).2 ≤ ((Qof P).vtx (a + d.nreg 180013)).2
  have hI₁ : I c₁ := ⟨e₁.wb_right, R₁, by omega, by omega, by omega, fun i hi => by
    rw [q13, show i = 0 by omega]⟩
  have keep : ∀ d r, FrameB Btop c d → Btop r = false → d.nreg r = c.nreg r := fun d r h hr =>
    h.1 r hr
  obtain ⟨c₂, k₂, e₂, ⟨w₂, F₂, h₁, h₂, h₃, h₄⟩, hex, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (W := W) (a := 180020) (b := 180023) (body := topBody) I
      (fun d => m + 1 - d.nreg 180020) 253 (fun d hd => hd.1)
      (by
        intro d ⟨wd, Fd, d1, d2, d3, d4⟩ hlt
        have d23 : d.nreg 180023 = m + 1 := by rw [keep d _ Fd (by decide), h23]
        rw [d23] at hlt
        obtain ⟨d', k', e', hk', F', q20', q13'⟩ := topBody_exec hG hW d wd
          (by rw [keep d _ Fd (by decide), h0]) (by rw [keep d _ Fd (by decide), h11]) rfl rfl
          (by omega) (by omega)
        refine ⟨d', k', e', ⟨e'.wb_right, Fd.trans F', by omega, by omega, ?_, ?_⟩, hk', by omega⟩
        · rw [q13', q20']; split_ifs <;> omega
        · intro i hi
          rw [q20'] at hi
          rw [q13']
          split_ifs with ht
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
            · exact (d4 i hi).trans ht.le
            · exact le_rfl
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
            · exact d4 i hi
            · exact not_lt.1 ht)
      hI₁
  have c23 : c₂.nreg 180023 = m + 1 := by rw [keep c₂ _ F₂ (by decide), h23]
  rw [c23] at hex
  refine ⟨c₂, _, .seq e₁ e₂, ?_, F₂, by omega, fun i hi => h₄ i (by omega)⟩
  rw [q20] at hk₂; omega

end

end Brute

end Chazelle.Core
