module

public import Chazelle.Core.SweepIoAsm

/-!
# The sweep RAM (WP-D), the assembly (piece I), part 2: the initialisation of the answers

`ansInit` (after stages 2/3): the constants `K0 … K6`, the model descriptors of `C₁`, `C₂` again
(`mdBlk`, so that `AEnv.hmd₁`, `AEnv.hmd₂` hold), the side `sSide := sw 99` (saved on entry), and
the table of powers `2 ^ j` at `TBR := ALLOC` for `j < TLR`, the least `TLR` with
`64 (K₁ + K₂ + 1) ≤ 2 ^ TLR` (so `TLR ≤ ⌈log₂ (K₁ + K₂ + 1)⌉ + 6`).  `ansInit_exec`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim

@[expose] public section

/-! ## Registers and program -/

def tT : ℕ := sw 700
def tV : ℕ := sw 701
def tN : ℕ := sw 702
def tA : ℕ := sw 703
def tB : ℕ := sw 704

/-- The constants `K0 … K6`. -/
def ksL : List Instr :=
  [.constN K0 0, .constN K1 1, .constN K6 6, .constN K4 4, .constN K5 5, .constN K2 2, .constN K3 3]

/-- The side, `64 (K₁ + K₂ + 1)`, the table base, the counters. -/
def tHead : List Instr :=
  [.copyN sSide (sw 99), .loadN tA (sw 3), .loadN tB (sw 4), .addN tN tA tB, .addN tN tN K1,
    .addN tN tN tN, .addN tN tN tN, .addN tN tN tN, .addN tN tN tN, .addN tN tN tN,
    .addN tN tN tN, .copyN TBR ALLOC, .constN tT 0, .constN tV 1]

/-- One entry of the table. -/
def tBody : List Instr :=
  [.storeN ALLOC tV, .addN ALLOC ALLOC K1, .addN tV tV tV, .addN tT tT K1]

/-- **The initialisation of the answers.** -/
def ansInit : Stmt :=
  .seq (block ksL) (.seq mdBlk (.seq (block tHead)
    (.seq (.whileLtN tV tN (block tBody)) (block [.copyN TLR tT]))))

variable {P : Polygon} {W : ℕ}

/-! ## The blocks -/

theorem ksL_exec (c : Config) (hw : WordsBounded W c) (hW : 6 ≤ W) :
    ∃ c' k, Exec P W (block ksL) c c' k ∧ k = 7 ∧ Consts c' ∧
      (∀ r, (r < K0 ∨ K3 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ksL Consts K0 K1 K2 K3 K4 K5 K6
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  all_goals try omega
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;> config_simp
  simp only [upd]
  rw [ite_eq_right by_o, ite_eq_right by_o, ite_eq_right by_o, ite_eq_right by_o,
    ite_eq_right by_o, ite_eq_right by_o, ite_eq_right by_o]

theorem tHead_exec (c : Config) (hw : WordsBounded W c) (hk1 : c.nreg K1 = 1) {n : ℕ}
    (hn : c.nmem (c.nreg (sw 3)) + c.nmem (c.nreg (sw 4)) + 1 = n) (hW : 64 * n ≤ W) :
    ∃ c' k, Exec P W (block tHead) c c' k ∧ k = 14 ∧ c'.nreg sSide = c.nreg (sw 99) ∧
      c'.nreg tN = 64 * n ∧ c'.nreg TBR = c.nreg ALLOC ∧ c'.nreg tT = 0 ∧ c'.nreg tV = 1 ∧
      (∀ r, r ≠ sSide → r ≠ tA → r ≠ tB → r ≠ tN → r ≠ TBR → r ≠ tT → r ≠ tV →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tHead sSide tA tB tN TBR tT tV ALLOC K1 at *
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; omega
  · config_simp
  · config_simp
  · config_simp
  · config_simp
    simp [upd, h1, h2, h3, h4, h5, h6, h7]

theorem tBody_exec (c : Config) (hw : WordsBounded W c) (hk1 : c.nreg K1 = 1)
    (h1 : c.nreg ALLOC + 1 ≤ W) (h2 : c.nreg tV + c.nreg tV ≤ W) (h3 : c.nreg tT + 1 ≤ W) :
    ∃ c' k, Exec P W (block tBody) c c' k ∧ k = 4 ∧ c'.nreg ALLOC = c.nreg ALLOC + 1 ∧
      c'.nreg tV = c.nreg tV + c.nreg tV ∧ c'.nreg tT = c.nreg tT + 1 ∧
      (∀ r, r ≠ ALLOC → r ≠ tV → r ≠ tT → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (c.nreg ALLOC) (c.nreg tV) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tBody tT tV ALLOC K1 at *
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, rfl, rfl, rfl⟩
  · config_simp; omega
  · config_simp
  · config_simp; omega
  · config_simp
    simp [upd, h1, h2, h3]
  · config_simp

/-! ## The table loop -/

theorem pow_clog64 (n : ℕ) : 64 * n ≤ 2 ^ (Nat.clog 2 n + 6) := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) n
  rw [pow_add]; norm_num; omega

theorem lt_of_pow_lt {t n : ℕ} (h : 2 ^ t < 64 * n) : t < Nat.clog 2 n + 6 := by
  by_contra hc
  push Not at hc
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc
  have := pow_clog64 n
  omega

/-- The invariant of the table loop (base `A`, bound `Λ = ⌈log₂ n⌉`). -/
abbrev tInv (A Λ n : ℕ) (c' : Config) : Prop :=
  c'.nreg tV = 2 ^ c'.nreg tT ∧ c'.nreg ALLOC = A + c'.nreg tT ∧
    (∀ i, i < c'.nreg tT → c'.nmem (A + i) = 2 ^ i) ∧ c'.nreg tT ≤ Λ + 6 ∧ c'.nreg tN = 64 * n

set_option maxRecDepth 20000 in
/-- **The table loop.** -/
theorem tLoop_exec (c : Config) (hw : WordsBounded W c) (hk1 : c.nreg K1 = 1) {n : ℕ}
    (htN : c.nreg tN = 64 * n) (htT : c.nreg tT = 0) (htV : c.nreg tV = 1)
    (hW1 : c.nreg ALLOC + 6 * (Nat.clog 2 n + 6) ≤ W) (hW2 : 128 * n ≤ W)
    (hW3 : Nat.clog 2 n + 7 ≤ W) :
    ∃ c' k, Exec P W (.whileLtN tV tN (block tBody)) c c' k ∧ k ≤ 6 * (Nat.clog 2 n + 6) + 2 ∧
      c'.nreg ALLOC = c.nreg ALLOC + c'.nreg tT ∧ 64 * n ≤ 2 ^ c'.nreg tT ∧
      c'.nreg tT ≤ Nat.clog 2 n + 6 ∧
      (∀ i, i < c'.nreg tT → c'.nmem (c.nreg ALLOC + i) = 2 ^ i) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧
      (∀ j, j < 700 → c'.nreg (sw j) = c.nreg (sw j)) ∧
      (∀ r, bandOf r ∉ ioBands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ioBands → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  have hI0 : IInv W c c := ⟨hw, fun _ _ => rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  set A := c.nreg ALLOC with hA
  set Λ := Nat.clog 2 n with hΛ
  have hI : tInv A Λ n c := ⟨by rw [htV, htT]; rfl, by rw [htT]; omega, fun i hi => by rw [htT] at hi; omega,
    by rw [htT]; omega, htN⟩
  have hiK : ∀ c', IInv W c c' → c'.nreg K1 = 1 := fun c' h' => by
    rw [h'.hin _ (by unfold IFix K1 sw; omega)]; exact hk1
  have hw' := IRS.while (P := P) (c₀ := c) (a := tV) (b := tN) (body := block tBody) (tInv A Λ n)
    (fun c' => Λ + 6 - c'.nreg tT) 4
    (fun c' hc' hlt => by
      obtain ⟨h1, -, -, -, h5⟩ := hc'
      rw [h1, h5] at hlt
      have := lt_of_pow_lt hlt
      omega)
    (fun c' hI' hc' hlt hroom => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hc'
      have hlt' : 2 ^ c'.nreg tT < 64 * n := by rw [← h1, ← h5]; exact hlt
      have htl := lt_of_pow_lt hlt'
      obtain ⟨c'', k, ex, hk, a1, aV, aT, ar, am, arr, arm, ao⟩ :=
        tBody_exec (P := P) c' hI'.hw (hiK c' hI') by_o (by rw [h1]; omega) by_o
      refine IRS.ofExec hI' ex by_o (fun r hr hra => ar r hra ?_ ?_) arr (fun a ha => ?_)
        arm ao by_o by_o ⟨⟨?_, ?_, fun i hi => ?_, ?_, ?_⟩, ?_⟩ |>.mono le_rfl
        (fun _ h => h)
      · intro h; subst h; exact hr (iscr_sw by_d by_d)
      · intro h; subst h; exact hr (iscr_sw by_d by_d)
      · rw [am, upd_other _ _ _ (by have := hI'.hA; omega)]
      · rw [aV, aT, h1, pow_succ]; ring
      · rw [a1, aT, h2]; ring
      · rw [aT] at hi
        rw [am]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · rw [upd_other _ _ _ by_o]; exact h3 i hi
        · rw [h2, upd_same, h1]
      · rw [aT]; omega
      · rwa [ar _ (by unfold tN ALLOC sw; omega) (by unfold tN tV sw; omega)
          (by unfold tN tT sw; omega)]
      · show Λ + 6 - c''.nreg tT < Λ + 6 - c'.nreg tT
        rw [aT]; omega)
    hI0 hI (by show A + (4 + 2) * (Λ + 6 - c.nreg tT) ≤ W; rw [htT]; omega)
  obtain ⟨c', k, ex, hk, hI', hfr, ⟨h1, h2, h3, h4, h5⟩, hex⟩ := hw'
  rw [htT] at hk
  refine ⟨c', k, ex, by_o, h2, ?_, h4, h3, hI'.hm, hI'.hrm, fun j hj => hI'.hin _ (by
    unfold IFix sw; omega), hfr.1, hfr.2.1, hfr.2.2.1, hfr.2.2.2.2⟩
  rw [← h1, ← h5]; omega

/-! ## The initialisation -/

theorem copy1_exec (c : Config) (hw : WordsBounded W c) (d s : ℕ) :
    ∃ c' k, Exec P W (block [.copyN d s]) c c' k ∧ k = 1 ∧ c'.nreg d = c.nreg s ∧
      (∀ r, r ≠ d → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, by config_simp, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  config_simp; simp [upd, hr]

theorem sw_band {r : ℕ} (hr : bandOf r ∉ sweepBands ∪ oracleBands) (j : ℕ) (hj : j < 10000) :
    r ≠ sw j := by
  rintro rfl
  apply hr
  rw [band_sw by_so by_so]
  exact bSweep_mem

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **The initialisation of the answers.** -/
theorem ansInit_exec (c : Config) (hw : WordsBounded W c) (h90 : c.nreg (sw 90) = 0)
    (h91 : c.nreg (sw 91) = 1) (s20 : c.nreg (sw 20) + 5 ≤ c.nreg ALLOC)
    (s21 : c.nreg (sw 21) + 5 ≤ c.nreg ALLOC) (b3 : c.nreg (sw 3) < c.nreg ALLOC)
    (b4 : c.nreg (sw 4) < c.nreg ALLOC) {n : ℕ}
    (hn : c.nmem (c.nreg (sw 3)) + c.nmem (c.nreg (sw 4)) + 1 = n)
    (hW1 : c.nreg ALLOC + 100 + 6 * (Nat.clog 2 n + 6) ≤ W) (hW2 : 128 * n ≤ W) :
    ∃ c' k, Exec P W ansInit c c' k ∧ k ≤ 100 + 6 * (Nat.clog 2 n + 6) ∧
      Frame (sweepBands ∪ oracleBands) c c' k ∧
      Consts c' ∧ c'.nreg sSide = c.nreg (sw 99) ∧
      c'.nreg (sw 30) = c.nreg ALLOC ∧ c'.nreg (sw 31) = c.nreg ALLOC + 6 ∧
      c'.nmem (c.nreg ALLOC) = 0 ∧
      (∀ j, j < 5 → c'.nmem (c.nreg ALLOC + 1 + j) = c.nmem (c.nreg (sw 20) + j)) ∧
      c'.nmem (c.nreg ALLOC + 6) = 0 ∧
      (∀ j, j < 5 → c'.nmem (c.nreg ALLOC + 6 + 1 + j) = c.nmem (c.nreg (sw 21) + j)) ∧
      c'.nreg TBR = c.nreg ALLOC + 12 ∧ c'.nreg ALLOC = c'.nreg TBR + c'.nreg TLR ∧
      64 * n ≤ 2 ^ c'.nreg TLR ∧ c'.nreg TLR ≤ Nat.clog 2 n + 6 ∧
      (∀ i, i < c'.nreg TLR → c'.nmem (c'.nreg TBR + i) = 2 ^ i) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ j, j < 700 → j ≠ 30 → j ≠ 31 → j ≠ 96 → j ≠ 97 → j ≠ 98 → j ≠ 600 → j ≠ 601 →
        (j < 610 ∨ 616 < j) → c'.nreg (sw j) = c.nreg (sw j)) := by
  set A := c.nreg ALLOC with hA
  have nA : ∀ j, sw j ≠ ALLOC := fun j => by unfold sw ALLOC; omega
  -- 1. the constants
  obtain ⟨c₁, k₁, e₁, hk₁, hK₁, r₁, m₁, rr₁, rm₁, o₁⟩ := ksL_exec (P := P) c hw by_o
  have q₁ : ∀ j, (j < 610 ∨ 616 < j) → c₁.nreg (sw j) = c.nreg (sw j) := fun j hj =>
    r₁ _ (by unfold K0 K3 sw; omega)
  have A₁ : c₁.nreg ALLOC = A := r₁ _ (by unfold K0 ALLOC sw; omega)
  -- 2. the model descriptors
  obtain ⟨c₂, k₂, e₂, hk₂, zA, z30, z31, z0, zq, z6, zl, zlo, zr, zrr, zrm, zo⟩ :=
    mdBlk_exec (P := P) c₁ e₁.wb_right (by rw [q₁ 90 by_o, h90])
      (by rw [q₁ 91 by_o, h91]) (by rwa [q₁ 20 by_o, A₁])
      (by rwa [q₁ 21 by_o, A₁]) (by rw [A₁]; omega)
  rw [A₁] at zA z30 z31 z0 zq z6 zl zlo
  rw [q₁ 20 by_o, m₁] at zq
  rw [q₁ 21 by_o, m₁] at zl
  rw [m₁] at zlo
  have q₂ : ∀ j, j < 10000 → j ≠ 30 → j ≠ 31 → j ≠ 96 → j ≠ 97 → j ≠ 98 →
      c₂.nreg (sw j) = c₁.nreg (sw j) := fun j hj h1 h2 h3 h4 h5 =>
    zr _ (nA j) by_so by_so by_so
      by_so by_so
  have hK₂ : c₂.nreg K1 = 1 := by
    rw [show K1 = sw 611 from rfl, q₂ 611 by_o by_o by_o by_o by_o
      by_o]; exact hK₁.2.1
  -- 3. the head of the table
  obtain ⟨c₃, k₃, e₃, hk₃, t98, tN3, tB3, tT3, tV3, tr, tm, trr, trm, tout⟩ :=
    tHead_exec (P := P) c₂ e₂.wb_right hK₂ (n := n) (by
      rwa [q₂ 3 by_o by_o by_o by_o by_o by_o,
        q₂ 4 by_o by_o by_o by_o by_o by_o,
        q₁ 3 by_o, q₁ 4 by_o, zlo _ b3, zlo _ b4]) by_o
  have q₃ : ∀ j, j < 10000 → j ≠ 98 → j ≠ 703 → j ≠ 704 → j ≠ 702 → j ≠ 600 → j ≠ 700 →
      j ≠ 701 → c₃.nreg (sw j) = c₂.nreg (sw j) := fun j hj h1 h2 h3 h4 h5 h6 h7 =>
    tr _ (by unfold sSide sw; omega) (by unfold tA sw; omega) (by unfold tB sw; omega)
      (by unfold tN sw; omega) (by unfold TBR sw; omega) (by unfold tT sw; omega)
      (by unfold tV sw; omega)
  have A₃ : c₃.nreg ALLOC = A + 12 := by
    rw [tr _ (by unfold sSide ALLOC sw; omega) (by unfold tA ALLOC sw; omega)
      (by unfold tB ALLOC sw; omega) (by unfold tN ALLOC sw; omega) (by unfold TBR ALLOC sw; omega)
      (by unfold tT ALLOC sw; omega) (by unfold tV ALLOC sw; omega), zA]
  have hK₃ : c₃.nreg K1 = 1 := by
    rwa [show K1 = sw 611 from rfl, q₃ 611 by_o by_o by_o by_o by_o
      by_o by_o by_o]
  -- 4. the loop
  obtain ⟨c₄, k₄, e₄, hk₄, l1, l2, l3, l4, lm, lrm, lsw, lr, lrr, lo, lA⟩ :=
    tLoop_exec (P := P) c₃ e₃.wb_right hK₃ tN3 tT3 tV3 (by rw [A₃]; omega) hW2 by_o
  -- 5. `TLR := tT`
  obtain ⟨c₅, k₅, e₅, hk₅, v5, r5, m5, rr5, rm5, o5⟩ := copy1_exec (P := P) c₄ e₄.wb_right TLR tT
  have ex : Exec P W ansInit c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have q₅ : ∀ j, j < 700 → j ≠ 601 → c₅.nreg (sw j) = c₄.nreg (sw j) := fun j hj h =>
    r5 _ (by unfold TLR sw; omega)
  have A₅ : c₅.nreg ALLOC = c₄.nreg ALLOC := r5 _ (by unfold TLR ALLOC sw; omega)
  have TB₅ : c₅.nreg TBR = A + 12 := by
    rw [show TBR = sw 600 from rfl, q₅ 600 by_o by_o, lsw 600 by_o]
    exact tB3.trans zA
  have TL₅ := v5
  -- memory
  have mem5 : ∀ a, a < A + 12 → c₅.nmem a = c₂.nmem a := fun a ha => by
    rw [m5, lm a (by rwa [A₃]), tm]
  refine ⟨c₅, _, ex, by_o, ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_,
    ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, TB₅, ?_, ?_, ?_,
    fun i hi => ?_, fun a ha => ?_, fun j hj h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
  · -- registers outside the bands
    have hT : r ≠ TLR := sw_band hr 601 by_o
    rw [r5 r hT, lr r (fun h => hr h) hra,
      tr r (sw_band hr 98 by_o) (sw_band hr 703 by_o) (sw_band hr 704 by_o)
        (sw_band hr 702 by_o) (sw_band hr 600 by_o) (sw_band hr 700 by_o)
        (sw_band hr 701 by_o),
      zr r hra (sw_band hr 30 by_o) (sw_band hr 31 by_o) (sw_band hr 96 by_o)
        (sw_band hr 97 by_o) (sw_band hr 98 by_o),
      r₁ r ?_]
    unfold K0 K3 sw
    by_contra hc
    push Not at hc
    apply hr
    rw [band_sw by_o by_o]
    exact bSweep_mem
  · rw [rr5, lrr r (fun h => hr h), trr, zrr, rr₁]
  · rw [mem5 a by_o, zlo a ha]
  · rw [rm5, lrm a (by rw [A₃]; omega), trm, zrm, rm₁]
  · rw [o5, lo, tout, zo, o₁]
  · rw [A₅]; omega
  · rw [A₅]; omega
  · -- the constants
    have k : ∀ j, 610 ≤ j → j ≤ 616 → c₅.nreg (sw j) = c₁.nreg (sw j) := fun j h1 h2 => by
      rw [q₅ j by_o by_o, lsw j by_o,
        q₃ j by_o by_o by_o by_o by_o by_o by_o by_o,
        q₂ j by_o by_o by_o by_o by_o by_o]
    obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK₁
    exact ⟨(k 610 le_rfl by_o).trans k0, (k 611 by_o by_o).trans k1,
      (k 612 by_o by_o).trans k6, (k 613 by_o by_o).trans k4,
      (k 614 by_o by_o).trans k5, (k 615 by_o by_o).trans k2,
      (k 616 by_o le_rfl).trans k3⟩
  · rw [show sSide = sw 98 from rfl, q₅ 98 by_o by_o, lsw 98 by_o]
    rw [show sw 98 = sSide from rfl, t98, q₂ 99 by_o by_o by_o by_o by_o by_o,
      q₁ 99 by_o]
  · rw [q₅ 30 by_o by_o, lsw 30 by_o,
      q₃ 30 by_o by_o by_o by_o by_o by_o by_o by_o,
      z30]
  · rw [q₅ 31 by_o by_o, lsw 31 by_o,
      q₃ 31 by_o by_o by_o by_o by_o by_o by_o by_o,
      z31]
  · rwa [mem5 _ by_o]
  · rw [mem5 _ by_o]; exact zq j hj
  · rwa [mem5 _ by_o]
  · rw [mem5 _ by_o]; exact zl j hj
  · rw [A₅, TB₅, TL₅, l1, A₃]
  · rwa [TL₅]
  · rwa [TL₅]
  · rw [TL₅] at hi
    rw [TB₅, m5, ← A₃]; exact l4 i hi
  · rw [mem5 a by_o, zlo a ha]
  · rw [q₅ j hj h7, lsw j hj,
      q₃ j by_o h5 by_o by_o by_o h6 by_o by_o,
      q₂ j by_o h1 h2 h3 h4 h5, q₁ j h8]

end

end SweepIo

end Chazelle.Core
