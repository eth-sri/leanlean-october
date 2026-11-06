module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRCost
public import Chazelle.Programs.Tactics

/-!
# Down-phase driver (RAM side), D1 part 3: the driver program and its straight-line pieces

Registers (band `bDownDrv = 21`, `210000 + i`): `210000` the level `λ`, `210006` the output
handle of the base case, `210007` the loop guard `g` (`λ` if `n₀ ≤ n`, else `0`), `210008` the
constant `15`, `210009` `n`, `210010` `n₀`, `210011` the setup handle `S`, `210012` a constant,
`210013` an address, `210014` `p`.  Band `23`: `coreReg 0 = 230000` (read), `coreReg 3 = 230003`
(written at the end).

```
downS sT sL sB n₀ := sT ; (lamP ; guardS n₀) ;
    while 15 < g do (sL ; lamNext ; guardS n₀) ;
    sB ; coreReg 3 := r210006
```

* `lamP`: `λ := p = m (S + 1)`;
* `lamNext`: `λ := m (S + p + 4 + λ) + 11 = ⌈λ/5⌉ + 11` (the `⌈i/5⌉` table of `SetupAt`);
* `guardS n₀`: `g := if n < n₀ then 0 else λ`, and the constant `15`.

Each piece gets an exec lemma with an exact cost, its outputs and its frame (only band-`21`
registers are written; `frame_drv`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## The program -/

/-- The guard: `g := if n < n₀ then 0 else λ`, and the constant `15`. -/
def guardS (n₀ : ℕ) : Stmt :=
  .seq (block [.inputSize 210009, .constN 210010 n₀, .constN 210008 15, .constN 210007 0])
    (.ifLtN 210009 210010 .skip (.instr (.copyN 210007 210000)))

/-- `λ := p`, read from the setup record (`m (S + 1)`). -/
def lamP : Stmt :=
  block [.copyN 210011 230000, .constN 210012 1, .addN 210013 210011 210012, .loadN 210000 210013]

/-- `λ := ⌈λ/5⌉ + 11`, read from the table `m (S + p + 4 + λ) = ⌈λ/5⌉` of the setup record. -/
def lamNext : Stmt :=
  block [.copyN 210011 230000, .constN 210012 1, .addN 210013 210011 210012,
    .loadN 210014 210013, .addN 210013 210011 210014, .constN 210012 4,
    .addN 210013 210013 210012, .addN 210013 210013 210000, .loadN 210000 210013,
    .constN 210012 11, .addN 210000 210000 210012]

/-- The body of the level loop. -/
def levelBody (sL : Stmt) (n₀ : ℕ) : Stmt := .seq sL (.seq lamNext (guardS n₀))

/-- The level loop. -/
def levelLoop (sL : Stmt) (n₀ : ℕ) : Stmt := .whileLtN 210008 210007 (levelBody sL n₀)

/-- **The down phase** from its components: transition `sT`, one level `sL`, base `sB`. -/
def downS (sT sL sB : Stmt) (n₀ : ℕ) : Stmt :=
  .seq sT (.seq (.seq lamP (guardS n₀))
    (.seq (levelLoop sL n₀) (.seq sB (.instr (.copyN 230003 210006)))))

/-! ## Registers -/

theorem rd_drv (c : Config) (i : ℕ) : rd c bDownDrv i = c.nreg (210000 + i) := rfl

/-- A configuration change writing only band-`21` registers is a frame of `{bDownDrv}`. -/
theorem frame_drv {c c' : Config} {k : ℕ}
    (hr : ∀ r, (r < 210000 ∨ 220000 ≤ r) → c'.nreg r = c.nreg r) (hm : c'.nmem = c.nmem)
    (hrr : c'.rreg = c.rreg) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    Frame {bDownDrv} c c' k := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC (by unfold ALLOC; omega)
  refine ⟨fun r hr' _ => hr r ?_, fun r _ => by rw [hrr], fun a _ => by rw [hm],
    fun a _ => by rw [hrm], ho, by omega, by omega⟩
  simp only [Finset.mem_singleton, bandOf, bDownDrv] at hr'
  omega

/-- The frame of the final copy into `coreReg 3`. -/
theorem frame_core {c c' : Config} {k : ℕ}
    (hr : ∀ r, r ≠ 230003 → c'.nreg r = c.nreg r) (hm : c'.nmem = c.nmem)
    (hrr : c'.rreg = c.rreg) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    Frame {bCore} c c' k := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC (by unfold ALLOC; omega)
  refine ⟨fun r hr' _ => hr r ?_, fun r _ => by rw [hrr], fun a _ => by rw [hm],
    fun a _ => by rw [hrm], ho, by omega, by omega⟩
  simp only [Finset.mem_singleton, bandOf, bCore] at hr'
  omega

/-! ## The pieces -/

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The guard.** -/
theorem guardS_exec (n₀ : ℕ) (c : Config) (hw : WordsBounded W c) (hn₀ : n₀ + 15 ≤ W)
    (hn : P.n ≤ W) :
    ∃ c' k, Exec P W (guardS n₀) c c' k ∧ k ≤ 7 ∧
      c'.nreg 210007 = (if n₀ ≤ P.n then c.nreg 210000 else 0) ∧ c'.nreg 210008 = 15 ∧
      (∀ r, (r < 210000 ∨ 220000 ≤ r) → c'.nreg r = c.nreg r) ∧
      (∀ r, 210001 ≤ r → r ≤ 210006 → c'.nreg r = c.nreg r) ∧ c'.nreg 210000 = c.nreg 210000 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold guardS
  refine spec_seq ?_
  exec_block
  all_goals try omega
  by_cases h : P.n < n₀
  · refine spec_ifLtN_true (by config_simp; omega) ?_
    refine spec_skip ‹_› ?_
    refine ⟨by omega, ?_, ?_, fun r hr => ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [Machine.upd_same, ite_eq_right (show ¬ n₀ ≤ P.n by omega)]
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other]
  · refine spec_ifLtN_false (by config_simp; omega) ?_
    refine spec_instr (Exec.copyN ‹_› 210007 210000) fun _ => ?_
    refine ⟨by omega, ?_, ?_, fun r hr => ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
        ite_eq_left (show n₀ ≤ P.n by omega)]
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

set_option maxHeartbeats 4000000 in
/-- **`λ := p`.** -/
theorem lamP_exec (c : Config) (hw : WordsBounded W c) {S : ℕ} (hS : c.nreg 230000 = S)
    (hSW : S + 1 ≤ W) :
    ∃ c' k, Exec P W lamP c c' k ∧ k = 4 ∧ c'.nreg 210000 = c.nmem (S + 1) ∧
      (∀ r, (r < 210000 ∨ 220000 ≤ r) → c'.nreg r = c.nreg r) ∧
      (∀ r, 210001 ≤ r → r ≤ 210010 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lamP
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hS]; omega)
  refine ⟨rfl, ?_, fun r hr => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hS]

set_option maxHeartbeats 4000000 in
/-- **`λ := ⌈λ/5⌉ + 11`** from the setup table. -/
theorem lamNext_exec (c : Config) (hw : WordsBounded W c) {S p lam : ℕ}
    (hS : c.nreg 230000 = S) (hp : c.nmem (S + 1) = p) (hl : c.nreg 210000 = lam)
    (hW1 : S + p + 4 + lam ≤ W) (hW2 : c.nmem (S + p + 4 + lam) + 11 ≤ W) :
    ∃ c' k, Exec P W lamNext c c' k ∧ k = 11 ∧
      c'.nreg 210000 = c.nmem (S + p + 4 + lam) + 11 ∧
      (∀ r, (r < 210000 ∨ 220000 ≤ r) → c'.nreg r = c.nreg r) ∧
      (∀ r, 210001 ≤ r → r ≤ 210010 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lamNext
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hS, hp, hl]; omega)
  refine ⟨rfl, ?_, fun r hr => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hS, hp, hl]

end exec

end

end DrvR

end Chazelle.Core
