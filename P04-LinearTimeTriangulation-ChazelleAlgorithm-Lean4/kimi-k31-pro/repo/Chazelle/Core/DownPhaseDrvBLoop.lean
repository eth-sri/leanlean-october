module

public import Chazelle.Core.DownPhaseDrvBPieces2
public import Chazelle.Core.DownPhaseDrvBBkt
public import Chazelle.Core.RestoreTRead
public import Chazelle.SimpTactics
set_option maxHeartbeats 4000000

/-!
# Down-phase base (D9): the region loop

`regLoopSpec_of (hS : RegStepSpec s κR) : RegLoopSpec`: the program
`regLoopS s = regInit; while r212014 < r212013 do s`.

* `regInit` (`regInit_exec`): the constants of `BRegs` (`liBit` normalised to `0/1`), the loop
  registers (`r212013 = K + 1`, `r212014 = 0`, `r216031 = RP 0`, `MX = 0`) and the empty output
  (`r216020 = 0`, `r216021 = B₂`, `r216022 = BK`): the state `RSt E 0` for the data `E` of the
  region loop (`regEnv`, the region correspondence from the validity of `buildNF`);
* the loop (`Restore.whileLtN_frame`): `RegStepSpec` for every region `r < K + 1`, the allocator
  staying below `A₀ + r · κR (S₀ + 1) (Cm + 1)`;
* `RegPost` from `RSt E (K + 1)` (`BEnv.TL_all`, `DrvB.bktMath`).
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs BuildRam SignK
open BuildNF (codeLe)

@[expose] public section

/-- The straight-line part of the initialisation. -/
def regInitB : Stmt :=
  block [.constN 212000 1, .constN 212001 0, .constN 212002 2, .inputSize 212010,
    .copyN 212012 210003, .constN 216002 1, .constN 216003 0, .constN 216005 2, .constN 216006 5,
    .constN 212020 4, .addN 212021 210005 212020, .loadN 216014 212021,
    .constN 212020 7, .addN 212021 210005 212020, .loadN 216016 212021,
    .addN 212021 210005 212000, .loadN 216017 212021,
    .constN 212020 5, .addN 212021 210005 212020, .loadN 216031 212021,
    .addN 216031 216031 212002,
    .addN 212013 212012 212000, .constN 212014 0, .constN 212018 0, .constN 216020 0,
    .copyN 216021 212019,
    .addN 216022 212019 212010, .addN 216022 216022 212010, .addN 216022 216022 212010,
    .addN 216022 216022 212010, .addN 216022 216022 212010, .addN 216022 216022 212010,
    .addN 212021 210001 212000, .loadN 212020 212021, .constN 212011 0]

/-- **The initialisation of the region loop.** -/
def regInit : Stmt :=
  .seq regInitB (.ifLtN 212020 212000 .skip (.ifLtN 212000 212020 .skip (block [.constN 212011 1])))

/-- **The region loop.** -/
def regLoopS (s : Stmt) : Stmt := .seq regInit (.whileLtN 212014 212013 s)

/-- The registers the initialisation writes. -/
def Binit (r : ℕ) : Bool :=
  decide ((212000 ≤ r ∧ r ≤ 212021 ∧ r ≠ 212019) ∨ (216000 ≤ r ∧ r ≤ 216031))

section init

variable {P : Polygon} {W : ℕ}

/-- **The initialisation.** -/
theorem regInit_exec (c : Config) (hw : WordsBounded W c) {MD K H B₂ : ℕ}
    (h01 : c.nreg 210001 = MD) (h03 : c.nreg 210003 = K) (h05 : c.nreg 210005 = H)
    (h19 : c.nreg 212019 = B₂) (hnW : P.n ≤ W) (h7 : 7 ≤ W) (hH : H + 7 ≤ W)
    (hRB : c.nmem (H + 5) + 2 ≤ W) (hK : K + 1 ≤ W) (hB : B₂ + 6 * P.n ≤ W) (hMD : MD + 1 ≤ W) :
    ∃ c' k, Exec P W regInit c c' k ∧ k ≤ 40 ∧
      c'.nreg 212000 = 1 ∧ c'.nreg 212001 = 0 ∧ c'.nreg 212002 = 2 ∧ c'.nreg 212010 = P.n ∧
      c'.nreg 212011 = (if c.nmem (MD + 1) = 1 then 1 else 0) ∧ c'.nreg 212012 = K ∧
      c'.nreg 216002 = 1 ∧ c'.nreg 216003 = 0 ∧ c'.nreg 216005 = 2 ∧ c'.nreg 216006 = 5 ∧
      c'.nreg 216014 = c.nmem (H + 4) ∧ c'.nreg 216016 = c.nmem (H + 7) ∧
      c'.nreg 216017 = c.nmem (H + 1) ∧ c'.nreg 216031 = c.nmem (H + 5) + 2 ∧
      c'.nreg 212013 = K + 1 ∧ c'.nreg 212014 = 0 ∧ c'.nreg 212018 = 0 ∧
      c'.nreg 216020 = 0 ∧ c'.nreg 216021 = B₂ ∧ c'.nreg 216022 = B₂ + 6 * P.n ∧
      FrameB Binit c c' := by
  obtain ⟨d1, k1, e1, hk1, a00, a01, a02, a10, a12, b02, b03, b05, b06, b14, b16, b17, b31, a13,
      a14, a18, b20, b21, b22, a20, a11⟩ : ∃ d1 k1, Exec P W regInitB c d1 k1 ∧ k1 ≤ 35 ∧
      d1.nreg 212000 = 1 ∧ d1.nreg 212001 = 0 ∧ d1.nreg 212002 = 2 ∧ d1.nreg 212010 = P.n ∧
      d1.nreg 212012 = K ∧ d1.nreg 216002 = 1 ∧ d1.nreg 216003 = 0 ∧ d1.nreg 216005 = 2 ∧
      d1.nreg 216006 = 5 ∧ d1.nreg 216014 = c.nmem (H + 4) ∧ d1.nreg 216016 = c.nmem (H + 7) ∧
      d1.nreg 216017 = c.nmem (H + 1) ∧ d1.nreg 216031 = c.nmem (H + 5) + 2 ∧
      d1.nreg 212013 = K + 1 ∧ d1.nreg 212014 = 0 ∧ d1.nreg 212018 = 0 ∧
      d1.nreg 216020 = 0 ∧ d1.nreg 216021 = B₂ ∧ d1.nreg 216022 = B₂ + 6 * P.n ∧
      d1.nreg 212020 = c.nmem (MD + 1) ∧ d1.nreg 212011 = 0 := by
    unfold regInitB
    exec_block
    all_goals (try (config_simp; simp (config := { failIfUnchanged := false }) only
      [h01, h03, h05, h19]; omega))
    all_goals (try (refine ⟨by omega, ?_⟩))
    all_goals (repeat' apply And.intro)
    all_goals (config_simp <;> simp (config := { failIfUnchanged := false }) only
      [h01, h03, h05, h19])
    all_goals omega
  have f1 : FrameB Binit c d1 := exec_frameB e1 (by decide)
  have hw1 := e1.wb_right
  obtain ⟨d2, k2, e2, hk2, v11, f2⟩ : ∃ d2 k2, Exec P W
      (.ifLtN 212020 212000 .skip (.ifLtN 212000 212020 .skip (block [.constN 212011 1]))) d1 d2 k2 ∧
      k2 ≤ 5 ∧ d2.nreg 212011 = (if c.nmem (MD + 1) = 1 then 1 else 0) ∧
      FrameB (fun r => decide (r = 212011)) d1 d2 := by
    obtain ⟨d2, k2, e2, hk2, v⟩ : ∃ d2 k2, Exec P W
        (.ifLtN 212020 212000 .skip (.ifLtN 212000 212020 .skip (block [.constN 212011 1])))
        d1 d2 k2 ∧ k2 ≤ 5 ∧ d2.nreg 212011 = (if c.nmem (MD + 1) = 1 then 1 else 0) := by
      by_cases c1 : d1.nreg 212020 < d1.nreg 212000
      · exact ⟨d1, 0 + 1, .ifLtN_true c1 (.skip hw1), by omega,
          by rw [a11, ite_eq_right (by omega)]⟩
      · by_cases c2 : d1.nreg 212000 < d1.nreg 212020
        · exact ⟨d1, 0 + 1 + 2, .ifLtN_false c1 (.ifLtN_true c2 (.skip hw1)), by omega,
            by rw [a11, ite_eq_right (by omega)]⟩
        · refine spec_ifLtN_false c1 ?_
          refine spec_ifLtN_false c2 ?_
          exec_block
          · omega
          · refine ⟨by omega, ?_⟩
            config_simp
            rw [ite_eq_left (by omega)]
    exact ⟨d2, k2, e2, hk2, v, exec_frameB e2 (by decide)⟩
  have g : ∀ r, r ≠ 212011 → d2.nreg r = d1.nreg r := fun r hr =>
    f2.1 r (by simp [decide_eq_false_iff_not]; exact hr)
  refine ⟨d2, k1 + k2, .seq e1 e2, by omega, by rw [g _ (by decide), a00],
    by rw [g _ (by decide), a01], by rw [g _ (by decide), a02], by rw [g _ (by decide), a10], v11,
    by rw [g _ (by decide), a12], by rw [g _ (by decide), b02], by rw [g _ (by decide), b03],
    by rw [g _ (by decide), b05], by rw [g _ (by decide), b06], by rw [g _ (by decide), b14],
    by rw [g _ (by decide), b16], by rw [g _ (by decide), b17], by rw [g _ (by decide), b31],
    by rw [g _ (by decide), a13], by rw [g _ (by decide), a14], by rw [g _ (by decide), a18],
    by rw [g _ (by decide), b20], by rw [g _ (by decide), b21], by rw [g _ (by decide), b22],
    f1.trans ⟨fun r hr => f2.1 r (by sio only [Binit, decide_eq_false_iff_not] at hr ⊢),
      fun r hr => f2.2.1 r (by sio only [Binit, decide_eq_false_iff_not] at hr ⊢),
      f2.2.2⟩⟩

end init

end

end DrvB

end Chazelle.Core
