module

public import Chazelle.Core.DownPhaseDrvBSpec
public import Chazelle.Core.DownPhaseDrvDRound3
public import Chazelle.Core.DownPhaseBaseMain
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ConfigTactics
set_option maxHeartbeats 2000000

/-!
# Down-phase base (D9), top level, part 1: the program and its straight-line pieces

`topS sR sD sB` (`sR` the region loop of `RegLoopSpec`, `sD` the program of `DropAugSpec`, `sB`
the program of `BuildNFSortedSpec`):

1. `tPre`: `B₂ := ALLOC` (register `212019`), `n`, the constants of the reservation;
2. `tRes`: reserve `10 n` words at the allocator (five words per step, `2 n` steps), so the
   area `[B₂, B₂ + 10 n)` of the region loop lies below the allocator;
3. `sR`: the region loop (new chords `L₂` at `B₂`, their number in `216020`, their buckets at
   `B₂ + 6 n`, the bucket bound `MX` in `212018`);
4. `tArgs`: the arguments of the splice (`210020 = B₂`, `210021 = K₂`, `210022 = B₂ + 6 n`,
   `210023` the number of arcs `mem[H + 1]`, `210024 = 4 MX`);
5. `DrvR.splS sB`: the splice (new `L ++ L₂`, its sorted events and normal form);
6. `tDrop`, `sD`: drop the chords that are not vertex chords (`dropAug`);
7. `tBld`, `sB`: the normal form of the kept chords (`buildNFSorted`);
8. `tOut`: its handle into register `210006`.

Registers of the top level (band `bDownDrv`): `219300 … 219307` (scratch), `212019` (`B₂`),
the splice's `210020 … 210024`; `200000 … 200003` (band `bDown`) and `40000 … 40004`
(band `bBuild`) as arguments.
-/

namespace Chazelle.Core

namespace DrvB.BTop

open Machine Machine.Stmt Programs SignK BuildRam

@[expose] public section

/-- `B₂ := ALLOC`, `n`, the constant `1`, the counter, the target `2 n` of the reservation. -/
def tPre : Stmt := block [.copyN 212019 9999, .inputSize 219300, .constN 219301 1,
  .constN 219302 0, .addN 219303 219300 219300]

/-- Reserve five words. -/
def tResBody : Stmt := block [.addN 9999 9999 219301, .addN 9999 9999 219301,
  .addN 9999 9999 219301, .addN 9999 9999 219301, .addN 9999 9999 219301,
  .addN 219302 219302 219301]

/-- The reservation loop (`10 n` words). -/
def tRes : Stmt := .whileLtN 219302 219303 tResBody

/-- The arguments of the splice. -/
def tArgs : Stmt := block [.copyN 210020 212019, .copyN 210021 216020, .inputSize 219300,
  .addN 219304 219300 219300, .addN 219305 219304 219304, .addN 219305 219305 219304,
  .addN 210022 212019 219305, .constN 219306 1, .addN 219307 210005 219306,
  .loadN 210023 219307, .addN 210024 212018 212018, .addN 210024 210024 210024]

/-- The arguments of `dropAug`. -/
def tDrop : Stmt := block [.copyN 200000 210001, .copyN 200001 210002, .copyN 200002 210003,
  .copyN 200003 210004]

/-- The arguments of `buildNFSorted`. -/
def tBld : Stmt := block [.copyN 40000 210001, .copyN 40001 200004, .copyN 40002 200005,
  .copyN 40004 200006]

/-- The output handle. -/
def tOut : Stmt := block [.copyN 210006 40003]

/-- **The top level of the base case.** -/
def topS (sR sD sB : Stmt) : Stmt :=
  .seq tPre (.seq tRes (.seq sR (.seq tArgs (.seq (DrvR.splS sB) (.seq tDrop (.seq sD
    (.seq tBld (.seq sB tOut))))))))

/-! ## Write sets -/

/-- The registers `tPre` writes. -/
def Bpre (r : ℕ) : Bool := decide (r = 212019) || decide (219300 ≤ r ∧ r ≤ 219303)

/-- The registers of the reservation. -/
def Bres (r : ℕ) : Bool := decide (r = 219302) || decide (r = 9999)

/-- The registers `tArgs` writes. -/
def Bargs (r : ℕ) : Bool := decide (210020 ≤ r ∧ r ≤ 210024) || decide (219300 ≤ r ∧ r ≤ 219307)

theorem bres_false {r : ℕ} (h1 : r ≠ 219302) (h2 : r ≠ 9999) : Bres r = false := by
  simp only [Bres, Bool.or_eq_false_iff, decide_eq_false_iff_not]; exact ⟨h1, h2⟩

theorem bpre_false {r : ℕ} (h1 : r ≠ 212019) (h2 : r < 219300 ∨ 219303 < r) : Bpre r = false := by
  sio only [Bpre, Bool.or_eq_false_iff, decide_eq_false_iff_not]

theorem bargs_false {r : ℕ} (h1 : r < 210020 ∨ 210024 < r) (h2 : r < 219300 ∨ 219307 < r) :
    Bargs r = false := by
  sio only [Bargs, Bool.or_eq_false_iff, decide_eq_false_iff_not]

theorem inDrv_pre : DrvD.InDrv Bpre := by
  intro r hr
  simp only [Bpre, Bool.or_eq_true, decide_eq_true_eq] at hr
  exact ⟨DrvD.mem_drvBands (by omega) (by omega), by ufo ALLOC⟩

theorem inDrv_args : DrvD.InDrv Bargs := by
  intro r hr
  simp only [Bargs, Bool.or_eq_true, decide_eq_true_eq] at hr
  exact ⟨DrvD.mem_drvBands (by omega) (by omega), by ufo ALLOC⟩

theorem inDrv_drop : DrvD.InDrv (fun r => decide (200000 ≤ r ∧ r ≤ 200003)) := by
  intro r hr
  simp only [decide_eq_true_eq] at hr
  exact ⟨DrvD.mem_drvBands (by omega) (by omega), by ufo ALLOC⟩

theorem inDrv_bld : DrvD.InDrv (fun r => decide (40000 ≤ r ∧ r ≤ 40004)) := by
  intro r hr
  simp only [decide_eq_true_eq] at hr
  exact ⟨DrvD.mem_drvBands (by omega) (by omega), by ufo ALLOC⟩

section exec

variable {P : Polygon} {W : ℕ}

/-- `tPre`. -/
theorem tPre_exec (c : Config) (hw : WordsBounded W c) (hW : 2 * P.n + 1 ≤ W) :
    ∃ c' k, Exec P W tPre c c' k ∧ k = 5 ∧ c'.nreg 212019 = c.nreg ALLOC ∧
      c'.nreg 219301 = 1 ∧ c'.nreg 219302 = 0 ∧ c'.nreg 219303 = 2 * P.n ∧
      FrameB Bpre c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tPre c c' k ∧ k = 5 ∧
      (c'.nreg 212019 = c.nreg ALLOC ∧ c'.nreg 219301 = 1 ∧ c'.nreg 219302 = 0 ∧
        c'.nreg 219303 = 2 * P.n) := by
    unfold tPre
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    all_goals config_simp
    all_goals (try rfl)
    all_goals omega
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2, exec_frameB ex (by decide)⟩

/-- **The reservation** of `5 R` words. -/
theorem tRes_exec {c : Config} (hw : WordsBounded W c) {R : ℕ} (h03 : c.nreg 219303 = R)
    (h02 : c.nreg 219302 = 0) (h01 : c.nreg 219301 = 1) (hW : c.nreg ALLOC + 5 * R + 1 ≤ W)
    (A₀ : ℕ) :
    ∃ c' k, Exec P W tRes c c' k ∧ k ≤ 8 * R + 2 ∧ c'.nreg ALLOC = c.nreg ALLOC + 5 * R ∧
      FrameB Bres c c' ∧ Restore.RF DrvR.drvBands A₀ c c' k := by
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded W e ∧ e.nreg 219302 = j ∧
    e.nreg 219303 = R ∧ e.nreg 219301 = 1 ∧ e.nreg ALLOC = c.nreg ALLOC + 5 * j ∧
    FrameB Bres c e ∧ j ≤ R
  have key : ∀ j e, j < R → Inv j e → ∃ e' k, Exec P W tResBody e e' k ∧ Inv (j + 1) e' ∧
      Restore.RF DrvR.drvBands A₀ e e' k ∧ k = 6 := by
    intro j e hj ⟨hw, h1, h2, h3, h4, hf, _⟩
    have h4' : e.nreg 9999 = c.nreg ALLOC + 5 * j := h4
    obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W tResBody e e' k ∧ k = 6 ∧
        (e'.nreg 219302 = j + 1 ∧ e'.nreg 9999 = c.nreg ALLOC + 5 * (j + 1)) := by
      unfold tResBody
      exec_block
      all_goals try (config_simp; (try simp only [h1, h3, h4']); omega)
      refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> simp only [h1, h3, h4']; omega
    have hf' : FrameB Bres e e' := exec_frameB ex (by decide)
    have hnot : ∀ r, bandOf r ∉ DrvR.drvBands → r ≠ ALLOC → Bres r = false := fun r hr hra => by
      simp only [Bres, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨fun h => hr (by rw [h]; exact DrvD.mem_drvBands (by norm_num) (by norm_num)), hra⟩
    refine ⟨e', k, ex, ⟨ex.wb_right, q.1, (hf'.1 _ (by decide)).trans h2,
      (hf'.1 _ (by decide)).trans h3, by show e'.nreg 9999 = _; rw [q.2], hf.trans hf', hj⟩,
      ⟨fun r hr hra => hf'.1 r (hnot r hr hra), fun r _ =>
        WalkKey.exec_rframe ex (B := fun _ => false) (by decide) r rfl, fun a _ => by rw [hf'.2.2.1],
        fun a _ => by rw [hf'.2.2.2.1], hf'.2.2.2.2, by show e.nreg 9999 ≤ e'.nreg 9999; omega,
        by show e'.nreg 9999 ≤ e.nreg 9999 + k; omega⟩, hk⟩
  have I0 : Inv 0 c := ⟨hw, h02, h03, h01, by simp, FrameB.refl _ _, Nat.zero_le _⟩
  obtain ⟨c', k, ex, ⟨j, w', h1, h2, -, h4, hf, hjle⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame
    (P := P) (W := W) (a := 219302) (b := 219303) (body := tResBody) (B := DrvR.drvBands)
    (A₀ := A₀) (fun e => ∃ j, Inv j e) (fun e => R - e.nreg 219302) 6 (fun e ⟨_, h⟩ => h.1)
    (fun e ⟨j, hI⟩ ht => by
      obtain ⟨hw, h1, h2, -⟩ := id hI
      rw [h1, h2] at ht
      obtain ⟨e', k, ex, hI', RF', hk⟩ := key j e ht hI
      exact ⟨e', k, ex, ⟨j + 1, hI'⟩, RF', by omega, by rwo [h1, hI'.2.1]⟩) ⟨0, I0⟩
  have hjR : j = R := by rwo [h1, h2] at hx
  subst hjR
  refine ⟨c', k, ex, ?_, h4, hf, RFl⟩
  rw [h02] at hk
  simpa using hk

/-- `tArgs`. -/
theorem tArgs_exec (c : Config) (hw : WordsBounded W c) {B₂ H MX K₂ : ℕ}
    (h19 : c.nreg 212019 = B₂) (h05 : c.nreg 210005 = H) (h18 : c.nreg 212018 = MX)
    (h20 : c.nreg 216020 = K₂) (hB : B₂ + 6 * P.n ≤ W) (hH : H + 1 ≤ W) (hM : 4 * MX ≤ W) :
    ∃ c' k, Exec P W tArgs c c' k ∧ k = 12 ∧ c'.nreg 210020 = B₂ ∧ c'.nreg 210021 = K₂ ∧
      c'.nreg 210022 = B₂ + 6 * P.n ∧ c'.nreg 210023 = c.nmem (H + 1) ∧
      c'.nreg 210024 = 4 * MX ∧ FrameB Bargs c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tArgs c c' k ∧ k = 12 ∧
      (c'.nreg 210020 = B₂ ∧ c'.nreg 210021 = K₂ ∧ c'.nreg 210022 = B₂ + 6 * P.n ∧
        c'.nreg 210023 = c.nmem (H + 1) ∧ c'.nreg 210024 = 4 * MX) := by
    unfold tArgs
    exec_block
    all_goals try (config_simp; (try simp only [h19, h05, h18, h20]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h19, h05, h18, h20]) <;>
      (try omega)
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, exec_frameB ex (by decide)⟩

/-- `tDrop`. -/
theorem tDrop_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W tDrop c c' k ∧ k = 4 ∧ c'.nreg 200000 = c.nreg 210001 ∧
      c'.nreg 200001 = c.nreg 210002 ∧ c'.nreg 200002 = c.nreg 210003 ∧
      c'.nreg 200003 = c.nreg 210004 ∧
      FrameB (fun r => decide (200000 ≤ r ∧ r ≤ 200003)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tDrop c c' k ∧ k = 4 ∧
      (c'.nreg 200000 = c.nreg 210001 ∧ c'.nreg 200001 = c.nreg 210002 ∧
        c'.nreg 200002 = c.nreg 210003 ∧ c'.nreg 200003 = c.nreg 210004) := by
    unfold tDrop
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2, exec_frameB ex (by decide)⟩

/-- `tBld`. -/
theorem tBld_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W tBld c c' k ∧ k = 4 ∧ c'.nreg 40000 = c.nreg 210001 ∧
      c'.nreg 40001 = c.nreg 200004 ∧ c'.nreg 40002 = c.nreg 200005 ∧
      c'.nreg 40004 = c.nreg 200006 ∧
      FrameB (fun r => decide (40000 ≤ r ∧ r ≤ 40004)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tBld c c' k ∧ k = 4 ∧
      (c'.nreg 40000 = c.nreg 210001 ∧ c'.nreg 40001 = c.nreg 200004 ∧
        c'.nreg 40002 = c.nreg 200005 ∧ c'.nreg 40004 = c.nreg 200006) := by
    unfold tBld
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2, exec_frameB ex (by decide)⟩

/-- `tOut`. -/
theorem tOut_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W tOut c c' k ∧ k = 1 ∧ c'.nreg 210006 = c.nreg 40003 ∧
      FrameB (fun r => decide (r = 210006)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tOut c c' k ∧ k = 1 ∧
      c'.nreg 210006 = c.nreg 40003 := by
    unfold tOut
    exec_block
    refine ⟨rfl, ?_⟩; config_simp
  exact ⟨c', k, ex, hk, q, exec_frameB ex (by decide)⟩

end exec

end

end DrvB.BTop

end Chazelle.Core
