module

public import Chazelle.Core.ClusterSearch
public import Chazelle.Core.ClusterPhase
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics
public import Chazelle.ConfigTactics

/-!
# WP-I, part 17: lower-bound search on the RAM

`lbStmt`: in a segment `[lo, hi)` of the item array `ACT` whose keys
`κ i = FPRE[FIRST[ACT[i]]]` are sorted, find the partition point of `κ i < key` by binary
lifting over the table `POW` of powers of two (`POW[j] = 2^j` for `j < LP`, `hi - lo < 2^LP`).
`lbStmt_exec`: at most `17 LP + 4` steps; the result `pos` has all keys before it below `key`
and none from it on (`LbInv.final`).

Registers: `130009` the constant `0`; `130300` `lo`, `130301` `hi`, `130310` `key`; output
`130311` `pos`; scratch `130312 … 130316`; bases `130320` (`ACT`), `130321` (`FIRST`),
`130322` (`FPRE`), `130323` (`POW`), `130324` `LP`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- The probe at `pos + 2^j - 1`. -/
def lbProbe : Stmt := .seq (block [.addN 130314 130320 130316, .subN 130314 130314 130001,
    .loadN 130315 130314, .addN 130314 130321 130315, .loadN 130315 130314,
    .addN 130314 130322 130315, .loadN 130315 130314])
  (.ifLtN 130315 130310 (.instr (.copyN 130311 130316)) .skip)

/-- One level of the search: `j := j - 1`, `p := 2^j`, probe if `pos + p ≤ hi`. -/
def lbBody : Stmt := .seq (block [.subN 130312 130312 130001, .addN 130314 130323 130312,
    .loadN 130313 130314, .addN 130316 130311 130313])
  (.ifLtN 130301 130316 .skip lbProbe)

/-- **The lower-bound search.** -/
def lbStmt : Stmt := .seq (block [.copyN 130312 130324, .copyN 130311 130300])
  (.whileLtN 130009 130312 lbBody)

/-- The registers written by the search. -/
def LbRG (r : ℕ) : Prop := 130311 ≤ r ∧ r ≤ 130316

/-- The key of position `i`. -/
def keyOf (m : ℕ → ℕ) (bACT bFIRST bFPRE i : ℕ) : ℕ := m (bFPRE + m (bFIRST + m (bACT + i)))

section proofs

variable {P : Polygon} {W : ℕ}

/-- The registers read by the search. -/
structure LbRegs (c : Config) (lo hi key bACT bFIRST bFPRE bPOW LP : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rkey : c.nreg 130310 = key
  rACT : c.nreg 130320 = bACT
  rFIRST : c.nreg 130321 = bFIRST
  rFPRE : c.nreg 130322 = bFPRE
  rPOW : c.nreg 130323 = bPOW
  rLP : c.nreg 130324 = LP

theorem LbRegs.of_frame {c c' : Config} {lo hi key bACT bFIRST bFPRE bPOW LP : ℕ}
    (h : LbRegs c lo hi key bACT bFIRST bFPRE bPOW LP)
    (hr : ∀ r, ¬ LbRG r → c'.nreg r = c.nreg r) : LbRegs c' lo hi key bACT bFIRST bFPRE bPOW LP := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [hr _ (by ufo LbRG)]; assumption)

/-- **One level of the search.** -/
theorem lbBody_exec {c : Config} (hw : WordsBounded W c) {lo hi key bACT bFIRST bFPRE bPOW LP : ℕ}
    (hR : LbRegs c lo hi key bACT bFIRST bFPRE bPOW LP)
    (hs : Sorted (keyOf c.nmem bACT bFIRST bFPRE) lo hi) {pos j : ℕ}
    (hpos : c.nreg 130311 = pos) (hj : c.nreg 130312 = j + 1) (hjL : j < LP)
    (hpow : c.nmem (bPOW + j) = 2 ^ j) (hI : LbInv (keyOf c.nmem bACT bFIRST bFPRE) lo hi key pos (j + 1))
    (hwpow : bPOW + LP ≤ W) (hwact : bACT + hi ≤ W) (hw2 : hi + 2 ^ j ≤ W)
    (hwf : ∀ i, lo ≤ i → i < hi → bFIRST + c.nmem (bACT + i) ≤ W ∧
      bFPRE + c.nmem (bFIRST + c.nmem (bACT + i)) ≤ W) :
    ∃ c' k, Exec P W lbBody c c' k ∧ k ≤ 15 ∧ c'.nmem = c.nmem ∧
      (∀ r, ¬ LbRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130312 = j ∧
      ∃ pos', c'.nreg 130311 = pos' ∧ LbInv (keyOf c.nmem bACT bFIRST bFPRE) lo hi key pos' j := by
  have hle := hI.le_hi
  have hlo := hI.lo_le
  obtain ⟨hstep1, hstep2⟩ := LbInv.step hs hI
  have hp1 := Nat.one_le_two_pow (n := j)
  -- load the power and form `pos + 2^j`
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hj1, hpos1, ht1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W (block [.subN 130312 130312 130001, .addN 130314 130323 130312,
        .loadN 130313 130314, .addN 130316 130311 130313]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧
      c1.nmem = c.nmem ∧ c1.nreg 130312 = j ∧ c1.nreg 130311 = pos ∧
      c1.nreg 130316 = pos + 2 ^ j ∧ (∀ r, ¬ LbRG r → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    · config_simp; rwo [hR.rPOW, hj, hR.one]
    · config_simp; rwo [hpos, hj, hR.one, hR.rPOW, show j + 1 - 1 = j by omega, hpow]
    · refine ⟨rfl, ‹_›, rfl, by config_simp; rwo [hj, hR.one], by config_simp; exact hpos, ?_,
        fun r hr => ?_, rfl, rfl, rfl⟩
      · config_simp; rw [hpos, hj, hR.one, hR.rPOW, show j + 1 - 1 = j by omega, hpow]
      · simp only [Machine.upd_apply]; unfold LbRG at hr; splao
  have hR1 := hR.of_frame hr1
  by_cases hbig : hi < pos + 2 ^ j
  · -- out of range: skip
    subst hk1
    refine ⟨c1, 4 + (0 + 1), .seq e1 (.ifLtN_true (by rwx [hR1.rhi, ht1])
      (.skip hw1)), by omega, hm1, hr1, hrr1, hrm1, ho1, hj1, pos, hpos1, ?_⟩
    exact hstep2 (fun h => by omega)
  · -- probe the key at `pos + 2^j - 1`
    have hin : lo ≤ pos + 2 ^ j - 1 ∧ pos + 2 ^ j - 1 < hi := ⟨by omega, by omega⟩
    obtain ⟨hwa, hwb⟩ := hwf _ hin.1 hin.2
    rw [← hm1] at hwa hwb
    obtain ⟨c2, k2, e2, hk2', hw2', hm2, hk2, hr2, hrr2, hrm2, ho2⟩ : ∃ c2 k2,
        Exec P W (block [.addN 130314 130320 130316, .subN 130314 130314 130001,
          .loadN 130315 130314, .addN 130314 130321 130315, .loadN 130315 130314,
          .addN 130314 130322 130315, .loadN 130315 130314]) c1 c2 k2 ∧ k2 = 7 ∧
        WordsBounded W c2 ∧
        c2.nmem = c1.nmem ∧
        c2.nreg 130315 = keyOf c1.nmem bACT bFIRST bFPRE (pos + 2 ^ j - 1) ∧
        (∀ r, r ≠ 130314 → r ≠ 130315 → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧
        c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      exec_block
      · rwo [hR1.rACT, ht1]
      · config_simp; rw [hR1.rFIRST, hR1.rACT, ht1, hR1.one,
          show bACT + (pos + 2 ^ j) - 1 = bACT + (pos + 2 ^ j - 1) by omega]; exact hwa
      · config_simp; rw [hR1.rFPRE, hR1.rFIRST, hR1.rACT, ht1, hR1.one,
          show bACT + (pos + 2 ^ j) - 1 = bACT + (pos + 2 ^ j - 1) by omega]; exact hwb
      · refine ⟨rfl, ‹_›, rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
        · config_simp; rw [hR1.rFPRE, hR1.rFIRST, hR1.rACT, ht1, hR1.one,
            show bACT + (pos + 2 ^ j) - 1 = bACT + (pos + 2 ^ j - 1) by omega]; rfl
        · simp only [Machine.upd_apply, h1, h2, ite_false]
    subst hk1 hk2'
    have hkey2 : c2.nreg 130310 = key := by rw [hr2 _ (by decide) (by decide)]; exact hR1.rkey
    have hkk : c2.nreg 130315 = keyOf c.nmem bACT bFIRST bFPRE (pos + 2 ^ j - 1) := by
      rw [hk2, hm1]
    have hframe : ∀ c3 : Config, (∀ r, ¬ LbRG r → c3.nreg r = c2.nreg r) →
        ∀ r, ¬ LbRG r → c3.nreg r = c.nreg r := by
      intro c3 h3 r hr
      rw [h3 r hr, hr2 r (fun e => hr (by ruo [e] LbRG))
        (fun e => hr (by ruo [e] LbRG)), hr1 r hr]
    by_cases hlt : keyOf c.nmem bACT bFIRST bFPRE (pos + 2 ^ j - 1) < key
    · have e3 := Exec.copyN (P := P) hw2' 130311 130316
      refine ⟨_, 4 + ((7 + (1 + 1)) + 2), .seq e1 (.ifLtN_false (by rwx [hR1.rhi, ht1])
        (.seq e2 (.ifLtN_true (by rwx [hkk, hkey2]) e3))), by omega, ?_, ?_, ?_, ?_,
        ?_, ?_, pos + 2 ^ j, ?_, hstep1 ⟨by omega, hlt⟩⟩
      · simp [hm2, hm1]
      · refine hframe _ (fun r hr => ?_)
        simp only [Machine.upd_apply]; unfold LbRG at hr; splao
      · simp [hrr2, hrr1]
      · simp [hrm2, hrm1]
      · simp [ho2, ho1]
      · simp only [Machine.upd_apply]
        rw [ite_eq_right (by decide), hr2 _ (by decide) (by decide), hj1]
      · simp only [Machine.upd_same]
        rw [hr2 _ (by decide) (by decide), ht1]
    · refine ⟨c2, 4 + ((7 + (0 + 2)) + 2), .seq e1 (.ifLtN_false (by rwx [hR1.rhi, ht1])
        (.seq e2 (.ifLtN_false (by rwx [hkk, hkey2]) (.skip hw2')))), by omega,
        hm2.trans hm1, hframe _ (fun _ _ => rfl), hrr2.trans hrr1, hrm2.trans hrm1,
        ho2.trans ho1, by rw [hr2 _ (by decide) (by decide), hj1], pos,
        by rw [hr2 _ (by decide) (by decide), hpos1], hstep2 (fun h => hlt h.2)⟩

/-- **The lower-bound search.**  At the end `pos` (register `130311`) is the partition point of
the sorted keys of `[lo, hi)` for `key`; only the scratch registers change. -/
theorem lbStmt_exec {c : Config} (hw : WordsBounded W c) {lo hi key bACT bFIRST bFPRE bPOW LP : ℕ}
    (hR : LbRegs c lo hi key bACT bFIRST bFPRE bPOW LP)
    (hs : Sorted (keyOf c.nmem bACT bFIRST bFPRE) lo hi) (hlh : lo ≤ hi)
    (hpow : ∀ j, j < LP → c.nmem (bPOW + j) = 2 ^ j) (hLP : hi - lo < 2 ^ LP)
    (hwpow : bPOW + LP ≤ W) (hwact : bACT + hi ≤ W) (hw2 : hi + 2 ^ LP ≤ W)
    (hwf : ∀ i, lo ≤ i → i < hi → bFIRST + c.nmem (bACT + i) ≤ W ∧
      bFPRE + c.nmem (bFIRST + c.nmem (bACT + i)) ≤ W) :
    ∃ c' k, Exec P W lbStmt c c' k ∧ k ≤ 17 * LP + 4 ∧ c'.nmem = c.nmem ∧
      (∀ r, ¬ LbRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ lo ≤ c'.nreg 130311 ∧ c'.nreg 130311 ≤ hi ∧
      (∀ i, lo ≤ i → i < c'.nreg 130311 → keyOf c.nmem bACT bFIRST bFPRE i < key) ∧
      (∀ i, c'.nreg 130311 ≤ i → i < hi → key ≤ keyOf c.nmem bACT bFIRST bFPRE i) := by
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hj1, hpos1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W (block [.copyN 130312 130324, .copyN 130311 130300]) c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130312 = LP ∧ c1.nreg 130311 = lo ∧
      (∀ r, ¬ LbRG r → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧
      c1.output = c.output := by
    exec_block
    refine ⟨rfl, ‹_›, rfl, by config_simp; exact hR.rLP, by config_simp; exact hR.rlo,
      fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [Machine.upd_apply]; unfold LbRG at hr; splao
  obtain ⟨c', k, e, ⟨hw', hm', hr', hrr', hrm', ho', j, pos, hj, hpos, hjL, hI⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 130009) (b := 130312) (body := lbBody)
    (fun c' => WordsBounded W c' ∧ c'.nmem = c.nmem ∧ (∀ r, ¬ LbRG r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      ∃ j pos, c'.nreg 130312 = j ∧ c'.nreg 130311 = pos ∧ j ≤ LP ∧
        LbInv (keyOf c.nmem bACT bFIRST bFPRE) lo hi key pos j)
    (fun c' => 17 * c'.nreg 130312) (fun c' h => h.1)
    (fun c2 ⟨hw2', hm2, hr2, hrr2, hrm2, ho2, j, pos, hj, hpos, hjL, hI⟩ htest => by
      have hR2 := hR.of_frame hr2
      rw [hR2.zero, hj] at htest
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hs2 : Sorted (keyOf c2.nmem bACT bFIRST bFPRE) lo hi := by rwx [hm2]
      have hI2 : LbInv (keyOf c2.nmem bACT bFIRST bFPRE) lo hi key pos (j' + 1) := by
        rwx [hm2]
      have hpow2 : c2.nmem (bPOW + j') = 2 ^ j' := by rw [hm2]; exact hpow j' (by omega)
      have hp : 2 ^ j' ≤ 2 ^ LP := Nat.pow_le_pow_right (by norm_num) (by omega)
      obtain ⟨c3, k3, e3, hk3, hm3, hr3, hrr3, hrm3, ho3, hj3, pos', hpos3, hI3⟩ :=
        lbBody_exec (P := P) hw2' hR2 hs2 hpos hj (by omega) hpow2 hI2 hwpow hwact (by omega)
          (fun i a b => by rw [hm2]; exact hwf i a b)
      refine ⟨c3, k3, e3, ⟨e3.wb_right, hm3.trans hm2, fun r hr => (hr3 r hr).trans (hr2 r hr),
        hrr3.trans hrr2, hrm3.trans hrm2, ho3.trans ho2, j', pos', hj3, hpos3, by omega,
        by rw [hm2] at hI3; exact hI3⟩, ?_⟩
      rwo [hj3, hj])
    ⟨hw1, hm1, hr1, hrr1, hrm1, ho1, LP, lo, hj1, hpos1, le_rfl, LbInv.init hlh hLP⟩
  have hR' := hR.of_frame hr'
  rw [hR'.zero, hj] at htest
  have hj0 : j = 0 := by omega
  subst hj0
  obtain ⟨fin1, fin2⟩ := LbInv.final hs hI
  refine ⟨c', k1 + k, .seq e1 e, by rwo [hj1] at hk, hm', hr', hrr', hrm', ho',
    by rw [hpos]; exact hI.lo_le, by rw [hpos]; exact hI.le_hi, by rw [hpos]; exact fin1,
    by rw [hpos]; exact fin2⟩


/-! ## The good test -/

/-- `key := FPRE[z]`. -/
def goodPre1 : Stmt := block [.addN 130333 130322 130330, .loadN 130310 130333]

/-- Save the first count, `key := FPRE[z] + FSZ[z]`. -/
def goodPre2 : Stmt := block [.copyN 130332 130311, .addN 130333 130325 130330,
  .loadN 130334 130333, .addN 130310 130310 130334]

/-- `2 cnt` and the comparison with `W`. -/
def goodFin : Stmt := .seq (block [.subN 130334 130311 130332, .addN 130334 130334 130334])
  (.ifLtN 130302 130334 (.instr (.constN 130331 1)) (.instr (.constN 130331 0)))

/-- **The good test** of the face in `130330`: `130331 := 1` iff more than half of the segment
has its key in the preorder interval of the face. -/
def goodStmt : Stmt := .seq goodPre1 (.seq lbStmt (.seq goodPre2 (.seq lbStmt goodFin)))

/-- The registers written by the good test. -/
def GoodRG (r : ℕ) : Prop := 130310 ≤ r ∧ r ≤ 130316 ∨ 130331 ≤ r ∧ r ≤ 130334

/-- The keys of `[lo, hi)` in the half-open interval `[a, b)`. -/
def cntIn (κ : ℕ → ℕ) (lo hi a b : ℕ) : ℕ :=
  ((Finset.Ico lo hi).filter (fun i => a ≤ κ i ∧ κ i < b)).card

/-- Counting a key interval with two partition points. -/
theorem cntIn_eq {κ : ℕ → ℕ} {lo hi a b p1 p2 : ℕ} (_hab : a ≤ b)
    (h1 : lo ≤ p1 ∧ p1 ≤ hi) (h2 : lo ≤ p2 ∧ p2 ≤ hi)
    (b1 : ∀ i, lo ≤ i → i < p1 → κ i < a) (a1 : ∀ i, p1 ≤ i → i < hi → a ≤ κ i)
    (b2 : ∀ i, lo ≤ i → i < p2 → κ i < b) (a2 : ∀ i, p2 ≤ i → i < hi → b ≤ κ i) :
    cntIn κ lo hi a b = p2 - p1 := by
  unfold cntIn
  have : (Finset.Ico lo hi).filter (fun i => a ≤ κ i ∧ κ i < b) = Finset.Ico p1 p2 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨c, d⟩, e, f⟩
      constructor
      · by_contra hc; have := b1 i c (by omega); omega
      · by_contra hc; have := a2 i (by omega) d; omega
    · rintro ⟨c, d⟩
      refine ⟨⟨by omega, by omega⟩, a1 i c (by omega), b2 i (by omega) d⟩
  rw [this, Nat.card_Ico]

/-- The registers read by the good test. -/
structure GoodRegs (c : Config) (lo hi z bACT bFIRST bFPRE bPOW LP bFSZ : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rACT : c.nreg 130320 = bACT
  rFIRST : c.nreg 130321 = bFIRST
  rFPRE : c.nreg 130322 = bFPRE
  rPOW : c.nreg 130323 = bPOW
  rLP : c.nreg 130324 = LP
  rW : c.nreg 130302 = hi - lo
  rz : c.nreg 130330 = z
  rFSZ : c.nreg 130325 = bFSZ

theorem GoodRegs.lb {c : Config} {lo hi z bACT bFIRST bFPRE bPOW LP bFSZ : ℕ}
    (h : GoodRegs c lo hi z bACT bFIRST bFPRE bPOW LP bFSZ) :
    LbRegs c lo hi (c.nreg 130310) bACT bFIRST bFPRE bPOW LP :=
  ⟨h.one, h.zero, h.rlo, h.rhi, rfl, h.rACT, h.rFIRST, h.rFPRE, h.rPOW, h.rLP⟩

theorem GoodRegs.of_frame {c c' : Config} {lo hi z bACT bFIRST bFPRE bPOW LP bFSZ : ℕ}
    (h : GoodRegs c lo hi z bACT bFIRST bFPRE bPOW LP bFSZ)
    (hr : ∀ r, ¬ GoodRG r → c'.nreg r = c.nreg r) :
    GoodRegs c' lo hi z bACT bFIRST bFPRE bPOW LP bFSZ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ (by ufo GoodRG)]; assumption)

/-- **The good test.** -/
theorem goodStmt_exec {c : Config} (hw : WordsBounded W c)
    {lo hi z bACT bFIRST bFPRE bPOW LP bFSZ : ℕ}
    (hR : GoodRegs c lo hi z bACT bFIRST bFPRE bPOW LP bFSZ)
    (hs : Sorted (keyOf c.nmem bACT bFIRST bFPRE) lo hi) (hlh : lo ≤ hi)
    (hpow : ∀ j, j < LP → c.nmem (bPOW + j) = 2 ^ j) (hLP : hi - lo < 2 ^ LP)
    (hwpow : bPOW + LP ≤ W) (hwact : bACT + hi ≤ W) (hw2 : hi + 2 ^ LP ≤ W)
    (hwf : ∀ i, lo ≤ i → i < hi → bFIRST + c.nmem (bACT + i) ≤ W ∧
      bFPRE + c.nmem (bFIRST + c.nmem (bACT + i)) ≤ W)
    (hwz : bFPRE + z ≤ W ∧ bFSZ + z ≤ W ∧ c.nmem (bFPRE + z) + c.nmem (bFSZ + z) ≤ W)
    (hwh : 2 * hi ≤ W) :
    ∃ c' k, Exec P W goodStmt c c' k ∧ k ≤ 34 * LP + 25 ∧ c'.nmem = c.nmem ∧
      (∀ r, ¬ GoodRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130331 ≤ 1 ∧
      (c'.nreg 130331 = 1 ↔ hi - lo < 2 * cntIn (keyOf c.nmem bACT bFIRST bFPRE) lo hi
        (c.nmem (bFPRE + z)) (c.nmem (bFPRE + z) + c.nmem (bFSZ + z))) := by
  obtain ⟨hwz1, hwz2, hwz3⟩ := hwz
  -- key := FPRE[z]
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hkey1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W goodPre1 c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130310 = c.nmem (bFPRE + z) ∧ (∀ r, r ≠ 130333 → r ≠ 130310 → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    unfold goodPre1
    exec_block
    · rwx [hR.rFPRE, hR.rz]
    · refine ⟨rfl, ‹_›, rfl, by config_simp; rw [hR.rFPRE, hR.rz], fun r h1 h2 => ?_, rfl, rfl,
        rfl⟩
      simp only [Machine.upd_apply, h1, h2, ite_false]
  have hR1 : GoodRegs c1 lo hi z bACT bFIRST bFPRE bPOW LP bFSZ :=
    hR.of_frame (fun r hr => hr1 r (fun e => hr (by ruo [e] GoodRG))
      (fun e => hr (by ruo [e] GoodRG)))
  have hL1 := hR1.lb
  rw [hkey1] at hL1
  obtain ⟨c2, k2, e2, hk2, hm2, hr2, hrr2, hrm2, ho2, hp1a, hp1b, hb1, ha1⟩ :=
    lbStmt_exec (P := P) hw1 hL1 (by rwx [hm1]) hlh (by rwx [hm1]) hLP hwpow
      hwact hw2 (by rwx [hm1])
  rw [hm1] at hb1 ha1
  have hR2 : GoodRegs c2 lo hi z bACT bFIRST bFPRE bPOW LP bFSZ :=
    hR1.of_frame (fun r hr => hr2 r (fun h => hr (Or.inl ⟨by ufo LbRG at h,
      by ufo LbRG at h⟩)))
  have hkey2 : c2.nreg 130310 = c.nmem (bFPRE + z) := by rw [hr2 _ (by ufo LbRG), hkey1]
  set p1 := c2.nreg 130311
  have hw2' := e2.wb_right
  -- save `p1`, key := FPRE[z] + FSZ[z]
  obtain ⟨c3, k3, e3, hk3, hw3, hm3, hs3, hkey3, hr3, hrr3, hrm3, ho3⟩ : ∃ c3 k3,
      Exec P W goodPre2 c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧ c3.nmem = c.nmem ∧
      c3.nreg 130332 = p1 ∧ c3.nreg 130310 = c.nmem (bFPRE + z) + c.nmem (bFSZ + z) ∧
      (∀ r, r ≠ 130332 → r ≠ 130333 → r ≠ 130334 → r ≠ 130310 → c3.nreg r = c2.nreg r) ∧
      c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    unfold goodPre2
    exec_block
    · config_simp; rwx [hR2.rFSZ, hR2.rz]
    · config_simp; rwx [hkey2, hR2.rFSZ, hR2.rz, hm2, hm1]
    · refine ⟨rfl, ‹_›, by rw [hm2, hm1], by csr, ?_, fun r h1 h2 h3 h4 => ?_, rfl,
        rfl, rfl⟩
      · config_simp; rw [hkey2, hR2.rFSZ, hR2.rz, hm2, hm1]
      · simp only [Machine.upd_apply, h1, h2, h3, h4, ite_false]
  have hR3 : GoodRegs c3 lo hi z bACT bFIRST bFPRE bPOW LP bFSZ :=
    hR2.of_frame (fun r hr => hr3 r (fun e => hr (by ruo [e] GoodRG))
      (fun e => hr (by ruo [e] GoodRG)) (fun e => hr (by ruo [e] GoodRG))
      (fun e => hr (by ruo [e] GoodRG)))
  have hL3 := hR3.lb
  rw [hkey3] at hL3
  obtain ⟨c4, k4, e4, hk4, hm4, hr4, hrr4, hrm4, ho4, hp2a, hp2b, hb2, ha2⟩ :=
    lbStmt_exec (P := P) hw3 hL3 (by rwx [hm3]) hlh (by rwx [hm3]) hLP hwpow
      hwact hw2 (by rwx [hm3])
  rw [hm3] at hb2 ha2
  have hs4 : c4.nreg 130332 = p1 := by rw [hr4 _ (by ufo LbRG), hs3]
  have hR4 : GoodRegs c4 lo hi z bACT bFIRST bFPRE bPOW LP bFSZ :=
    hR3.of_frame (fun r hr => hr4 r (fun h => hr (Or.inl ⟨by ufo LbRG at h,
      by ufo LbRG at h⟩)))
  set p2 := c4.nreg 130311
  have hw4 := e4.wb_right
  have hcnt : cntIn (keyOf c.nmem bACT bFIRST bFPRE) lo hi (c.nmem (bFPRE + z))
      (c.nmem (bFPRE + z) + c.nmem (bFSZ + z)) = p2 - p1 :=
    cntIn_eq (by omega) ⟨hp1a, hp1b⟩ ⟨hp2a, hp2b⟩ hb1 ha1 hb2 ha2
  -- the comparison
  obtain ⟨c5, k5, e5, hk5, hw5, hm5, hd5, hr5, hrr5, hrm5, ho5⟩ : ∃ c5 k5,
      Exec P W (block [.subN 130334 130311 130332, .addN 130334 130334 130334]) c4 c5 k5 ∧
      k5 = 2 ∧ WordsBounded W c5 ∧ c5.nmem = c4.nmem ∧ c5.nreg 130334 = 2 * (p2 - p1) ∧
      (∀ r, r ≠ 130334 → c5.nreg r = c4.nreg r) ∧ c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧
      c5.output = c4.output := by
    exec_block
    · config_simp; rwo [hs4]
    · refine ⟨rfl, ‹_›, rfl, by config_simp; rwo [hs4], fun r h1 => ?_, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply, h1, ite_false]
  have hW5 : c5.nreg 130302 = hi - lo := by
    rw [hr5 _ (by decide)]; exact hR4.rW
  have hframe : ∀ c6 : Config, (∀ r, r ≠ 130331 → c6.nreg r = c5.nreg r) →
      ∀ r, ¬ GoodRG r → c6.nreg r = c.nreg r := by
    intro c6 h6 r hr
    have n1 : ¬ LbRG r := fun h => hr (Or.inl ⟨by ufo LbRG at h, by ufo LbRG at h⟩)
    rw [h6 r (fun e => hr (by ruo [e] GoodRG)),
      hr5 r (fun e => hr (by ruo [e] GoodRG)), hr4 r n1,
      hr3 r (fun e => hr (by ruo [e] GoodRG)) (fun e => hr (by ruo [e] GoodRG))
        (fun e => hr (by ruo [e] GoodRG)) (fun e => hr (by ruo [e] GoodRG)),
      hr2 r n1, hr1 r (fun e => hr (by ruo [e] GoodRG))
        (fun e => hr (by ruo [e] GoodRG))]
  subst hk1 hk3 hk5
  by_cases hgood : c5.nreg 130302 < c5.nreg 130334
  · have e6 := Exec.constN (P := P) hw5 130331 1 (by omega)
    refine ⟨_, 2 + (k2 + (4 + (k4 + (2 + (1 + 1))))), .seq e1 (.seq e2 (.seq e3 (.seq e4
      (.seq e5 (.ifLtN_true hgood e6))))), by omega, ?_, hframe _ (fun r hr => by simp [hr]),
      by simp [hrr5, hrr4, hrr3, hrr2, hrr1], by simp [hrm5, hrm4, hrm3, hrm2, hrm1],
      by simp [ho5, ho4, ho3, ho2, ho1], by simp, ?_⟩
    · simp [hm5, hm4, hm3]
    · simp only [Machine.upd_same, true_iff]
      rw [hW5, hd5] at hgood; rwx [hcnt]
  · have e6 := Exec.constN (P := P) hw5 130331 0 (by omega)
    refine ⟨_, 2 + (k2 + (4 + (k4 + (2 + (1 + 2))))), .seq e1 (.seq e2 (.seq e3 (.seq e4
      (.seq e5 (.ifLtN_false hgood e6))))), by omega, ?_, hframe _ (fun r hr => by simp [hr]),
      by simp [hrr5, hrr4, hrr3, hrr2, hrr1], by simp [hrm5, hrm4, hrm3, hrm2, hrm1],
      by simp [ho5, ho4, ho3, ho2, ho1], by simp, ?_⟩
    · simp [hm5, hm4, hm3]
    · simp only [Machine.upd_same, zero_ne_one, false_iff]
      rw [hW5, hd5] at hgood; rwx [hcnt]

/-! ## The climb -/

/-- One level of the climb: `j := j - 1`, `base := base - N`, `z := UP_j[x]`, move if bad. -/
def climbBody : Stmt := .seq (block [.subN 130342 130342 130001, .subN 130343 130343 130328,
    .addN 130333 130343 130341, .loadN 130330 130333])
  (.seq goodStmt (.ifLtN 130331 130001 (.instr (.copyN 130341 130330)) .skip))

/-- The climb loop and the final parent step `f := UP_0[x]`. -/
def climbLoop : Stmt := .seq (block [.copyN 130341 130340, .copyN 130342 130345,
    .copyN 130343 130327])
  (.seq (.whileLtN 130009 130342 climbBody) (block [.addN 130333 130326 130341,
    .loadN 130344 130333]))

/-- **The climb** from `y` (register `130340`) to the centroid `f` (register `130344`). -/
def climbStmt : Stmt := .seq (.instr (.copyN 130330 130340))
  (.seq goodStmt (.ifLtN 130331 130001 climbLoop (.instr (.copyN 130344 130340))))

/-- The registers written by the climb. -/
def ClimbRG (r : ℕ) : Prop := GoodRG r ∨ r = 130330 ∨ (130341 ≤ r ∧ r ≤ 130344)

/-- The good predicate of the segment `[lo, hi)`. -/
def GdF (m : ℕ → ℕ) (bACT bFIRST bFPRE bFSZ lo hi z : ℕ) : Prop :=
  hi - lo < 2 * cntIn (keyOf m bACT bFIRST bFPRE) lo hi (m (bFPRE + z)) (m (bFPRE + z) + m (bFSZ + z))

/-- The static hypotheses of the good test and the climb (everything but the tested face). -/
structure ClimbCtx (c : Config) (lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rACT : c.nreg 130320 = bACT
  rFIRST : c.nreg 130321 = bFIRST
  rFPRE : c.nreg 130322 = bFPRE
  rPOW : c.nreg 130323 = bPOW
  rLP : c.nreg 130324 = LP
  rW : c.nreg 130302 = hi - lo
  rFSZ : c.nreg 130325 = bFSZ
  rUP : c.nreg 130326 = bUP
  rUPE : c.nreg 130327 = bUP + L * N
  rN : c.nreg 130328 = N
  rL : c.nreg 130345 = L

theorem ClimbCtx.of_frame {c c' : Config} {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ}
    (h : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N)
    (hr : ∀ r, ¬ ClimbRG r → c'.nreg r = c.nreg r) :
    ClimbCtx c' lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ (by ufo ClimbRG GoodRG)]; assumption)

theorem ClimbCtx.good {c : Config} {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N z : ℕ}
    (h : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N) (hz : c.nreg 130330 = z) :
    GoodRegs c lo hi z bACT bFIRST bFPRE bPOW LP bFSZ :=
  ⟨h.one, h.zero, h.rlo, h.rhi, h.rACT, h.rFIRST, h.rFPRE, h.rPOW, h.rLP, h.rW, hz, h.rFSZ⟩

/-- The static memory hypotheses of the climb. -/
structure ClimbMem (m : ℕ → ℕ) (W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ)
    (up : ℕ → ℕ) : Prop where
  sorted : Sorted (keyOf m bACT bFIRST bFPRE) lo hi
  lh : lo ≤ hi
  pow : ∀ j, j < LP → m (bPOW + j) = 2 ^ j
  hLP : hi - lo < 2 ^ LP
  wpow : bPOW + LP ≤ W
  wact : bACT + hi ≤ W
  w2 : hi + 2 ^ LP ≤ W
  wf : ∀ i, lo ≤ i → i < hi → bFIRST + m (bACT + i) ≤ W ∧
    bFPRE + m (bFIRST + m (bACT + i)) ≤ W
  wz : ∀ z, z < N → bFPRE + z ≤ W ∧ bFSZ + z ≤ W ∧ m (bFPRE + z) + m (bFSZ + z) ≤ W
  wh : 2 * hi ≤ W
  up_lt : ∀ g, g < N → up g < N
  tab : ∀ j, j < L → ∀ g, g < N → m (bUP + j * N + g) = up^[2 ^ j] g
  wup : bUP + L * N ≤ W

/-- The good test in the climb context. -/
theorem good_in_ctx {c : Config} (hw : WordsBounded W c)
    {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ} {up : ℕ → ℕ}
    (hC : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N)
    (hM : ClimbMem c.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up) {z : ℕ}
    (hz : c.nreg 130330 = z) (hzN : z < N) :
    ∃ c' k, Exec P W goodStmt c c' k ∧ k ≤ 34 * LP + 25 ∧ c'.nmem = c.nmem ∧
      (∀ r, ¬ GoodRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130331 ≤ 1 ∧
      (c'.nreg 130331 = 1 ↔ GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi z) :=
  goodStmt_exec hw (hC.good hz) hM.sorted hM.lh hM.pow hM.hLP hM.wpow hM.wact hM.w2 hM.wf
    (hM.wz z hzN) hM.wh

/-- **One level of the climb.** -/
theorem climbBody_exec {c : Config} (hw : WordsBounded W c)
    {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ} {up : ℕ → ℕ}
    (hC : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N)
    (hM : ClimbMem c.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up) {x j y : ℕ}
    (hx : c.nreg 130341 = x) (hj : c.nreg 130342 = j + 1) (hjL : j < L)
    (hb : c.nreg 130343 = bUP + (j + 1) * N) (hxN : x < N)
    (hI : ClimbInv up (GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi) x (j + 1))
    (hanc : ∃ n, up^[n] y = x) :
    ∃ c' k, Exec P W climbBody c c' k ∧ k ≤ 34 * LP + 32 ∧ c'.nmem = c.nmem ∧
      (∀ r, ¬ ClimbRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130342 = j ∧ c'.nreg 130343 = bUP + j * N ∧
      ∃ x', c'.nreg 130341 = x' ∧ x' < N ∧
        ClimbInv up (GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi) x' j ∧ ∃ n, up^[n] y = x' := by
  obtain ⟨hs1, hs2⟩ := hI.step
  have hzN : up^[2 ^ j] x < N := by
    have : ∀ n g, g < N → up^[n] g < N := by
      intro n; induction n with
      | zero => intro g hg; exact hg
      | succ n ih => intro g hg; rw [Function.iterate_succ_apply]; exact ih _ (hM.up_lt g hg)
    exact this _ x hxN
  have htab := hM.tab j hjL x hxN
  have hjN : bUP + j * N + x ≤ W := by
    have : j * N + x < L * N := by
      calc j * N + x < j * N + N := by omega
        _ = (j + 1) * N := by ring
        _ ≤ L * N := Nat.mul_le_mul_right _ hjL
    have := hM.wup; omega
  -- load `z := UP_j[x]`
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hj1, hb1, hz1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W (block [.subN 130342 130342 130001, .subN 130343 130343 130328,
        .addN 130333 130343 130341, .loadN 130330 130333]) c c1 k1 ∧ k1 = 4 ∧
      WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130342 = j ∧
      c1.nreg 130343 = bUP + j * N ∧ c1.nreg 130330 = up^[2 ^ j] x ∧
      (∀ r, r ≠ 130342 → r ≠ 130343 → r ≠ 130333 → r ≠ 130330 → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    have hbj : bUP + (j + 1) * N - N = bUP + j * N := by
      rwo [show (j + 1) * N = j * N + N by ring]
    exec_block
    · config_simp; rwx [hb, hC.rN, hx, hbj]
    · refine ⟨rfl, ‹_›, rfl, by config_simp; rwo [hj, hC.one],
        by config_simp; rw [hb, hC.rN, hbj], ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
      · config_simp; rw [hb, hC.rN, hx, hbj, htab]
      · simp only [Machine.upd_apply, h1, h2, h3, h4, ite_false]
  have hC1 : ClimbCtx c1 lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N :=
    hC.of_frame (fun r hr => hr1 r (fun e => hr (by ruo [e] ClimbRG))
      (fun e => hr (by ruo [e] ClimbRG))
      (fun e => hr (by ruo [e] ClimbRG GoodRG))
      (fun e => hr (by ruo [e] ClimbRG)))
  have hM1 : ClimbMem c1.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up := by
    rwx [hm1]
  obtain ⟨c2, k2, e2, hk2, hm2, hr2, hrr2, hrm2, ho2, hle2, hg2⟩ :=
    good_in_ctx (P := P) hw1 hC1 hM1 hz1 hzN
  rw [hm1] at hg2
  have hone2 : c2.nreg 130001 = 1 := by rw [hr2 _ (by ufo GoodRG)]; exact hC1.one
  have hx2 : c2.nreg 130341 = x := by
    rw [hr2 _ (by ufo GoodRG), hr1 _ (by decide) (by decide) (by decide) (by decide), hx]
  have hz2 : c2.nreg 130330 = up^[2 ^ j] x := by
    rw [hr2 _ (by ufo GoodRG), hz1]
  have hframe : ∀ c3 : Config, (∀ r, r ≠ 130341 → c3.nreg r = c2.nreg r) →
      ∀ r, ¬ ClimbRG r → c3.nreg r = c.nreg r := by
    intro c3 h3 r hr
    rw [h3 r (fun e => hr (by ruo [e] ClimbRG)),
      hr2 r (fun h => hr (Or.inl h)),
      hr1 r (fun e => hr (by ruo [e] ClimbRG))
        (fun e => hr (by ruo [e] ClimbRG))
        (fun e => hr (by ruo [e] ClimbRG GoodRG))
        (fun e => hr (by ruo [e] ClimbRG))]
  have hj2 : c2.nreg 130342 = j := by rw [hr2 _ (by ufo GoodRG), hj1]
  have hb2 : c2.nreg 130343 = bUP + j * N := by rw [hr2 _ (by ufo GoodRG), hb1]
  obtain ⟨n, hn⟩ := hanc
  subst hk1
  by_cases hbad : c2.nreg 130331 < c2.nreg 130001
  · -- not good: move
    have hng : ¬ GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi (up^[2 ^ j] x) := by
      intro h; have := hg2.mpr h; rwo [hone2] at hbad
    have e3 := Exec.copyN (P := P) e2.wb_right 130341 130330
    refine ⟨_, 4 + (k2 + (1 + 1)), .seq e1 (.seq e2 (.ifLtN_true hbad e3)), by omega,
      by simp [hm2, hm1], hframe _ (fun r hr => by simp [hr]), by simp [hrr2, hrr1],
      by simp [hrm2, hrm1], by simp [ho2, ho1], by simp [hj2], by simp [hb2],
      up^[2 ^ j] x, by simp [hz2], hzN, hs1 hng, 2 ^ j + n, ?_⟩
    rw [Function.iterate_add_apply, hn]
  · have hgd : GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi (up^[2 ^ j] x) := by
      rw [hone2] at hbad; exact hg2.mp (by omega)
    refine ⟨c2, 4 + (k2 + (0 + 2)), .seq e1 (.seq e2 (.ifLtN_false hbad (.skip e2.wb_right))),
      by omega, by rw [hm2, hm1], hframe _ (fun _ _ => rfl), by rw [hrr2, hrr1],
      by rw [hrm2, hrm1], by rw [ho2, ho1], hj2, hb2, x, hx2, hxN, hs2 hgd, n, hn⟩

/-- **The climb**: from `y < N` (register `130340`), the face `f` in register `130344` is `y` if
`y` is good, and otherwise the parent of an ancestor `x` of `y` that is not good while its parent
is.  Needs the `2^L`-th ancestor of `y` to be good. -/
theorem climbStmt_exec {c : Config} (hw : WordsBounded W c)
    {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ} {up : ℕ → ℕ}
    (hC : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N)
    (hM : ClimbMem c.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up) {y : ℕ}
    (hy : c.nreg 130340 = y) (hyN : y < N) (hL : 0 < L)
    (hroot : GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi (up^[2 ^ L] y)) :
    ∃ c' k, Exec P W climbStmt c c' k ∧ k ≤ (34 * LP + 34) * (L + 2) + 10 ∧ c'.nmem = c.nmem ∧
      (∀ r, ¬ ClimbRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130344 < N ∧
      ((GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi y ∧ c'.nreg 130344 = y) ∨
        ∃ x n, up^[n] y = x ∧ ¬ GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi x ∧
          GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi (up x) ∧ c'.nreg 130344 = up x) := by
  have e0 := Exec.copyN (P := P) hw 130330 130340
  set c0 := { c with nreg := upd c.nreg 130330 (c.nreg 130340) }
  have hC0 : ClimbCtx c0 lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N :=
    hC.of_frame (fun r hr => by
      simp only [c0, Machine.upd_apply]
      rw [ite_eq_right (fun e => hr (by ruo [e] ClimbRG))])
  have hz0 : c0.nreg 130330 = y := by simp [c0, hy]
  obtain ⟨c1, k1, e1, hk1, hm1, hr1, hrr1, hrm1, ho1, hle1, hg1⟩ :=
    good_in_ctx (P := P) e0.wb_right hC0 (by simpa [c0] using hM) hz0 hyN
  have hm1'  := hm1
  rw [show c0.nmem = c.nmem from rfl] at hg1
  have hC1 : ClimbCtx c1 lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N :=
    hC0.of_frame (fun r hr => hr1 r (fun h => hr (Or.inl h)))
  have hy1 : c1.nreg 130340 = y := by
    rw [hr1 _ (by ufo GoodRG)]; simp [c0, hy]
  have hframe1 : ∀ r, ¬ ClimbRG r → c1.nreg r = c.nreg r := by
    intro r hr
    rw [hr1 r (fun h => hr (Or.inl h))]
    simp only [c0, Machine.upd_apply]
    rw [ite_eq_right (fun e => hr (by ruo [e] ClimbRG))]
  have hone1 := hC1.one
  have hup_lt : ∀ n g, g < N → up^[n] g < N := by
    intro n; induction n with
    | zero => intro g hg; exact hg
    | succ n ih => intro g hg; rw [Function.iterate_succ_apply]; exact ih _ (hM.up_lt g hg)
  by_cases hbad : c1.nreg 130331 < c1.nreg 130001
  · -- `y` is not good: the loop
    have hng : ¬ GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi y := by
      intro h; have := hg1.mpr h; rwo [hone1] at hbad
    obtain ⟨c2, k2, e2, hk2, hw2, hm2, hx2, hj2, hb2, hr2, hrr2, hrm2, ho2⟩ : ∃ c2 k2,
        Exec P W (block [.copyN 130341 130340, .copyN 130342 130345, .copyN 130343 130327])
          c1 c2 k2 ∧ k2 = 3 ∧ WordsBounded W c2 ∧ c2.nmem = c1.nmem ∧ c2.nreg 130341 = y ∧
        c2.nreg 130342 = L ∧ c2.nreg 130343 = bUP + L * N ∧
        (∀ r, r ≠ 130341 → r ≠ 130342 → r ≠ 130343 → c2.nreg r = c1.nreg r) ∧
        c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      have := e1.wb_right
      exec_block
      refine ⟨rfl, ‹_›, rfl, by config_simp; exact hy1, by config_simp; exact hC1.rL,
        by config_simp; exact hC1.rUPE, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply, h1, h2, h3, ite_false]
    have hC2 : ClimbCtx c2 lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N :=
      hC1.of_frame (fun r hr => hr2 r (fun e => hr (by ruo [e] ClimbRG))
        (fun e => hr (by ruo [e] ClimbRG))
        (fun e => hr (by ruo [e] ClimbRG)))
    obtain ⟨c3, k3, e3, ⟨hw3, hm3, hr3, hrr3, hrm3, ho3, x, j, hx3, hj3, hb3, hxN, hjL, hI3,
        hanc3⟩, htest, hk3⟩ :=
      Exec.whileLtN_potential (P := P) (W := W) (a := 130009) (b := 130342) (body := climbBody)
      (fun c' => WordsBounded W c' ∧ c'.nmem = c.nmem ∧
        (∀ r, ¬ ClimbRG r → c'.nreg r = c2.nreg r) ∧ c'.rreg = c2.rreg ∧ c'.rmem = c2.rmem ∧
        c'.output = c2.output ∧ ∃ x j, c'.nreg 130341 = x ∧ c'.nreg 130342 = j ∧
          c'.nreg 130343 = bUP + j * N ∧ x < N ∧ j ≤ L ∧
          ClimbInv up (GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi) x j ∧ ∃ n, up^[n] y = x)
      (fun c' => (34 * LP + 34) * c'.nreg 130342) (fun c' h => h.1)
      (fun c4 ⟨hw4, hm4, hr4, hrr4, hrm4, ho4, x, j, hx4, hj4, hb4, hxN4, hjL4, hI4, hanc4⟩
          htest => by
        have hC4 := hC2.of_frame hr4
        rw [hC4.zero, hj4] at htest
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hM4 : ClimbMem c4.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up := by
          rwx [hm4]
        rw [← hm4] at hI4
        obtain ⟨c5, k5, e5, hk5, hm5, hr5, hrr5, hrm5, ho5, hj5, hb5, x', hx5, hxN5, hI5, hanc5⟩ :=
          climbBody_exec (P := P) hw4 hC4 hM4 hx4 hj4 (by omega) hb4 hxN4 hI4 hanc4
        rw [hm4] at hI5
        refine ⟨c5, k5, e5, ⟨e5.wb_right, hm5.trans hm4, fun r hr => (hr5 r hr).trans (hr4 r hr),
          hrr5.trans hrr4, hrm5.trans hrm4, ho5.trans ho4, x', j', hx5, hj5, hb5, hxN5, by omega,
          hI5, hanc5⟩, ?_⟩
        rw [hj5, hj4]
        have : (34 * LP + 34) * (j' + 1) = (34 * LP + 34) * j' + (34 * LP + 34) := by ring
        omega)
      ⟨e2.wb_right, hm2.trans hm1', fun _ _ => rfl, rfl, rfl, rfl, y, L, hx2, hj2, hb2, hyN,
        le_rfl, ⟨hng, hroot⟩, 0, rfl⟩
    have hC3 := hC2.of_frame hr3
    rw [hC3.zero, hj3] at htest
    have hj0 : j = 0 := by omega
    subst hj0
    obtain ⟨hfb, hfg⟩ := hI3.final
    -- `f := UP_0[x]`
    have htab := hM.tab 0 hL x hxN
    simp only [Nat.zero_mul, add_zero, pow_zero, Function.iterate_one] at htab
    have hwx : bUP + x ≤ W := by
      have := hM.wup
      have : x < L * N := lt_of_lt_of_le hxN (by nlinarith)
      omega
    obtain ⟨c4, k4, e4, hk4, hw4, hm4, hf4, hr4, hrr4, hrm4, ho4⟩ : ∃ c4 k4,
        Exec P W (block [.addN 130333 130326 130341, .loadN 130344 130333]) c3 c4 k4 ∧ k4 = 2 ∧
        WordsBounded W c4 ∧ c4.nmem = c3.nmem ∧ c4.nreg 130344 = up x ∧
        (∀ r, r ≠ 130333 → r ≠ 130344 → c4.nreg r = c3.nreg r) ∧ c4.rreg = c3.rreg ∧
        c4.rmem = c3.rmem ∧ c4.output = c3.output := by
      exec_block
      · rwx [hC3.rUP, hx3]
      · refine ⟨rfl, ‹_›, rfl, by config_simp; rw [hC3.rUP, hx3, hm3, htab], fun r h1 h2 => ?_,
          rfl, rfl, rfl⟩
        simp only [Machine.upd_apply, h1, h2, ite_false]
    subst hk2 hk4
    refine ⟨c4, _, .seq e0 (.seq e1 (.ifLtN_true hbad
      (.seq e2 (.seq e3 e4)))), ?_, hm4.trans hm3, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : (34 * LP + 34) * (L + 2) = (34 * LP + 34) * L + 2 * (34 * LP + 34) := by ring
      rw [hj2] at hk3
      omega
    · rw [hr4 r (fun e => hr (by ruo [e] ClimbRG GoodRG))
        (fun e => hr (by ruo [e] ClimbRG)), hr3 r hr,
        hr2 r (fun e => hr (by ruo [e] ClimbRG))
          (fun e => hr (by ruo [e] ClimbRG))
          (fun e => hr (by ruo [e] ClimbRG))]
      exact hframe1 r hr
    · rw [hrr4, hrr3, hrr2, hrr1]
    · rw [hrm4, hrm3, hrm2, hrm1]
    · rw [ho4, ho3, ho2, ho1]
    · rw [hf4]; exact hM.up_lt x hxN
    · obtain ⟨n, hn⟩ := hanc3
      exact Or.inr ⟨x, n, hn, hfb, hfg, hf4⟩
  · -- `y` is good
    have hgd : GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi y := by
      rw [hone1] at hbad; exact hg1.mp (by omega)
    have e2 := Exec.copyN (P := P) e1.wb_right 130344 130340
    refine ⟨_, 1 + (k1 + (1 + 2)), .seq e0 (.seq e1 (.ifLtN_false hbad e2)), ?_, hm1', ?_, ?_, ?_,
      ?_, ?_, Or.inl ⟨hgd, ?_⟩⟩
    · have : (34 * LP + 34) * (L + 2) ≥ 34 * LP + 25 := by nlinarith
      omega
    · intro r hr
      simp only [Machine.upd_apply]
      rw [ite_eq_right (fun e => hr (by ruo [e] ClimbRG))]
      exact hframe1 r hr
    · exact hrr1
    · exact hrm1
    · exact ho1
    · simp only [Machine.upd_same]; rwx [hy1]
    · simp only [Machine.upd_same]; rw [hy1]

end proofs

end

end Chazelle.Core.Cluster
