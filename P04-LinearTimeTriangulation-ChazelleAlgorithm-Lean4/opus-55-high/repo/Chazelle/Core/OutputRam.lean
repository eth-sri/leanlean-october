module

public import Chazelle.MacT
public import Chazelle.Core.GranRamBody
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Final.RamOutput
public import Chazelle.Core.NFBuildRegFill
public import Chazelle.Core.DownPhaseRegionBox
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.DownPhaseDrvBCorner
public import Chazelle.Core.RestoreFComplete2
public import Chazelle.Core.FuseAsmMain
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.DownPhaseDrvRPlB
public import Chazelle.Core.OraclePrepMain
public import Chazelle.Core.OracleRamLoad
public import Chazelle.Core.UpPhase15
public import Chazelle.Core.Lemma41Exec
public import Chazelle.Core.DownPhaseDrvBTopMain
public import Chazelle.Core.DownPhaseDrvHArc
public import Chazelle.Core.DownPhaseDrvRLvB
public import Chazelle.Core.DownPhaseMathHR1
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.DownPhaseDrvXRamH
public import Chazelle.Core.DownPhaseDrvDRound3
public import Chazelle.Core.RestoreFEndP
public import Chazelle.Core.SweepIoQry
public import Chazelle.Core.SweepEvGenR
public import Chazelle.Core.SweepIoCand1B
public import Chazelle.Core.SweepIoBruteLoop
public import Chazelle.Core.SweepEvBatch
public import Chazelle.Core.SweepEvWinM2
public import Chazelle.Core.SweepEvStepL5
public import Chazelle.Core.SweepIoS0CandInitTab
public import Chazelle.Core.SweepIoLoop
public import Chazelle.Core.SweepEvStopSort3
public import Chazelle.Core.SweepEvStopFin6

section
set_option hygiene false
local macro "zqrn" : tactic => `(tactic| (by_contra hc; push Not at hc; simp only [mX] at this; grind))
local macro "zqro" : tactic => `(tactic| (set v := (N.region r).chords.getD t 0; have := ((hX ztjgl).2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht))
local macro "zqrp" : tactic => `(tactic| refine ⟨by_omega, ?_, fun r hr => ?_, by_simp_all, rfl, rfl, rfl⟩)
local macro "zqrq" : tactic => `(tactic| obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hacc)
local macro "zqrr" : tactic => `(tactic| refine spec_ifLtN_false by_simp_all (spec_instr (Exec.copyN hc d s) fun _ => ?_))
local macro "zqrs" : tactic => `(tactic| refine ⟨by_omega, ?_⟩)
local macro "zqrt" : tactic => `(tactic| refine spec_ifLtN_true by_simp_all (spec_instr (Exec.copyN hc d x) fun _ => ?_))
local macro "zqru" : tactic => `(tactic| simp only [Machine.upd_same, Machine.upd_other _ _ _ (Ne.symm hd0), h0, h1])
local macro "zqrv" : tactic => `(tactic| obtain ⟨a0, a1, a2, a3, a17, a18⟩ := hA)
set_option hygiene true

/-!
# WP-N, part 5: the output program

`Output.prog` computes the orientation of the walk (`Final.orientStmt`, the sign of the corner
at a lowest vertex), then scans the regions of the normal form: for region `r` it scans its exit
chords (`chordBody`, the step `OutTrap.accStep`), completes the record (`finS`, the function
`OutTrap.finish`) and writes it at `T₀ + 4 r`, where `T₀` is the allocator on entry; the
allocator is raised by `4` per region.  The vertex-chord table is empty (at `T₀`, length `0`).

Register map (band `bOut = 22`): `220000` `n`, `220001` `1`, `220002` `0`, `220003` the reversal
flag, `220004` the handle `B`, `220005` the number of regions, `220006`/`220007`/`220008` the
chord, region and list bases, `220009` `T₀`, `220010` the region index, `220011` `4`, `220012`
`5`, `220013` the region record address, `220014` the length of its chord list, `220015` its
offset, `220016` the output address, `220017` `n - 1`, `220018` `n - 2`, `220019` `2`, `220020`
`3`, `220021` `7`; the chord scan `220100 … 220117` (index, list address, chord, chord address,
`h`, `lp`, `rp`, `dn`, the four flags, the four values, two temporaries); the completion
`220120 … 220125`.  Band `0`: the orientation program's registers, the hand-off registers and
the allocator.
-/
namespace Chazelle.Core
namespace Output
open Machine Machine.Stmt Programs
open OutWalk OutTrap
@[expose] public section
def wvS (d s : ℕ) : Stmt := .ifLtN 220002 220003 (.instr (.subN d 220017 s)) ztovy

/-- `d := nxt n s` (`n` in `220000`, `1` in `220001`). -/
def nxtS (d s : ℕ) : Stmt :=
  .seq (.instr (.addN d s 220001)) (.ifLtN d 220000 .skip ztfes)

/-- `d := inp b n s` (temporary `220116`, `n - 2` in `220018`). -/
def inpS (d s : ℕ) : Stmt :=
  .ifLtN 220002 220003
    (.seq (.instr (.addN 220116 s 220001))
      (.ifLtN 220116 220000 (.instr (.subN d 220018 s)) (.instr (.copyN d 220017))))
    ztovy

/-- The constants of the index arithmetic hold. -/
def ArithRegs (c : Config) (b : Bool) (n : ℕ) : Prop :=
  c.nreg 220000 = n ∧ c.nreg 220001 = 1 ∧ c.nreg 220002 = 0 ∧ c.nreg 220003 = b.toNat ∧
    c.nreg 220017 = n - 1 ∧ c.nreg 220018 = n - 2
section helpers
variable {P : Polygon} {W : ℕ}
variable {c : Config}
/-- Spec of `wvS`: cost `≤ 3`, `d := wv b n s`. -/
theorem wvS_spec (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (d s : ℕ) :
    ∃ c' k, Exec P W (wvS d s) c c' k ∧ k ≤ 3 ∧
      c' = { c with nreg := upd c.nreg d (wv b n (c.nreg s)) } := by
  obtain ⟨-, -, h2, h3, h17, -⟩ := hA
  unfold wvS
  cases b
  · zqrr
    tauto
  · refine spec_ifLtN_true by_simp_all (spec_instr (Exec.subN hc d 220017 s) fun _ => ?_)
    exact ⟨by_omega, by simp [wv, h17]⟩

/-- Spec of `nxtS`: cost `≤ 4`, `d := nxt n s`. -/
theorem nxtS_spec (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (d s : ℕ) (hd0 : d ≠ 220000) (_hd1 : d ≠ 220001) (hs : c.nreg s < n) (hn : n ≤ W) :
    ∃ c' k, Exec P W (nxtS d s) c c' k ∧ k ≤ 4 ∧
      c' = { c with nreg := upd c.nreg d (nxt n (c.nreg s)) } := by
  obtain ⟨h0, h1, -, -, -, -⟩ := hA
  unfold nxtS
  refine spec_seq (spec_instr (Exec.addN hc d s 220001 by_omega) fun hw₁ => ?_)
  zuhbq
  · refine spec_ifLtN_true (by
      zqru
      omega) (spec_skip hw₁ ?_)
    zqrs
    simp [nxt, hlt, h1]
  · refine spec_ifLtN_false (by
      zqru
      omega) (spec_instr (Exec.constN hw₁ d 0 (Nat.zero_le _)) fun _ => ?_)
    zqrs
    simp [nxt, hlt]

/-- Spec of `inpS`: cost `≤ 6`, `d := inp b n s`; only `d` and `220116` written. -/
theorem inpS_spec (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (d s : ℕ) (_hd : d ≠ 220116) (hsX : s ≠ 220116) (hs : c.nreg s < n) (hn : n ≤ W) :
    ∃ c' k, Exec P W (inpS d s) c c' k ∧ k ≤ 6 ∧ c'.nreg d = inp b n (c.nreg s) ∧
      SignK.FrameB (fun r => decide (r = d ∨ r = 220116)) c c' := by
  obtain ⟨h0, h1, h2, h3, h17, h18⟩ := hA
  unfold inpS
  cases b
  · zqrr
    refine ⟨by_omega, by simp [inp], fun r hr => ?_, by_simp_all, rfl, rfl, rfl⟩
    simp_all
  · refine spec_ifLtN_true by_simp_all
      (spec_seq (spec_instr (Exec.addN hc 220116 s 220001 by_omega) fun hw₁ => ?_))
    zuhbq
    · refine spec_ifLtN_true by_simp_all
        (spec_instr (Exec.subN hw₁ d 220018 s) fun _ => ?_)
      zqrp
      · simp [inp, hlt, h18, hsX]
      simp_all
    · refine spec_ifLtN_false by_simp_all
        (spec_instr (Exec.copyN hw₁ d 220017) fun _ => ?_)
      zqrp
      · simp [inp, hlt, h17]
      simp_all
end helpers

/-! ## The scan of one exit chord -/

/-- The accumulator `a` is held in the registers `220108 … 220115`. -/
def AccIn (c : Config) (a : Acc) : Prop :=
  c.nreg 220108 = a.hT.toNat ∧ c.nreg 220109 = a.hB.toNat ∧ c.nreg 220110 = a.hL.toNat ∧
    c.nreg 220111 = a.hR.toNat ∧ c.nreg 220112 = a.vt ∧ c.nreg 220113 = a.vb ∧
    c.nreg 220114 = a.pl ∧ c.nreg 220115 = a.pr

/-- Load chord `k = m (LB + OFF + TI)`: its record at `CB + 5 k` into `220104 … 220107`. -/
def loadS : Stmt :=
  block [.addN 220101 220008 220015, .addN 220101 220101 220100, .loadN 220102 220101,
    .addN 220103 220102 220102, .addN 220103 220103 220102, .addN 220103 220103 220102,
    .addN 220103 220103 220102, .addN 220103 220103 220006, .loadN 220104 220103,
    .addN 220117 220103 220001, .loadN 220105 220117, .addN 220117 220117 220001,
    .loadN 220106 220117, .addN 220117 220117 220019, .loadN 220107 220117]

/-- Top or bottom chord (`dn = r`?). -/
def dnS : Stmt :=
  .ifLtN 220107 220010 ztkrd
    (.ifLtN 220010 220107 ztkrd
      (block [.constN 220108 1, .copyN 220112 220104]))

/-- A side end (`wv p ≠ h`?, with `wv p` in `220116`): flag `F`, value `V := S`. -/
def lrS (F V S : ℕ) : Stmt :=
  .ifLtN 220116 220104 ztkrj
    (.ifLtN 220104 220116 ztkrj .skip)

/-- **The scan of one exit chord.** -/
def chordBody : Stmt :=
  .seq loadS (.seq dnS (.seq (wvS 220116 220105) (.seq (lrS 220110 220114 220105)
    (.seq (wvS 220116 220106) (.seq (lrS 220111 220115 220106)
      (block [.addN 220100 220100 220001]))))))
section chord
variable {P : Polygon} {W : ℕ}
variable {c : Config}
/-- Spec of `dnS`: a top chord sets the top flag and vertex, a bottom chord the bottom ones. -/
theorem dnS_spec (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W dnS c c' k ∧ k ≤ 6 ∧
      c' = if c.nreg 220107 = c.nreg 220010 then
        { c with nreg := upd (upd c.nreg 220108 1) 220112 (c.nreg 220104) }
      else { c with nreg := upd (upd c.nreg 220109 1) 220113 (c.nreg 220104) } := by
  unfold dnS
  rcases lt_trichotomy (c.nreg 220107) (c.nreg 220010) with h | h | h
  · zugss
    exec_block
    · zugkh
    grind
  · zumjj
    exec_block
    · zugkh
    simp_all
  · refine spec_ifLtN_false by_omega ztuaq
    exec_block
    · zugkh
    grind

/-- Spec of `lrS`: when `wv p ≠ h`, set the flag `F` and `V := S`. -/
theorem lrS_spec (hc : WordsBounded W c) (hW : 1 ≤ W) (F V S : ℕ) (hSF : S ≠ F) :
    ∃ c' k, Exec P W (lrS F V S) c c' k ∧ k ≤ 6 ∧
      c' = if c.nreg 220116 = c.nreg 220104 then c
      else { c with nreg := upd (upd c.nreg F 1) V (c.nreg S) } := by
  unfold lrS
  rcases lt_trichotomy (c.nreg 220116) (c.nreg 220104) with h | h | h
  · zugss
    exec_block
    · zugkh
    · zqrs
      rw [Setup.iteF h.ne, Machine.upd_other _ _ _ hSF]
  · refine spec_ifLtN_false by_omega (spec_ifLtN_false by_omega ztoic)
    simp_all
  · refine spec_ifLtN_false by_omega ztuaq
    exec_block
    · zugkh
    · zqrs
      rw [Setup.iteF h.ne', Machine.upd_other _ _ _ hSF]
end chord
section chord2
variable {P : Polygon} {W : ℕ}

/-- Spec of `loadS`: the record of chord `m (LB + OFF + TI)` is loaded; cost `15`. -/
theorem loadS_spec {c : Config} (hc : WordsBounded W c) {lb off t cb kk : ℕ}
    (h1 : c.nreg 220001 = 1) (h19 : c.nreg 220019 = 2) (hLB : c.nreg 220008 = lb)
    (hOFF : c.nreg 220015 = off) (hTI : c.nreg 220100 = t) (hCB : c.nreg 220006 = cb)
    (hK : c.nmem ztkac = kk) (hb1 : lb + off + t ≤ W) (hb2 : cb + 5 * kk + 4 ≤ W) :
    ∃ c' k, Exec P W loadS c c' k ∧ k = 15 ∧ c'.nreg 220104 = c.nmem ztqjp ∧
      c'.nreg 220105 = c.nmem ztnwu ∧ c'.nreg 220106 = c.nmem ztnwv ∧
      c'.nreg 220107 = c.nmem ztnww ∧
      (∀ r, (r < 220101 ∨ 220107 < r) → r ≠ 220117 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold loadS
  exec_block
  all_goals try (config_simp; simp only [hLB, hOFF, hTI, hCB, h1, h19, hK]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr1 hr2 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · zup
end chord2
section chord3
variable {P : Polygon} {W : ℕ}

/-- The registers the chord scan writes. -/
def scanB (r : ℕ) : Bool := decide ztnfy

/-- The chord scan writes only its own registers. -/
theorem wr_chordBody : SignK.wr scanB chordBody = true := by_decide

/-- **Spec of the scan of one exit chord.** -/
theorem chordBody_spec {c : Config} (hc : WordsBounded W c) {b : Bool}
    {n ri lb off t cb kk : ℕ} {rec : CRec} {a : Acc}
    (hA : ArithRegs c b n) (h19 : c.nreg 220019 = 2) (hRI : c.nreg 220010 = ri)
    (hLB : c.nreg 220008 = lb) (hOFF : c.nreg 220015 = off) (hTI : c.nreg 220100 = t)
    (hCB : c.nreg 220006 = cb) (hK : c.nmem ztkac = kk)
    (hrh : c.nmem ztqjp = rec.h) (hrl : c.nmem ztnwu = rec.lp)
    (hrr : c.nmem ztnwv = rec.rp) (hrd : c.nmem ztnww = rec.dn)
    (hb1 : lb + off + t ≤ W) (hb2 : cb + 5 * kk + 4 ≤ W) (ht : t + 1 ≤ W) (hW : 1 ≤ W)
    (hacc : AccIn c a) :
    ∃ c' k, Exec P W chordBody c c' k ∧ k ≤ 50 ∧ AccIn c' (accStep b n ri a rec) ∧
      c'.nreg 220100 = t + 1 ∧ SignK.FrameB scanB c c' := by
  obtain ⟨hA0, hA1, hA2, hA3, hA17, hA18⟩ := hA
  obtain ⟨c1, k1, e1, hk1, v104, v105, v106, v107, fr1, -, -, -, -⟩ :=
    loadS_spec (P := P) hc hA1 h19 hLB hOFF hTI hCB hK hb1 hb2
  zuqj
  have f1 := fr1
  obtain ⟨c2, k2, e2, hk2, hc2⟩ := dnS_spec (P := P) hw1 hW
  zump
  have hA2' : ztukb := by
    subst hc2; split_ifs <;>
    exact ⟨by_simp_all, by_simp_all, by_simp_all, by_simp_all,
      by simp_all, by_simp_all⟩
  obtain ⟨c3, k3, e3, hk3, hc3⟩ := wvS_spec (P := P) hw2 hA2' 220116 220105
  zubgh
  obtain ⟨c4, k4, e4, hk4, hc4⟩ := lrS_spec (P := P) hw3 hW 220110 220114 220105 by_decide
  zubgi
  have hA4 : ArithRegs c4 b n := by
    subst hc4 hc3; split_ifs <;>
    exact ⟨by simp [hA2'.1], by simp [hA2'.2.1], by simp [hA2'.2.2.1], by simp [hA2'.2.2.2.1],
      by simp [hA2'.2.2.2.2.1], by simp [hA2'.2.2.2.2.2]⟩
  obtain ⟨c5, k5, e5, hk5, hc5⟩ := wvS_spec (P := P) hw4 hA4 220116 220106
  zudpn
  obtain ⟨c6, k6, e6, hk6, hc6⟩ := lrS_spec (P := P) hw5 hW 220111 220115 220106 by_decide
  zueso
  have hone6 : c6.nreg 220001 = 1 := by
    subst hc6 hc5; split_ifs <;> simp [hA4.2.1]
  have hti6 : c6.nreg 220100 = t := by
    subst hc6 hc5 hc4 hc3 hc2; split_ifs <;> simp [f1, hTI]
  have e7 := Exec.addN (P := P) hw6 220100 220100 220001 by_omega
  have e7' : Exec P W _ c6
      { c6 with nreg := upd c6.nreg 220100 _ } 1 :=
    Exec.block_cons e7 (Exec.block_nil e7.wb_right)
  have eall : Exec P W chordBody c _ _ :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7')))))
  refine ⟨_, _, eall, by_omega, ?_, by simp [hone6, hti6], SignK.exec_frameB eall wr_chordBody⟩
  -- the accumulator
  zqrq
  have g104 : c1.nreg 220104 = rec.h := by_omega
  have g105 : c1.nreg 220105 = rec.lp := by_omega
  have g106 : c1.nreg 220106 = rec.rp := by_omega
  have g107 : c1.nreg 220107 = rec.dn := by_omega
  have g010 : c1.nreg 220010 = ri := by_grind
  have gacc : ∀ r, 220108 ≤ r → r ≤ 220115 → c1.nreg r = c.nreg r :=
    by grind
  subst hc6 hc5 hc4 hc3 hc2
  simp only [AccIn, accStep]
  rw [g107, g010]
  by_cases hd : rec.dn = ri <;> simp only [hd, ite_true, ite_false] <;>
    simp only [Machine.upd_same, Machine.upd_other, ne_eq, not_false_eq_true, Nat.reduceEqDiff] <;>
    rw [g104, g105] <;>
    by_cases hl : wv b n rec.lp = rec.h <;> simp only [hl, ite_true, ite_false] <;>
    simp only [Machine.upd_other, ne_eq,
      not_false_eq_true, Nat.reduceEqDiff] <;>
    rw [g104, g106] <;>
    by_cases hr : wv b n rec.rp = rec.h <;> simp only [hr, ite_true, ite_false] <;>
    simp only [Machine.upd_same, Machine.upd_other, ne_eq,
      not_false_eq_true, Nat.reduceEqDiff] <;>
    simp [gacc, a1, a2, a3, a4, a5, a6, a7, a8]
end chord3

/-! ## The scan of a region's exit chords -/

/-- The scan loop. -/
def chordLoop : Stmt := .whileLtN 220100 220014 chordBody
section loop
variable {P : Polygon} {W : ℕ}

/-- The scan of the first `t` chords of the list `L`. -/
def scanAcc (b : Bool) (n ri : ℕ) (N : NF) (L : List ℕ) (t : ℕ) : Acc :=
  ((L.take t).map N.chord).foldl ztbvn Acc.init

/-- One more chord of the list. -/
theorem scanAcc_succ (b : Bool) (n ri : ℕ) (N : NF) (L : List ℕ) {t : ℕ} (ht : t < L.length) :
    scanAcc b n ri N L ztbx = accStep b n ri (scanAcc b n ri N L t) (N.chord ztemz) := by
  unfold scanAcc
  rw [List.take_add_one, List.map_append, List.foldl_append, List.getElem?_eq_getElem ht]
  simp_all

/-- The invariant of the scan loop (`cs` the configuration on entry). -/
def ScanInv (W : ℕ) (b : Bool) (n ri : ℕ) (N : NF) (L : List ℕ) (cs c : Config) : Prop :=
  WordsBounded W c ∧ SignK.FrameB scanB cs c ∧ c.nreg 220100 ≤ L.length ∧
    AccIn c (scanAcc b n ri N L (c.nreg 220100))

/-- **Spec of the scan loop.** -/
theorem chordLoop_spec {cs : Config} {b : Bool} {n ri lb off cb : ℕ} {N : NF} {L : List ℕ}
    (hA : ArithRegs cs b n) (h19 : cs.nreg 220019 = 2) (hRI : cs.nreg 220010 = ri)
    (hLB : cs.nreg 220008 = lb) (hOFF : cs.nreg 220015 = off) (hCB : cs.nreg 220006 = cb)
    (hLEN : cs.nreg 220014 = L.length)
    (hK : ∀ t, t < L.length → cs.nmem ztkac = L.getD t 0 ∧ lb + off + t ≤ W ∧
      cb + 5 * L.getD t 0 + 4 ≤ W ∧
      cs.nmem (cb + 5 * L.getD t 0) = (N.chord ztemz).h ∧
      cs.nmem (cb + 5 * L.getD t 0 + 1) = (N.chord ztemz).lp ∧
      cs.nmem (cb + 5 * L.getD t 0 + 2) = (N.chord ztemz).rp ∧
      cs.nmem (cb + 5 * L.getD t 0 + 4) = (N.chord ztemz).dn)
    (hW : 1 ≤ W) (hI : ScanInv W b n ri N L cs cs) (h0 : cs.nreg 220100 = 0) :
    ∃ c' k, Exec P W chordLoop cs c' k ∧ k ≤ 52 * L.length + 2 ∧
      AccIn c' (scanAcc b n ri N L L.length) ∧ SignK.FrameB scanB cs c' := by
  have hfr : ∀ c : Config, SignK.FrameB scanB cs c → ∀ r, scanB r = false → c.nreg r = cs.nreg r :=
    fun c h r hr => h.1 r hr
  obtain ⟨c', k, he, hI', hex, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 220100) (b := 220014)
    (body := chordBody) (ScanInv W b n ri N L cs) (fun c => L.length - c.nreg 220100) 50
    ztcvf (fun c h htest => by
      obtain ⟨hw, hf, hle, hacc⟩ := h
      have g : ∀ r, scanB r = false → c.nreg r = cs.nreg r := by_simp_all
      have e14 : c.nreg 220014 = L.length := by rw [g _ by_decide, hLEN]
      rw [e14] at htest
      set t := c.nreg 220100 with htdef
      obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := hK t htest
      zuiyj
      have hA' : ztuka := by
        zqrv
        exact ⟨by rw [g _ by_decide, a0], by rw [g _ by_decide, a1], by rw [g _ by_decide, a2],
          by rw [g _ by_decide, a3], by rw [g _ by_decide, a17], by rw [g _ by_decide, a18]⟩
      have hlen : L.length ≤ W := by rw [← e14]; exact hw.1 _
      obtain ⟨c'', k'', e'', hk'', hacc'', ht'', hfr''⟩ := chordBody_spec (P := P) hw hA'
        (by rw [g _ by_decide, h19]) (by rw [g _ by_decide, hRI]) (by rw [g _ by_decide, hLB])
        (by rw [g _ by_decide, hOFF]) rfl (by rw [g _ by_decide, hCB]) (by zvmwi; exact hk1)
        (by zvmwi; exact hk4) (by zvmwi; exact hk5) (by zvmwi; exact hk6)
        (by zvmwi; exact hk7) hk2 hk3 by_omega hW hacc
      refine ⟨c'', k'', e'', ⟨e''.wb_right, hf.trans hfr'', by_omega, ?_⟩, hk'', by_omega⟩
      rw [ht'', scanAcc_succ b n ri N L htest]
      exact hacc'') hI
  obtain ⟨hw', hf', hle', hacc'⟩ := hI'
  have e14 : c'.nreg 220014 = L.length := by rw [hf'.1 _ by_decide, hLEN]
  rw [e14] at hex
  have ht' : c'.nreg 220100 = L.length := by_omega
  refine ⟨c', k, he, ?_, by_simp_all, hf'⟩
  omega
end loop

/-! ## Completion of the record -/

/-- `d := if flag f then x else (if flag g then wv y else nxt z)`. -/
def pickS (d f x g y z : ℕ) : Stmt :=
  .ifLtN 220002 f ztign (.ifLtN 220002 g (wvS d y) (nxtS d z))

/-- `d := if flag f then x else wv (nxt z)` (temporary `220117`). -/
def cornerS (d f x z : ℕ) : Stmt :=
  .ifLtN 220002 f ztign (.seq (nxtS 220117 z) (wvS d 220117))

/-- **Completion**: `220120` the left walk edge, `220121` the right walk edge, `220122` the top
vertex, `220123` the bottom vertex, `220124`/`220125` the left and right edges of `Q`. -/
def finS : Stmt :=
  .seq (pickS 220120 220110 220114 220108 220112 220115)
    (.seq (pickS 220121 220111 220115 220109 220113 220120)
      (.seq (cornerS 220122 220108 220112 220121)
        (.seq (cornerS 220123 220109 220113 220120)
          (.seq (inpS 220124 220120) (inpS 220125 220121)))))
section fin
variable {P : Polygon} {W : ℕ}
variable {c : Config}
/-- Spec of `pickS`: cost `≤ 8`. -/
theorem pickS_spec (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (hn : n ≤ W) (d f x g y z : ℕ) (hd0 : d ≠ 220000) (hd1 : d ≠ 220001) {bf bg : Bool}
    (hf : c.nreg f = bf.toNat) (hg : c.nreg g = bg.toNat)
    (hz : bf = false → bg = false → c.nreg z < n) :
    ∃ c' k, Exec P W (pickS d f x g y z) c c' k ∧ k ≤ 8 ∧
      c' = { c with nreg := (upd c.nreg d
        (if bf then c.nreg x else if bg then wv b n (c.nreg y) else nxt n ztvjz)) } := by
  zumbg
  unfold pickS
  cases bf
  · zudx
    cases bg
    · zudx
      obtain ⟨c', k, e, hk, rfl⟩ := nxtS_spec (P := P) hc hA d z hd0 hd1 by_simp_all hn
      grind
    · zuek
      obtain ⟨c', k, e, hk, rfl⟩ := wvS_spec (P := P) hc hA d y
      grind
  · zqrt
    simp

/-- Spec of `cornerS`: cost `≤ 9`; only `d` and `220117` written. -/
theorem cornerS_spec (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (hn : n ≤ W) (d f x z : ℕ) (_hd : d ≠ 220117) {bf : Bool} (hf : c.nreg f = bf.toNat)
    (hz : bf = false → c.nreg z < n) :
    ∃ c' k, Exec P W (cornerS d f x z) c c' k ∧ k ≤ 9 ∧
      c'.nreg d = (if bf then c.nreg x else wv b n (nxt n ztvjz)) ∧
      SignK.FrameB (fun r => decide (r = d ∨ r = 220117)) c c' := by
  zumbg
  unfold cornerS
  cases bf
  · zudx
    obtain ⟨c1, k1, e1, hk1, rfl⟩ := nxtS_spec hc hA 220117 z by_decide by_decide
      (hz rfl) hn
    have hA1 : ArithRegs { c with nreg := upd c.nreg 220117 (nxt n (c.nreg z)) } b n := by
      tauto
    obtain ⟨c2, k2, e2, hk2, rfl⟩ := wvS_spec e1.wb_right hA1 d 220117
    refine ⟨_, _, e1.seq e2, by_omega, by_simp, fun r hr => ?_, by_simp_all, rfl, rfl, rfl⟩
    simp_all
  · zqrt
    refine ⟨by_omega, by_simp, fun r hr => ?_, by_simp_all, rfl, rfl, rfl⟩
    simp_all
end fin
section fin2
variable {P : Polygon} {W : ℕ}

/-- The registers the completion writes. -/
def finB (r : ℕ) : Bool := decide (220116 ≤ r ∧ r ≤ 220125)

/-- The completion writes only its own registers. -/
theorem wr_finS : SignK.wr finB finS = true := by_decide

/-- The constants of the index arithmetic survive a frame not touching them. -/
theorem ArithRegs.frame {c c' : Config} {b : Bool} {n : ℕ} {B : ℕ → Bool} (h : ArithRegs c b n)
    (hf : SignK.FrameB B c c') (h0 : B 220000 = false) (h1 : B 220001 = false)
    (h2 : B 220002 = false) (h3 : B 220003 = false) (h17 : B 220017 = false)
    (h18 : B 220018 = false) : ArithRegs c' b n := by
  obtain ⟨a0, a1, a2, a3, a17, a18⟩ := h
  exact ⟨by rw [hf.1 _ h0, a0], by rw [hf.1 _ h1, a1], by rw [hf.1 _ h2, a2],
    by rw [hf.1 _ h3, a3], by rw [hf.1 _ h17, a17], by rw [hf.1 _ h18, a18]⟩

/-- **Spec of the completion.** -/
theorem finS_spec {c : Config} (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (hn : n ≤ W) {a : Acc} (hacc : AccIn c a) (hpl : a.pl < n) (hpr : a.pr < n) (hvt : a.vt < n)
    (hvb : a.vb < n) :
    ∃ c' k, Exec P W finS c c' k ∧ k ≤ 50 ∧
      c'.nreg 220124 = (finish b n a).left ∧ c'.nreg 220125 = (finish b n a).right ∧
      c'.nreg 220122 = (finish b n a).top ∧ c'.nreg 220123 = (finish b n a).bot ∧
      SignK.FrameB finB c c' := by
  zqrq
  have hn1 := by_omega
  set PLv := (if a.hL then a.pl else if a.hT then wv b n a.vt else nxt n a.pr) with hPLv
  have hPL : PLv < n := by
    rw [hPLv]; split_ifs
    · omega
    · exact wv_lt hvt
    · exact nxt_lt hpr
  set PRv := (if a.hR then a.pr else if a.hB then wv b n a.vb else nxt n PLv) with hPRv
  have hPR : PRv < n := by
    rw [hPRv]; split_ifs
    · omega
    · exact wv_lt hvb
    · exact nxt_lt hPL
  -- stage 1
  obtain ⟨c1, k1, e1, hk1, hc1⟩ := pickS_spec (P := P) hc hA hn 220120 220110 220114 220108 220112
    220115 by_decide by_decide a3 a1 ztqnd
  have v1 : c1.nreg 220120 = PLv := by_simp_all
  have hA1 : ArithRegs c1 b n := by
    obtain ⟨b0, b1, b2, b3, b17, b18⟩ := hA
    zvmwl; exact ⟨by_simp_all, by_simp_all, by_simp_all, by_simp_all, by_simp_all,
      by simp_all⟩
  -- stage 2
  obtain ⟨c2, k2, e2, hk2, hc2⟩ := pickS_spec (P := P) (bf := a.hR) (bg := a.hB) e1.wb_right hA1
    hn 220121 220111 220115 220109 220113 220120 by_decide by_decide by_simp_all
    by_simp_all ztqnd
  have v2 : c2.nreg 220121 = PRv := by
    zumyw; zumzo; rw [v1, hc1]; simp [a8, a6, hPRv]
  have v2' : c2.nreg 220120 = PLv := by zumyw; tauto
  have hA2 : ztukb := by
    obtain ⟨b0, b1, b2, b3, b17, b18⟩ := hA1
    zumyw; exact ⟨by_tauto, by_tauto, by_tauto, by_tauto, by_tauto,
      by tauto⟩
  have g2 : ∀ r, r ≠ 220120 → r ≠ 220121 → c2.nreg r = c.nreg r := fun r h1 h2 => by
    rw [hc2, hc1]; zungi
  -- stage 3
  obtain ⟨c3, k3, e3, hk3, v3, f3⟩ := cornerS_spec (P := P) e2.wb_right hA2 hn 220122 220108
    220112 220121 by_decide (by rw [g2 _ by_decide by_decide]; exact a1)
    (fun _ => by_omega)
  have hA3 := hA2.frame f3 rfl rfl rfl rfl rfl rfl
  -- stage 4
  obtain ⟨c4, k4, e4, hk4, v4, f4⟩ := cornerS_spec (P := P) e3.wb_right hA3 hn 220123 220109
    220113 220120 by_decide (by rw [f3.1 _ rfl, g2 _ by_decide by_decide]; exact a2)
    (fun _ => by rw [f3.1 _ rfl, v2']; omega)
  have hA4 := hA3.frame f4 rfl rfl rfl rfl rfl rfl
  -- stage 5, 6
  obtain ⟨c5, k5, e5, hk5, v5, f5⟩ := inpS_spec (P := P) e4.wb_right hA4 220124 220120 by_decide
    by_decide (by rw [f4.1 _ rfl, f3.1 _ rfl, v2']; omega) hn
  have hA5 := hA4.frame f5 rfl rfl rfl rfl rfl rfl
  obtain ⟨c6, k6, e6, hk6, v6, f6⟩ := inpS_spec (P := P) e5.wb_right hA5 220125 220121 by_decide
    by_decide (by rw [f5.1 _ rfl, f4.1 _ rfl, f3.1 _ rfl, v2]; omega) hn
  have eall : Exec P W finS c c6 _ :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
  refine ⟨c6, _, eall, by_omega, ?_, ?_, ?_, ?_, SignK.exec_frameB eall wr_finS⟩
  · rw [f6.1 220124 rfl, v5, f4.1 220120 rfl, f3.1 220120 rfl, v2']
    rfl
  · rw [v6, f5.1 220121 rfl, f4.1 220121 rfl, f3.1 220121 rfl, v2]
    rfl
  · rw [f6.1 220122 rfl, f5.1 220122 rfl, f4.1 220122 rfl, v3, v2,
      g2 220112 by_decide by_decide, a5]
    rfl
  · rw [f6.1 220123 rfl, f5.1 220123 rfl, v4, f3.1 220113 rfl, f3.1 220120 rfl, v2',
      g2 220113 by_decide by_decide, a6]
    rfl
end fin2

/-! ## Reading a robust normal form -/

/-- The memory `m` below `A`, the constant `X` above. -/
def mX (A : ℕ) (m : ℕ → ℕ) (X : ℕ) (y : ℕ) : ℕ := if y < A then m y else X
variable {A : ℕ} {m : ℕ → ℕ} {X y : ℕ}
/-- `mX` below `A`. -/
theorem mX_of_lt (h : y < A) : mX A m X y = m y := by
  simp [mX, h]

/-- `mX` at or above `A`. -/
theorem mX_of_ge (h : A ≤ y) : mX A m X y = X := by
  simp [mX, not_lt.2 h]

/-- The facts of a normal form in memory that the output program reads, with the addresses it
computes below `A`. -/
structure NFReads (m : ℕ → ℕ) (A B : ℕ) (N : NF) : Prop where
  nr : m zthb = N.nRegions ∧ B + 2 < A
  regs : ∀ r, r < N.nRegions →
    m ztyjm = (N.region r).chords.length ∧ m zter + 5 * r + 2 < A
  lists : ∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
    m ztbanz = (N.region r).chords.getD t 0 ∧
      m ztlw + m ztwnp + t < A ∧ m zter + 5 * r + 3 < A
  chords : ∀ k, k < N.nChords →
    m (m ztkh + 5 * k) = (N.chord k).h ∧ m (m ztkh + 5 * k + 1) = (N.chord k).lp ∧
      m (m ztkh + 5 * k + 2) = (N.chord k).rp ∧ m (m ztkh + 5 * k + 4) = (N.chord k).dn ∧
      m ztkh + 5 * k + 4 < A

/-- **A robust normal form is read below its bound.** -/
theorem nfReads_of_robust {A B : ℕ} {m : ℕ → ℕ} {N : NF} (h : Robust A m fun m' => NFAt m' B N) :
    NFReads m A B N := by
  have hm := h.holds
  have hX : ∀ X, NFAt (mX A m X) B N := fun X => h _ fun a ha => mX_of_lt ha
  refine ⟨⟨hm.2.2.1, ?_⟩, fun r hr => ⟨(hm.2.2.2.2.2.2.2.1 r hr).2.1, ?_⟩,
    fun r hr t ht => ⟨((hm.2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht).trans rfl, ?_, ?_⟩,
    fun k hk => ⟨(hm.2.2.2.2.2.1 k hk).1, (hm.2.2.2.2.2.1 k hk).2.1, (hm.2.2.2.2.2.1 k hk).2.2.1,
      (hm.2.2.2.2.2.1 k hk).2.2.2.2, ?_⟩⟩
  · zuca
    have := (hX (N.nRegions + 1)).2.2.1
    rw [mX_of_ge hc] at this; unfold NF.nRegions at this; omega
  · set v := (N.region r).chords.length
    have := ((hX ztjgl).2.2.2.2.2.2.2.1 r hr).2.1
    zqrn
  · zqro
    zqrn
  · zqro
    zqrn
  · set v := (N.chord k).dn
    have := ((hX ztjgl).2.2.2.2.2.1 k hk).2.2.2.2
    zqrn

/-! ## One region -/

/-- Read the chord list of the region (length, offset) and reset the scan. -/
def regPre : Stmt :=
  block [.addN 220117 220013 220019, .loadN 220014 220117, .addN 220117 220013 220020,
    .loadN 220015 220117, .constN 220100 0, .constN 220108 0, .constN 220109 0, .constN 220110 0,
    .constN 220111 0, .constN 220112 0, .constN 220113 0, .constN 220114 0, .constN 220115 0]

/-- Write the record at the output address and advance. -/
def storeS : Stmt :=
  block [.storeN 220016 220124, .addN 220117 220016 220001, .storeN 220117 220125,
    .addN 220117 220117 220001, .storeN 220117 220122, .addN 220117 220117 220001,
    .storeN 220117 220123, .addN 220016 220016 220011, .addN 220013 220013 220012,
    .addN 220010 220010 220001, .addN 9999 9999 220011]

/-- **One region**: scan its exit chords, complete and write its record. -/
def regionBody : Stmt := .seq regPre (.seq chordLoop (.seq finS storeS))

/-- The region loop. -/
def regionLoop : Stmt := .whileLtN 220010 220005 regionBody
section region
variable {P : Polygon} {W : ℕ}

/-- The registers `regPre` writes. -/
def preB (r : ℕ) : Bool := decide (r = 220014 ∨ r = 220015 ∨ ztnfy)

/-- `regPre` writes only its own registers. -/
theorem wr_regPre : SignK.wr preB regPre = true := by_decide
variable {c : Config}
/-- Spec of `regPre`: the length and offset of the chord list of the region, the scan reset; cost `13`. -/
theorem regPre_spec (hc : WordsBounded W c) {ra : ℕ} (h19 : c.nreg 220019 = 2)
    (h20 : c.nreg 220020 = 3) (hRA : c.nreg 220013 = ra) (hb : ra + 3 ≤ W) :
    ∃ c' k, Exec P W regPre c c' k ∧ k = 13 ∧ c'.nreg 220014 = c.nmem zttyf ∧
      c'.nreg 220015 = c.nmem zttyg ∧ c'.nreg 220100 = 0 ∧ AccIn c' Acc.init ∧
      SignK.FrameB preB c c' := by
  have e : ∃ c' k, Exec P W regPre c c' k ∧ k = 13 ∧ c'.nreg 220014 = c.nmem zttyf ∧
      c'.nreg 220015 = c.nmem zttyg ∧ c'.nreg 220100 = 0 ∧ AccIn c' Acc.init := by
    unfold regPre
    exec_block
    all_goals try (config_simp; simp only [hRA, h19, h20]; omega)
    zubqj
    refine ztboc
    · simp_all
    · simp_all
    · config_simp
    trivial
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4⟩ := e
  exact ⟨c', k, ex, hk, h1, h2, h3, h4, SignK.exec_frameB ex wr_regPre⟩

/-- Spec of `storeS`: the four words of the record at the output address, the addresses and the allocator advanced; cost `11`. -/
theorem storeS_spec (hc : WordsBounded W c) {o ra ri al : ℕ}
    (h1 : c.nreg 220001 = 1) (h11 : c.nreg 220011 = 4) (h12 : c.nreg 220012 = 5)
    (hO : c.nreg 220016 = o) (hRA : c.nreg 220013 = ra) (hRI : c.nreg 220010 = ri)
    (hAL : c.nreg 9999 = al) (hb1 : o + 4 ≤ W) (hb2 : ra + 5 ≤ W) (hb3 : ri + 1 ≤ W)
    (hb4 : al + 4 ≤ W) :
    ∃ c' k, Exec P W storeS c c' k ∧ k = 11 ∧
      c'.nmem = upd (upd (upd (upd c.nmem o (c.nreg 220124)) ztbql (c.nreg 220125)) ztdvm
        (c.nreg 220122)) (o + 3) (c.nreg 220123) ∧
      c'.nreg 220016 = o + 4 ∧ c'.nreg 220013 = ra + 5 ∧ c'.nreg 220010 = ri + 1 ∧
      c'.nreg 9999 = al + 4 ∧
      (∀ r, r ≠ 220117 → r ≠ 220016 → r ≠ 220013 → r ≠ 220010 → r ≠ 9999 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold storeS
  exec_block
  all_goals try (config_simp; simp only [hO, hRA, hRI, hAL, h1, h11, h12]; omega)
  simp_all
end region
section region2
variable {P : Polygon} {W : ℕ}
variable (b : Bool) (n ri : ℕ)
/-- The values of the scan stay below `n`. -/
theorem fold_lt (L : List CRec) (hL : ∀ c ∈ L, c.h < n ∧ c.lp < n ∧ c.rp < n)
    (a : Acc) (ha : a.vt < n ∧ a.vb < n ∧ a.pl < n ∧ a.pr < n) :
    (L.foldl ztbvn a).vt < n ∧ (L.foldl ztbvn a).vb < n ∧
      (L.foldl ztbvn a).pl < n ∧ (L.foldl ztbvn a).pr < n := by
  induction L generalizing a with
  | nil => exact ha
  | cons c L ih =>
    zuhpf
    apply ih by_grind
    obtain ⟨h1, h2, h3⟩ := hL c List.mem_cons_self
    zufiq
    refine ztfh <;> simp only [accStep] <;> split_ifs <;> assumption

/-- The scan of the whole list is `accOf`. -/
theorem scanAcc_length (N : NF) :
    scanAcc b n ri N (N.region ri).chords (N.region ri).chords.length = accOf b n N ri := by
  unfold scanAcc accOf; simp

/-- The record `rec` is stored at `A` (four words). -/
def TrapAt (m : ℕ → ℕ) (A : ℕ) (rec : Final.TrapRec) : Prop :=
  m A = rec.left ∧ m ztbo = rec.right ∧ m ztbcl = rec.top ∧ m zttf = rec.bot

/-- The registers the region loop keeps. -/
def regFree (r : ℕ) : Prop :=
  ¬ (r = 220010 ∨ r = 220013 ∨ r = 220014 ∨ r = 220015 ∨ r = 220016 ∨ (220100 ≤ r ∧ r ≤ 220125) ∨
    r = 9999)

/-- The constants of the region loop. -/
def RegConsts (c : Config) (b : Bool) (n nR cb lb T0 : ℕ) : Prop :=
  ArithRegs c b n ∧ c.nreg 220005 = nR ∧ c.nreg 220006 = cb ∧ c.nreg 220008 = lb ∧
    c.nreg 220009 = T0 ∧ c.nreg 220011 = 4 ∧ c.nreg 220012 = 5 ∧ c.nreg 220019 = 2 ∧
    c.nreg 220020 = 3

/-- The invariant of the region loop (`c0` on entry, `m0` the memory of the normal form below
`T0`). -/
def RegInv (W : ℕ) (b : Bool) (n : ℕ) (N : NF) (T0 rb : ℕ) (m0 : ℕ → ℕ) (c0 c : Config) : Prop :=
  WordsBounded W c ∧ (∀ r, regFree r → c.nreg r = c0.nreg r) ∧
    (∀ r, regFree r → c.rreg r = c0.rreg r) ∧
    c.rmem = c0.rmem ∧ c.output = c0.output ∧ c.nreg 220010 ≤ N.nRegions ∧
    c.nreg 220013 = rb + 5 * c.nreg 220010 ∧ c.nreg 220016 = T0 + 4 * c.nreg 220010 ∧
    c.nreg 9999 = T0 + 4 * c.nreg 220010 ∧ (∀ a, a < T0 → c.nmem a = m0 a) ∧
    ∀ s, s < c.nreg 220010 → TrapAt c.nmem (T0 + 4 * s) (trapOf b n N s)
end region2
section region3
variable {P : Polygon} {W : ℕ}

/-- **Spec of one region.** -/
theorem regionBody_spec {c0 c : Config} {b : Bool} {n B T0 rb lb cb : ℕ} {N : NF} {m0 : ℕ → ℕ}
    (hC : RegConsts c0 b n N.nRegions cb lb T0) (hRd : NFReads m0 T0 B N) (hrb : m0 zter = rb)
    (hlb : m0 ztlw = lb) (hcb : m0 ztkh = cb)
    (hlen : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ 4)
    (hent : ∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
      (N.region r).chords.getD t 0 < N.nChords)
    (hrec : ∀ k, k < N.nChords → (N.chord k).h < n ∧ (N.chord k).lp < n ∧ (N.chord k).rp < n)
    (hn : 1 ≤ n) (hnW : n + 1 ≤ W) (hTW : T0 + 4 * N.nRegions + 8 ≤ W)
    (hI : RegInv W b n N T0 rb m0 c0 c) (ht : c.nreg 220010 < N.nRegions) :
    ∃ c' k, Exec P W regionBody c c' k ∧ RegInv W b n N T0 rb m0 c0 c' ∧ k ≤ 330 ∧
      c'.nreg 220010 = c.nreg 220010 + 1 ∧ c'.nreg 9999 ≤ c.nreg 9999 + k := by
  obtain ⟨hw, hfr, hrr, hrm, ho, hle, hRA, hOUT, hAL, hmem, hrecs⟩ := hI
  obtain ⟨hA, hnR, hcb', hlb', hT0, h4, h5, h19, h20⟩ := hC
  set ri := c.nreg 220010 with hri
  have g := hfr
  have hAc : ztuka := by
    zqrv
    exact ⟨by rw [g _ by_tauto, a0], by rw [g _ by_tauto, a1],
      by rw [g _ by_tauto, a2], by rw [g _ by_tauto, a3],
      by rw [g _ by_tauto, a17], by rw [g _ by_tauto, a18]⟩
  have c19 : c.nreg 220019 = 2 := by rw [g _ by_tauto, h19]
  have c20 : c.nreg 220020 = 3 := by rw [g _ by_tauto, h20]
  have c11 : c.nreg 220011 = 4 := by rw [g _ by_tauto, h4]
  have c12 : c.nreg 220012 = 5 := by rw [g _ by_tauto, h5]
  have c6 : c.nreg 220006 = cb := by rw [g _ by_tauto, hcb']
  have c8 : c.nreg 220008 = lb := by rw [g _ by_tauto, hlb']
  have hT0W : T0 ≤ W := by_omega
  obtain ⟨hlenm, hlenA⟩ := hRd.regs ri ht
  rw [hrb] at hlenm hlenA
  -- stage 1
  obtain ⟨c1, k1, e1, hk1, v14, v15, v100, vacc, f1⟩ :=
    regPre_spec (P := P) hw c19 c20 hRA by_omega
  zuqj
  zumas
  have m1 := f1.2.2.1
  have hlen1 : c1.nreg 220014 = (N.region ri).chords.length := by_simp_all
  -- the chord data
  have hK : ∀ t, t < (N.region ri).chords.length → c1.nmem (lb + c1.nreg 220015 + t) = (N.region ri).chords.getD t 0 ∧
      lb + c1.nreg 220015 + t ≤ W ∧ cb + 5 * (N.region ri).chords.getD t 0 + 4 ≤ W ∧
      c1.nmem (cb + 5 * (N.region ri).chords.getD t 0) = (N.chord zteiq).h ∧
      c1.nmem (cb + 5 * (N.region ri).chords.getD t 0 + 1) = (N.chord zteiq).lp ∧
      c1.nmem (cb + 5 * (N.region ri).chords.getD t 0 + 2) = (N.chord zteiq).rp ∧
      c1.nmem (cb + 5 * (N.region ri).chords.getD t 0 + 4) = (N.chord zteiq).dn := by
    intro t htl
    obtain ⟨l1, l2, l3⟩ := hRd.lists ri ht t htl
    rw [hlb, hrb] at l1 l2
    rw [hrb] at l3
    have hoff : c1.nreg 220015 = m0 (rb + 5 * ri + 3) := by_grind
    have hk := hent ri ht t htl
    obtain ⟨q1, q2, q3, q4, q5⟩ := hRd.chords _ hk
    grind
  have hA1 := hAc.frame f1 rfl rfl rfl rfl rfl rfl
  -- stage 2
  obtain ⟨c2, k2, e2, hk2, vacc2, f2⟩ := chordLoop_spec (P := P) (cs := c1) (L := (N.region ri).chords) (N := N)
    (ri := ri) hA1 (by rw [g1 _ rfl, c19]) (by rw [g1 _ rfl]) (by rw [g1 _ rfl, c8]) rfl
    (by rw [g1 _ rfl, c6]) hlen1 hK by_omega
    ⟨hw1, SignK.FrameB.refl _ _, by_omega, by rw [v100]; tauto⟩ v100
  zump
  rw [scanAcc_length] at vacc2
  have hA2 := hA1.frame f2 rfl rfl rfl rfl rfl rfl
  -- stage 3
  have hbnd := fold_lt b n ri ((N.region ri).chords.map N.chord) (fun cr hcr => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hcr
      obtain ⟨t, htl, rfl⟩ := List.getElem_of_mem hk
      have e : (N.region ri).chords.getD t 0 = (N.region ri).chords[t] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
      grind) Acc.init
    ⟨hn, hn, hn, hn⟩
  obtain ⟨c3, k3, e3, hk3, v124, v125, v122, v123, f3⟩ := finS_spec (P := P) hw2 hA2
    by_omega vacc2 hbnd.2.2.1 hbnd.2.2.2 hbnd.1 hbnd.2.1
  zubgh
  -- registers through the three stages
  have gg : ∀ r, preB r = false → scanB r = false → finB r = false → c3.nreg r = c.nreg r :=
    fun r a1 a2 a3 => by rw [f3.1 r a3, f2.1 r a2, f1.1 r a1]
  -- stage 4
  obtain ⟨c4, k4, e4, hk4, m4, v16, v13, v10, v9999, g4, rr4, rm4, o4⟩ := storeS_spec (P := P) hw3
    (o := T0 + 4 * ri) (ra := rb + 5 * ri) (ri := ri) (al := T0 + 4 * ri)
    (by rw [gg _ rfl rfl rfl, hAc.2.1]) (by rw [gg _ rfl rfl rfl, c11])
    (by rw [gg _ rfl rfl rfl, c12]) (by rw [gg _ rfl rfl rfl, hOUT]) (by rw [gg _ rfl rfl rfl, hRA])
    (by rw [gg _ rfl rfl rfl]) (by rw [gg _ rfl rfl rfl, hAL]) by_omega by_omega by_omega
    by_omega
  have eall : Exec P W regionBody c c4 _ := e1.seq (e2.seq (e3.seq e4))
  have hlenL := hlen ri ht
  refine ⟨c4, _, eall, ⟨e4.wb_right, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by omega, v10, by_omega⟩
  · zumud
    rw [g4 r by_omega by_omega by_omega by_omega by_omega,
      gg r ztqgo ztqgp ztqgm]
    exact g r ztozv
  · zumud
    rw [rr4, f3.2.1 r ztqgm, f2.2.1 r ztqgp,
      f1.2.1 r ztqgo]
    exact hrr r ztozv
  · rw [rm4, f3.2.2.2.1, f2.2.2.2.1, f1.2.2.2.1, hrm]
  · rw [o4, f3.2.2.2.2, f2.2.2.2.2, f1.2.2.2.2, ho]
  · omega
  · omega
  · omega
  · omega
  · zuge
    rw [m4]
    zudi
    rw [Setup.iteF by_omega, Setup.iteF by_omega, Setup.iteF by_omega, Setup.iteF by_omega,
      f3.2.2.1, f2.2.2.1, m1, hmem a ha]
  · zugg
    rw [v10] at hs
    have mem3 : ztmut := by zunyl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · obtain ⟨t1, t2, t3, t4⟩ := hrecs s hs
      refine ztfh <;> rw [m4] <;> zumwj <;>
        rw [Setup.iteF by_omega, Setup.iteF by_omega, Setup.iteF by_omega, Setup.iteF by_omega, mem3] <;>
        assumption
    · refine ztfh <;> rw [m4]
      · simp [v124, trapOf]
      · simp [v125, trapOf]
      · simp [v122, trapOf]
      · simp [v123, trapOf]
end region3
section region4
variable {P : Polygon} {W : ℕ}

/-- **Spec of the region loop.** -/
theorem regionLoop_spec {c0 c : Config} {b : Bool} {n B T0 rb lb cb : ℕ} {N : NF} {m0 : ℕ → ℕ}
    (hC : RegConsts c0 b n N.nRegions cb lb T0) (hRd : NFReads m0 T0 B N) (hrb : m0 zter = rb)
    (hlb : m0 ztlw = lb) (hcb : m0 ztkh = cb)
    (hlen : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ 4)
    (hent : ∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
      (N.region r).chords.getD t 0 < N.nChords)
    (hrec : ∀ k, k < N.nChords → (N.chord k).h < n ∧ (N.chord k).lp < n ∧ (N.chord k).rp < n)
    (hn : 1 ≤ n) (hnW : n + 1 ≤ W) (hTW : T0 + 4 * N.nRegions + 8 ≤ W)
    (hI : RegInv W b n N T0 rb m0 c0 c) (h0 : c.nreg 220010 = 0) :
    ∃ c' k, Exec P W regionLoop c c' k ∧ RegInv W b n N T0 rb m0 c0 c' ∧
      c'.nreg 220010 = N.nRegions ∧ k ≤ 332 * N.nRegions + 2 ∧ c'.nreg 9999 ≤ c.nreg 9999 + k := by
  have hnR : ∀ c', RegInv W b n N T0 rb m0 c0 c' → c'.nreg 220005 = N.nRegions := fun c' h => by
    rw [h.2.1 _ by_tauto, hC.2.1]
  obtain ⟨c', k, he, hI', hex, hk, hΨ⟩ := Setup.whileLtN_acc (P := P) (a := 220010) (b := 220005)
    (body := regionBody) (RegInv W b n N T0 rb m0 c0) (fun c => N.nRegions - c.nreg 220010) 330
    ztqnj ztcvf (fun c h htest => by
      rw [hnR c h] at htest
      obtain ⟨c'', k'', e'', hI'', hk'', h10, hA⟩ := regionBody_spec (P := P) hC hRd hrb hlb hcb hlen
        hent hrec hn hnW hTW h htest
      grind) hI
  rw [hnR c' hI'] at hex
  have hle := hI'.2.2.2.2.2.1
  refine ⟨c', k, he, hI', by_omega, by_omega, hΨ⟩
end region4
end
end Output
end Chazelle.Core
end
namespace Chazelle.Core
namespace Output
open Machine Machine.Stmt Programs
open OutWalk OutTrap OutNF
@[expose] public section
def initS : Stmt :=
  block [.inputSize 220000, .constN 220001 1, .constN 220002 0, .constN 220019 2,
    .constN 220020 3, .constN 220011 4, .constN 220012 5, .constN 220021 7,
    .subN 220017 220000 220001, .subN 220018 220017 220001, .constR 220000 0]

/-- The reversal flag: `1` iff the orientation (real register `100`) is negative. -/
def revS : Stmt := .ifLtR 100 220000 (.instr (.constN 220003 1)) (.instr (.constN 220003 0))

/-- The header of the normal form (handle in `coreReg 3`), the table base `T₀ = ALLOC`, the loop
registers and the hand-off registers. -/
def readS : Stmt :=
  block [.copyN 220004 230003, .addN 220117 220004 220019, .loadN 220005 220117,
    .addN 220117 220004 220020, .loadN 220006 220117, .addN 220117 220004 220012,
    .loadN 220007 220117, .addN 220117 220004 220021, .loadN 220008 220117,
    .copyN 220009 9999, .constN 220010 0, .copyN 220013 220007, .copyN 220016 220009,
    .copyN 9990 220009, .copyN 9991 220005, .copyN 9992 220009, .constN 9993 0]

/-- The preparation. -/
def prepS : Stmt := .seq initS (.seq revS readS)

/-- **The output program.** -/
def prog : Stmt := .seq Final.orientStmt (.seq prepS regionLoop)
section prep
variable {P : Polygon} {W : ℕ}

/-- Spec of the preparation: constants, the reversal flag from the orientation, the header of the normal form, the table base and the hand-off registers; cost `≤ 40`. -/
theorem prepS_spec {c : Config} (hc : WordsBounded W c) {σ : ℝ} {B T0 : ℕ}
    (hσ : c.rreg 100 = σ) (hB : c.nreg 230003 = B) (hT0 : c.nreg 9999 = T0) (hb : B + 7 ≤ W)
    (hn : P.n + 7 ≤ W) :
    ∃ c' k, Exec P W prepS c c' k ∧ k ≤ 40 ∧ ArithRegs c' (decide (σ < 0)) P.n ∧
      c'.nreg 220005 = c.nmem zthb ∧ c'.nreg 220006 = c.nmem ztkh ∧
      c'.nreg 220007 = c.nmem zter ∧ c'.nreg 220008 = c.nmem ztlw ∧
      c'.nreg 220009 = T0 ∧ c'.nreg 220011 = 4 ∧ c'.nreg 220012 = 5 ∧ c'.nreg 220019 = 2 ∧
      c'.nreg 220020 = 3 ∧ c'.nreg 220010 = 0 ∧ c'.nreg 220013 = c.nmem zter ∧
      c'.nreg 220016 = T0 ∧ c'.nreg 9990 = T0 ∧ c'.nreg 9991 = c.nmem zthb ∧
      c'.nreg 9992 = T0 ∧ c'.nreg 9993 = 0 ∧ c'.nreg 9999 = T0 ∧
      (∀ r, 240000 ≤ r → c'.nreg r = c.nreg r) ∧ (∀ r, 240000 ≤ r → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold prepS
  zujl
  zujqm
  exec_block
  all_goals try omega
  refine Final.spec_name fun c1 hc1 => ?_
  have hw1 : WordsBounded W c1 := by_simp_all
  have r1 : c1.rreg 100 = σ := by_simp_all
  have r0 : c1.rreg 220000 = 0 := by_simp_all
  have hA1 : ∀ bb : Bool, c1.nreg 220000 = P.n ∧ c1.nreg 220001 = 1 ∧ c1.nreg 220002 = 0 ∧
      c1.nreg 220017 = P.n - 1 ∧ c1.nreg 220018 = P.n - 2 ∧ c1.nreg 220019 = 2 ∧
      c1.nreg 220020 = 3 ∧ c1.nreg 220011 = 4 ∧ c1.nreg 220012 = 5 ∧ c1.nreg 220021 = 7 ∧
      c1.nreg 230003 = B ∧ c1.nreg 9999 = T0 := fun _ => by
    zvmwl; trivial
  obtain ⟨b0, b1, b2, b17, b18, b19, b20, b11, b12, b21, b3, b9999⟩ := hA1 true
  have fr1 : ∀ r, 240000 ≤ r → c1.nreg r = c.nreg r := fun r hr => by
    zuedc
  have rr1 : ∀ r, 240000 ≤ r → c1.rreg r = c.rreg r := fun r hr => by
    zuedc
  zucwx
  have rm1 : c1.rmem = c.rmem := by zvmwl
  have o1 : c1.output = c.output := by zvmwl
  -- the reversal flag
  have hrev : ∃ c2 k2, Exec P W revS c1 c2 k2 ∧ k2 ≤ 3 ∧
      c2 = { c1 with nreg := upd c1.nreg 220003 (decide (σ < 0)).toNat } := by
    unfold revS
    by_cases hneg : σ < 0
    · refine spec_ifLtR_true by_grind
        (spec_instr (Exec.constN hw1 220003 1 by_omega) fun _ => ?_)
      grind
    · refine spec_ifLtR_false by_grind
        (spec_instr (Exec.constN hw1 220003 0 by_omega) fun _ => ?_)
      grind
  obtain ⟨c2, k2, e2, hk2, rfl⟩ := hrev
  refine spec_seq ⟨_, k2, e2, ?_⟩
  unfold readS
  zump
  exec_block
  all_goals try (config_simp; simp only [b3, b19, b20, b12, b21]; omega)
  zubqj
  refine ⟨by_omega, ztcbl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  all_goals try (config_simp; simp only [b0, b1, b2, b17, b18, b19, b20, b11, b12, b21, b3, b9999, m1]; done)
  all_goals try (config_simp; done)
  · rw [← fr1 r hr]; simp (disch := omega) only [Machine.upd_other]
  · grind
  all_goals first | exact m1 | exact rm1 | exact o1
end prep
end
end Output
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Machine Machine.Stmt Programs
open OutWalk OutTrap OutNF Output

/-- **WP-N with the height hypothesis**: `OutputSpec` with the extra precondition that the chord
records of the normal form name their height vertex (`h < n`); see the module docstring. -/
def OutputSpecH : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s outBands
    (fun P W c => GoodEnv P ∧ P.n + 3 ≤ W ∧ c.output = [] ∧
      ∃ N, Robust ztm c.nmem (fun m => NFAt m (c.nreg ztvlv) N) ∧
        IsNF ztwiq zta N ∧
        N.F ztwiq zta = (interiorModel zta).Full ∧
        ∀ k, k < N.nChords → (N.chord k).h < P.n)
    (fun P _ c' => TablesReady zta c')
    ztwqk

/-- The reversal flag computed from the orientation. -/
theorem decide_orient_neg (Q : Polygon) : decide (Mountain.orient Q < 0) = revOf Q := by
  classical
  unfold Mountain.orient revOf
  by_cases h : Mountain.LeftInside Q <;> zumxk

/-- Entry `i` of the table of records of the regions. -/
theorem getD_trapTable {nR : ℕ} {f : ℕ → Final.TrapRec} {i : ℕ} (hi : i < nR) :
    ((List.range nR).map f).getD i ztcor = f i := by
  simp_all

/-- A register outside the output bands is at least `240000`. -/
theorem ge_of_band {r : ℕ} (h : bandOf r ∉ outBands) : 240000 ≤ r := by
  have h' : ¬ r / 10000 < 25 := fun h' => h (Finset.mem_range.2 h')
  omega

/-- **WP-N (proved, with the height hypothesis)**: the output program meets `OutputSpecH` with
the constant `κ = 700`. -/
theorem outputSpecH : OutputSpecH := by
  refine ⟨Output.prog, 700, ?_⟩
  intro P W c hw ⟨hge, hn3, hout, N, hRob, hNF, hfull, hhlt⟩ hroom
  have hQ : ztxw := (shearInvariance _ P).1 hge.1
  have hgs := goodShear_epsOf hge.2
  have hdh := hgs.2.1
  have hPQ : ShearRel P _ := shearRel_Qof hge.2
  zuc
  have hn3' := hge.1.1
  obtain ⟨reg, hcorr, hsides, -, hregs, -⟩ := hNF.2.2.2
  have H : RegCtx _ N reg :=
    ⟨hQ, hdh, hNF, hfull, by_simp_all, hcorr, hsides, hregs⟩
  have hT := table_ok H
  have hnR : N.nRegions ≤ 2 * P.n + 1 := by
    have := hT.length_le hQ
    rwa [List.length_map, List.length_range, hQn] at this
  zuhp
  have hc3 : coreReg 3 = 230003 := rfl
  zvnek at hroom hRob
  zvnar at hRob
  simp only at hroom
  set B := c.nreg 230003 with hBdef
  set T0 := c.nreg 9999 with hT0def
  have hRd := nfReads_of_robust hRob
  have hB2 := hRd.nr
  -- stage 1: the orientation
  obtain ⟨c1, k1, e1, hk1, hσ, fn1, fr1, m1, rm1, o1⟩ :=
    Final.orientStmt_exec (W := W) hPQ hQ c hw by_omega
  -- stage 2: the preparation
  obtain ⟨c2, k2, e2, hk2, hA2, v5, v6, v7, v8, v9, v11, v12, v19, v20, v10, v13, v16, v9990, v9991,
    v9992, v9993, v9999, fn2, fr2, m2, rm2, o2⟩ := prepS_spec (P := P) e1.wb_right hσ
      ztnth ztnth by_omega by_omega
  rw [decide_orient_neg] at hA2
  zvnmf at v5 v6 v7 v8 v13 v9991
  -- stage 3: the regions
  have hent := fun r hr t ht => by
    have hmem : (N.region r).chords.getD t 0 ∈ (N.region r).chords := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
      exact List.getElem_mem ht
    exact (((hregs r hr).1 _).1 hmem).1
  have hrec : ∀ k, k < N.nChords →
      (N.chord k).h < P.n ∧ (N.chord k).lp < P.n ∧ (N.chord k).rp < P.n := fun k hk => by
    obtain ⟨hl, hr, -⟩ := rec_attach hNF hk
    zubfo
  have hC : RegConsts c2 _ P.n N.nRegions (c.nmem ztkh) (c.nmem ztlw) T0 :=
    ⟨hA2, by rw [v5, hB2.1], v6, v8, v9, v11, v12, v19, v20⟩
  have hI0 : RegInv W (revOf zta) P.n N T0 (c.nmem zter) c.nmem c2 c2 :=
    ⟨e2.wb_right, by_omega, by_grind, rfl, rfl, by rw [v10]; exact Nat.zero_le _,
      by rw [v13, v10]; ring, by rw [v16, v10]; ring, by rw [v9999, v10]; ring,
      by grind, by_omega⟩
  obtain ⟨c3, k3, e3, hI3, h10, hk3, hΨ⟩ := regionLoop_spec (P := P) hC hRd rfl rfl rfl
    (fun r hr => chords_length_le H hr) hent hrec by_omega by_omega by_omega hI0 v10
  obtain ⟨hw3, hfr3, hrr3, hrm3, ho3, -, -, -, hal3, hmem3, hrecs3⟩ := hI3
  have eall : Exec P W Output.prog c c3 _ := e1.seq (e2.seq e3)
  refine ⟨c3, _, eall, ?_, ?_, ?_⟩
  · -- cost
    zulgl
    nlinarith
  · -- the tables
    refine ⟨_, [], hT, vtxChordTable_nil hQ hdh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show c3.nreg 9991 = _
      rw [hfr3 _ ztcuq, v9991, hB2.1, List.length_map, List.length_range]
    · show TrapTableAt c3.nmem (c3.nreg 9990) _
      rw [hfr3 _ ztcuq, v9990]
      zug
      rw [List.length_map, List.length_range] at hi
      rw [getD_trapTable hi, hQn]
      obtain ⟨t1, t2, t3, t4⟩ := hrecs3 i (by rw [h10]; exact hi)
      zubfo
    · show c3.nreg 9993 = _
      rw [hfr3 _ ztcuq, v9993]; rfl
    · intro i hi; exact by_grind
    · show c3.nreg 9990 + _ ≤ c3.nreg 9999
      rw [hfr3 _ ztcuq, v9990, hal3, h10, List.length_map, List.length_range]
    · show c3.nreg 9992 + 3 * 0 ≤ c3.nreg 9999
      rw [hfr3 _ ztcuq, v9992, hal3]; omega
    · rw [ho3, o2, o1, hout]
  · -- the frame
    refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a _ => ?_, ?_, ?_, ?_⟩
    · zullc
      rw [hfr3 _ ztcuq, fn2 _ hr', fn1 _ by_omega]
    · zullc
      rw [hrr3 _ ztcuq, fr2 _ hr', fr1 _ by_omega by_omega]
    · exact hmem3 a ha
    · rw [hrm3, rm2, rm1]
    · rw [ho3, o2, o1]
    · rw [hAL, hal3]; omega
    · zvnek; rw [v9999] at hΨ; omega

/-! ## Composition with the strengthened down phase -/

/-- `DownPhaseSpec` whose normal form also names the height vertex of each chord record. -/
def DownPhaseSpecH (X : MemCtx) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s phaseBands
    (fun P W c => GoodEnv P ∧ P.n + 3 ≤ W ∧
      Robust ztm c.nmem ztxwy ∧
      X.holds P c.nmem ztyim ztm ∧
      P.n - 1 ≤ X.cap P c.nmem ztyim ∧
      ∃ C N, TopChain P C ∧ Robust ztm c.nmem ztijq ∧
        IsCanonicalNF ztc zta N ztmow 4)
    (fun P _ c' => ∃ N, Robust ztdo c'.nmem (fun m => NFAt m (c'.nreg ztvlv) N) ∧
      IsNF ztwiq zta N ∧
      N.F ztwiq zta = (interiorModel zta).Full ∧
      ∀ k, k < N.nChords → (N.chord k).h < P.n)
    ztwqk

/-- **The core stage from the phases, with the height hypothesis** (the proof of
`core_of_phases`, with `DownPhaseSpecH` and `OutputSpecH`). -/
theorem core_of_phasesH (hS : SetupSpec) (hUD : ∃ X : MemCtx, UpPhaseSpec X ∧ DownPhaseSpecH X)
    (hO : OutputSpecH) (hgood : GoodShearExistsSpec) (hsh : ShearInvarianceSpec) :
    CoreStageSpec := by
  obtain ⟨⟨sS, κS, hS⟩, ⟨X, ⟨sU, κU, hU⟩, ⟨sD, κD, hD⟩⟩, ⟨sO, κO, hO⟩⟩ := And.intro hS
    (And.intro hUD hO)
  refine ⟨.seq sS (.seq sU (.seq sD sO)), κS + κU + κD + κO, κS + κU + κD + κO + 3, ?_⟩
  intro P hP W hW
  have hge : GoodEnv P := ⟨hP, hgood P hP⟩
  obtain ⟨bS, hbS⟩ : ∃ b, b = κS * (P.n + 1) := by_grind
  obtain ⟨bU, hbU⟩ : ∃ b, b = κU * (P.n + 1) := by_grind
  obtain ⟨bD, hbD⟩ : ∃ b, b = κD * (P.n + 1) := by_grind
  obtain ⟨bO, hbO⟩ : ∃ b, b = κO * (P.n + 1) := by_grind
  have hsum : (κS + κU + κD + κO + 3) * ztju = bS + bU + bD + bO + 3 * ztju := by
    grind
  have hC : (κS + κU + κD + κO) * ztju = bS + bU + bD + bO := by
    grind
  rw [hsum] at hW
  have hn3 : ztmd := by_omega
  have hw0 : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  have ha0 : initConfig.nreg ALLOC = 0 := rfl
  obtain ⟨c₁, k₁, e₁, hk₁, hq₁, hf₁⟩ := hS P W initConfig hw0 ⟨hge, hn3⟩
    (show initConfig.nreg ALLOC + κS * ztju ≤ W by rw [ha0, ← hbS]; omega)
  replace hk₁ : k₁ ≤ bS := by_grind
  have ha₁ : c₁.nreg ALLOC ≤ k₁ := by have := hf₁.2.2.2.2.2.2; omega
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨hkeep₂, hX₂, hcap₂, C, N, hC₂, hN₂, hcan₂⟩, hf₂⟩ :=
    hU P W c₁ e₁.wb_right ⟨hge, hn3, hq₁⟩
      (show c₁.nreg ALLOC + κU * ztju ≤ W by rw [← hbU]; omega)
  replace hk₂ : k₂ ≤ bU := by_grind
  have ha₂ := hf₂.2.2.2.2.2.2
  have hset₂ : Robust zthwb c₂.nmem
      (fun m => SetupAt m (c₂.nreg ztcpu) P.n zthwb) := by
    have h0 : c₂.nreg _ = c₁.nreg _ := hkeep₂ 0 by_simp
    zudty
    zucng
    have hq := (hq₁.frame hf₂) m hm
    exact ⟨hq.1, hq.2.1, hq.2.2.1, le_trans hq.2.2.2 hf₂.2.2.2.2.2.1⟩
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨N', hN₃, hnf₃, hfull₃, hh₃⟩, hf₃⟩ :=
    hD P W c₂ e₂.wb_right ⟨hge, hn3, hset₂, hX₂, hcap₂, C, N, hC₂, hN₂, hcan₂⟩
      (show c₂.nreg ALLOC + κD * ztju ≤ W by rw [← hbD]; omega)
  replace hk₃ : k₃ ≤ bD := by_grind
  have ha₃ := hf₃.2.2.2.2.2.2
  have hout₃ : c₃.output = [] := by
    rw [hf₃.2.2.2.2.1, hf₂.2.2.2.2.1, hf₁.2.2.2.2.1]; rfl
  obtain ⟨c₄, k₄, e₄, hk₄, hq₄, hf₄⟩ :=
    hO P W c₃ e₃.wb_right ⟨hge, hn3, hout₃, N', hN₃, hnf₃, hfull₃, hh₃⟩
      (show c₃.nreg ALLOC + κO * ztju ≤ W by rw [← hbO]; omega)
  replace hk₄ : k₄ ≤ bO := by_grind
  have ha₄ := hf₄.2.2.2.2.2.2
  refine ⟨c₄, k₁ + zttk, .seq e₁ ztcb, ?_, ?_,
    Qof P, shearRel_Qof (hgood P hP), (hsh _ P).1 hP, hq₄⟩
  · omega
  omega
end
end Chazelle.Core
namespace Chazelle.Core
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs
@[expose] public section
theorem whileLtN_potential_frame {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt} {B : Finset ℕ}
    (I : Config → Prop) (Φ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Frame B c c' k ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      Frame B c c' k ∧ k ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · obtain ⟨c₁, k₁, hb, hI₁, hF₁, hΦ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hF₂, hk₂⟩ := ih ztgnc by_omega hI₁ rfl
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht',
        (hF₁.trans hF₂).mono by_simp by_omega, by_omega⟩
    · exact ⟨c, 2, .whileLtN_false ht by_grind, hc, ht,
        ⟨by_omega, by_grind, by_omega, by_grind, rfl, le_rfl,
          by omega⟩, by_omega⟩

/-! ## The loop invariant -/

/-- **The invariant of the level loop**: the word bound, the environment, the level `λ ≤ p` in
register `0` of `bDownDrv` with `Inv(λ)`, the guard `g` and the constant `15`, and room for the
remaining budget `pot f λ` plus `Bb` (the base and the final copy). -/
def LoopI (X : MemCtx) (cnt : ℕ → ℕ) (n₀ : ℕ) (f : ℕ → ℕ) (Bb : ℕ) (P : Polygon) (W : ℕ)
    (c : Config) : Prop :=
  WordsBounded W c ∧ EnvD X P W c ∧ rd c bDownDrv 0 ≤ topGrade P.n ∧
    InvAt cnt P c ztxo ∧
    c.nreg 210007 = ztlqd ∧ c.nreg 210008 = 15 ∧
    c.nreg ALLOC + pot f ztxo + Bb ≤ W
variable (n : ℕ) {X : MemCtx}
theorem topGrade_le : topGrade n ≤ n := by
  zuhrf
  exact Nat.clog_le_of_le_pow ztkpf

/-- The setup record gives `λ ↦ ⌈λ/5⌉ + 11` for `λ ≤ p`. -/
theorem setup_next {m : ℕ → ℕ} {S n E lam : ℕ} (h : SetupAt m S n E) (hl : lam ≤ topGrade n) :
    m (S + topGrade n + 4 + lam) = Cost.ceilBeta lam := (h.2.2.1 lam by_omega).2

/-- `EnvD` in terms of the raw registers of `coreReg 0`. -/
theorem EnvD.setup {P : Polygon} {W : ℕ} {c : Config} (h : EnvD X P W c) :
    SetupAt c.nmem (c.nreg 230000) P.n ztm := h.2.2.2.1.holds

/-- **One iteration of the level loop.** -/
theorem levelBody_step (hX : X.CapLocal) {cnt : ℕ → ℕ} {n₀ : ℕ} {sL : Stmt}
    {κL : ℕ}
    (hL : Meets sL drvBands
      (fun P W c => EnvD X P W c ∧ n₀ ≤ P.n ∧ 16 ≤ rd c bDownDrv 0 ∧
        rd c bDownDrv 0 ≤ topGrade P.n ∧ InvAt cnt P c ztxo)
      (fun P c c' => rd c' bDownDrv 0 = rd c bDownDrv 0 ∧
        InvAt cnt P c' ztbail)
      (fun _ c => κL * ztbaoe))
    {Bb : ℕ} {P : Polygon} {W : ℕ} (hn₀ : n₀ + 15 ≤ W) {c : Config}
    (hI : LoopI X cnt n₀ ztxoi Bb P W c)
    (ht : c.nreg 210008 < c.nreg 210007) :
    ∃ c' k, Exec P W zttsf c c' k ∧
      LoopI X cnt n₀ ztxoi Bb P W c' ∧
      Frame drvBands c c' k ∧
      pot ztxoi (rd c' bDownDrv 0) + k + 2 ≤
        pot ztxoi ztxo := by
  obtain ⟨hw, hE, hlp, hInv, hg, h15, hroom⟩ := hI
  have hn₀n : n₀ ≤ P.n := by
    grind
  have h16 : 16 ≤ rd c bDownDrv 0 := by
    rw [ite_eq_left hn₀n] at hg; show 16 ≤ c.nreg 210000; omega
  have hpot := pot_of_le (f := lvlBudget ztcxh cnt ztcdz) h16
  -- the level
  have hK := InvAt.len_le hInv
  have hcost : κL * ztbaoe + 20 ≤
      lvlBudget ztcxh cnt ztcdz ztxo := by
    unfold lvlBudget kBound
    have h1 : ztcix * zthyq ≤
        (cnt ztxo * (2 ^ topGrade P.n + 2 ^ Cost.ceilBeta ztxo) /
            2 ^ Cost.ceilBeta ztxo + 1) *
          ztwqn := Nat.mul_le_mul_right _ by_omega
    have h2 : 1 ≤ ztcix * ztwqn :=
      by grind
    nlinarith
  have hpre : EnvD X P W c ∧ n₀ ≤ P.n ∧ 16 ≤ rd c bDownDrv 0 ∧ rd c bDownDrv 0 ≤ topGrade P.n ∧
      InvAt cnt P c _ := ⟨hE, hn₀n, h16, hlp, hInv⟩
  obtain ⟨c₁, k₁, e₁, hk₁, ⟨h0₁, hInv₁⟩, hF₁⟩ := hL P W c hw hpre (by
    grind)
  replace hk₁ : k₁ ≤ κL * (ztcix *
      ztwqn) := hk₁
  zuka
  zuivv
  zumcl
  zumbl
  -- `λ := ⌈λ/5⌉ + 11`
  have hl₁ := h0₁
  have hp₁ : c₁.nmem _ = topGrade P.n := hS₁.2.1
  have hnext := setup_next hS₁ hlp
  have hpn := topGrade_le P.n
  zumck
  have hS₁W : c₁.nreg 230000 + topGrade P.n + 4 + rd c bDownDrv 0 ≤ W := by_omega
  have hlt := Cost.ceilBeta_add_eleven_lt h16
  have hnW := hE.2.1
  obtain ⟨c₂, k₂, e₂, hk₂, hl₂, hr₂, hr₂', hm₂, hrr₂, hrm₂, ho₂⟩ :=
    lamNext_exec (P := P) c₁ hw₁ rfl hp₁ hl₁ hS₁W by_omega
  rw [hnext] at hl₂
  zuja
  -- the guard
  obtain ⟨c₃, k₃, e₃, hk₃, hg₃, h15₃, hr₃, hr₃', hl₃, hm₃, hrr₃, hrm₃, ho₃⟩ :=
    guardS_exec (P := P) n₀ c₂ hw₂ hn₀ by_omega
  zuboe
  -- frames
  zucgi

  have hsub : drvBands ∪ {bDownDrv} ∪ {bDownDrv} ⊆ drvBands := by
    decide
  have hF : Frame drvBands c c₃ _ := ((hF₁.trans hF₂).trans hF₃).mono hsub le_rfl
  have hlam₃ : rd c₃ bDownDrv 0 = nextLvl ztxo := by
    zunsg; rfl
  have hr13 : ∀ i, 1 ≤ i → i ≤ 5 → rd c₃ bDownDrv i = rd c₁ bDownDrv i := by
    intro i h1 h5
    zunfx
  zuffw

  have hInv₃ : ztsbr :=
    hInv₁.transport hr13 by_omega by_grind
  have hE₃ :=
    hE₁.frame hX ztvtd by_decide
  have hpotn := nextLvl_lt h16
  refine ⟨c₃, k₁ + zttl, Exec.seq e₁ ztnkw,
    ⟨hw₃, hE₃, ?_, ?_, ?_, h15₃, ?_⟩, by_grind, ?_⟩
  · omega
  · grind
  · grind
  · grind
  grind

/-- `2^p ≤ 2 n + 2` for `p = topGrade n`. -/
theorem two_pow_topGrade_le : 2 ^ topGrade n ≤ 2 * n + 2 := by
  zuhrf
  rcases Nat.lt_or_ge ztkl 2 with h | h
  · rw [Nat.clog_of_right_le_one by_simp_all, pow_zero]; omega
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) by_norm_num (show 1 < n - 1 by omega)
    have h2 : ztzom := Nat.clog_pos by_norm_num by_omega
    obtain ⟨q, hq⟩ : ∃ q, Nat.clog 2 (n - 1) = q + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h2).symm⟩
    zvnck at h1 ⊢
    zugwx
    simp only [Nat.pred_succ] at h1
    omega

/-- The word bound of the host procedures from the budget. -/
theorem hostWords_le {n κ : ℕ} (hκ : 272 ≤ κ) : hostWords n ≤ κ * ztkk := by
  unfold hostWords
  have := Nat.mul_le_mul_right ztkk hκ
  omega

/-- **The down phase from its components** (D1): the transition, one level and the base case,
with a bounded count function, give `DownPhaseSpecH X` for a context with a local capacity. -/
theorem downPhaseH_of_parts (hX : X.CapLocal) {cnt : ℕ → ℕ} {C n₀ : ℕ}
    (hc : ∀ l, cnt l ≤ C) (hT : TransSpec X cnt) (hL : LevelSpec X cnt n₀)
    (hB : BaseSpec X cnt n₀) : DownPhaseSpecH X := by
  obtain ⟨sT, κT, hT⟩ := hT
  obtain ⟨sL, κL, hL⟩ := hL
  obtain ⟨sB, κB, hB⟩ := hB
  refine ⟨downS sT sL sB n₀, κT + κB + 2 * potConst C ztcxh + n₀ + 300, ?_⟩
  zubgq
  obtain ⟨hG, hn3, hSet, hXh, hcap, hTop⟩ := hpre
  replace hroom : c.nreg ALLOC + (κT + κB + 2 * potConst C ztcxh + n₀ + 300) * ztju ≤ W :=
    hroom
  obtain ⟨κ, hκ⟩ : ∃ κ, κT + κB + 2 * potConst C (κL + 20) + n₀ + 300 = κ := by_grind
  rw [hκ] at hroom
  obtain ⟨f, hf⟩ : ∃ f, lvlBudget (κL + 20) cnt (topGrade P.n) = f := by_grind
  have hn1 : n₀ + 300 ≤ κ * ztju := by
    grind
  have hWh : ztuum := by
    have := hostWords_le (n := P.n) (show 272 ≤ κ by omega); omega
  have hE : EnvD X P W c := ⟨hG, hn3, hWh, hSet, hXh, hcap⟩
  have hpot : pot f _ ≤ potConst C _ * ztptt := hf ▸
    (pot_lvlBudget_le hc _ _ _ le_rfl).trans
      (Nat.mul_le_mul_left _ (two_pow_topGrade_le P.n))
  have hbud : κT * ztju + κB * ztju + 1 + pot f ztcdz + 13 ≤ κ * ztju := by
    have : potConst C ztcxh * ztptt = 2 * potConst C ztcxh * ztju := by_ring
    rw [← hκ]; nlinarith
  -- the transition
  obtain ⟨c₁, k₁, e₁, hk₁, hInv₁, hF₁⟩ := hT P W c hw ⟨hE, hTop⟩ (by
    grind)
  replace hk₁ : k₁ ≤ κT * ztju := hk₁
  zuka
  zuivv
  zumbl
  -- `λ := p` and the guard
  zumcl
  zumck
  obtain ⟨c₂, k₂, e₂, hk₂, hl₂, hr₂, hr₂', hm₂, hrr₂, hrm₂, ho₂⟩ :=
    lamP_exec (P := P) c₁ hw₁ rfl by_omega
  zuja
  rw [hS₁.2.1] at hl₂
  obtain ⟨c₃, k₃, e₃, hk₃, hg₃, h15₃, hr₃, hr₃', hl₃, hm₃, hrr₃, hrm₃, ho₃⟩ :=
    guardS_exec (P := P) n₀ c₂ hw₂ by_omega by_omega
  zuboe
  zucgi

  zuffw

  have hl3 : rd c₃ bDownDrv 0 = topGrade P.n := by zunsg
  have hInv₃ : ztsbr :=
    hInv₁.transport (fun i h1 h5 => by
      zunfx)
      by_omega by_grind
  have hE₃ := hE₁.frame hX ztvtd by_decide
  have hI₃ : LoopI X cnt n₀ f ztzhy P W c₃ := by
    refine ⟨hw₃, hE₃, by rw [hl3], by_grind, ?_, h15₃, ?_⟩
    · grind
    grind
  -- the level loop
  obtain ⟨c₄, k₄, e₄, hI₄, hx₄, hF₄, hk₄⟩ := whileLtN_potential_frame (P := P) (W := W)
    (a := 210008) (b := 210007) (body := levelBody sL n₀) (B := drvBands)
    (LoopI X cnt n₀ f ztzhy P W) (fun c => pot f ztxo)
    ztcvf
    (fun c h ht => hf ▸ levelBody_step hX hL (P := P) (W := W) by_omega (hf ▸ h) ht) hI₃
  rw [hl3] at hk₄
  obtain ⟨hw₄, hE₄, hlp₄, hInv₄, hg₄, h15₄, hroom₄⟩ := hI₄
  -- the base
  have hbase : 16 > rd c₄ bDownDrv 0 ∨ P.n < n₀ := by
    by_cases h : n₀ ≤ P.n
    · zvnbq at hg₄; left; show c₄.nreg 210000 < 16; omega
    omega
  obtain ⟨c₅, k₅, e₅, hk₅, ⟨N, hN, hNF, hFull⟩, hF₅⟩ := hB P W c₄ hw₄
    ⟨hE₄, rd c₄ bDownDrv 0, hlp₄, by_omega, hInv₄⟩ (by
      grind)
  replace hk₅ : k₅ ≤ κB * ztju := hk₅
  zudpp
  -- the final copy
  have e₆ := Exec.copyN (P := P) hw₅ 230003 210006
  refine ⟨_, k₁ + (zttl + ztzwt),
    Exec.seq e₁ (Exec.seq ztnkw (Exec.seq e₄ (Exec.seq e₅ e₆))), ?_, ?_, ?_⟩
  · show _ ≤ (κT + κB + 2 * potConst C _ + n₀ + 300) * ztju
    zukwq
  · refine ⟨N, ?_, hNF, hFull, fun k hk => ?_⟩
    · show Robust _ _ fun m => NFAt m ((upd c₅.nreg 230003 _) 230003) N
      zumls
      have hA : ztojd ALLOC = c₅.nreg ALLOC := by
        rfl
      show Robust (ztojd ALLOC) c₅.nmem _
      zvmze; exact hN
    · have := hNF.2.2.2.choose_spec.2.2.2.2.2.1 k hk
      zuic
  · have hF₆ : Frame {bCore} c₅ { c₅ with nreg := upd c₅.nreg 230003 (c₅.nreg 210006) } 1 :=
      frame_core (fun r hr => by rw [Config.nreg_mk, Machine.upd_other _ _ _ hr]) rfl rfl rfl rfl
    have h23 : (drvBands ∪ (({bDownDrv} : Finset ℕ) ∪ {bDownDrv} ∪ (drvBands ∪ (drvBands ∪ {bCore}))))
        ⊆ phaseBands := by
      zuh
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with hx | ((hx | hx) | hx | hx | hx)
      · zuley
      · zugeo
      · zugeo
      · zuley
      · zuley
      · zugeo
    exact (hF₁.trans ((hF₂.trans hF₃).trans (hF₄.trans (hF₅.trans hF₆)))).mono h23 le_rfl
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvP
@[expose] public section
open Set
open BuildRegions (famOf)
theorem chain_eq {C C' : Chain} (hP : C.P = C'.P) (hs : C.s = C'.s) (hm : C.m = C'.m) :
    C = C' := by
  cases C; simp_all
variable {P : Polygon}
/-- **A leaf is a box twin** of the chain of `Q` over the same vertices. -/
theorem twin_leaf {H : Host} {CQ CH : Chain} {a : ℕ} (hQ : CQ.P = Qof P)
    (hsQ : CQ.s = a) (hm : CQ.m = CH.m) (hCH : CH.P = H.poly zta)
    (hsm : CH.s + CH.m < (H.pts P.n).length) (han : a + CH.m < P.n)
    (hpt : ∀ k, k ≤ CH.m → pt H P.n (CH.s + k) = .vtx ztbzd) : BoxT.Twin CQ CH := by
  refine ⟨hm, fun k hk => ?_⟩
  rw [hchain_vertex_lt hCH by_omega, hpt k by_omega]
  show CQ.P.vtx ((CQ.s + k) % CQ.P.n) = _
  rw [hQ, hsQ, qof_n, Nat.mod_eq_of_lt by_omega]
  rfl

/-- **The transported list of a leaf.** -/
theorem leaf_list {CQ CH : Chain} {N₀ : NF} {γ' : ℕ} (hG : GoodEnv P)
    (hQ : CQ.P = Qof P) (hT : BoxT.Twin CQ CH) (hP' : CH.P.Simple)
    (hN₀ : IsCanonicalNF ztmhi zta N₀ γ' 4) :
    ChordTriplesOK ztcpt zta ztdkt ∧
      (chainModel CH).DegLe
        ztxod 4 ∧
      (chainModel CH).Semigranular
        ztxod (2 * γ') := by
  have hP : CQ.P.Simple := by zvnao; exact (shearInvariance ztbhs P).1 hG.1
  obtain ⟨hNF, hdeg, hgran, -⟩ := hN₀
  exact BoxT.boxTransport_nf hT hP hP' hNF hdeg hgran.semigranular

/-- **The empty list of a connector.** -/
theorem conn_list {CH : Chain} {γ : ℕ} (hP' : CH.P.Simple) (h2m : 2 * CH.m ≤ γ) :
    ChordTriplesOK ztcpt zta [] ∧
      (chainModel CH).DegLe ztzer 4 ∧
      (chainModel CH).Semigranular ztzer γ := by
  have he : famOf ztcpt zta [] = ∅ := by
    zuiua
  have hM := walkAx_chainModel hP'
  refine ⟨⟨ztcg, by_simp, by_simp, by_simp⟩, ?_, ?_⟩
  · simp
  · simp
  · simp
  · zvmxm; intro U _
    zuhqm
    simp
  · zvmxm; intro U hU
    rw [Gran.weight_empty hM hU, DownMath.chainModel_size]
    omega
theorem isDecomp_mono {N : NF} {d d' : ℕ} (h : IsDecomp N d) (hd : d ≤ d') : IsDecomp N d' := by
  zucbi
  refine ⟨h1, h2, h3, h4, h5, h6, fun x hx => ?_, h8, h9, h10⟩
  obtain ⟨j, hj, e⟩ := h7 x hx
  exact ⟨j, hj.trans hd, e⟩

/-- **A canonical normal form of cap `4` has every cap `D ≥ 4`.** -/
theorem canonical_cap {M : Model} {Q : Polygon} {N : NF} {γ D : ℕ}
    (h : IsCanonicalNF M Q N γ 4) (hD : 4 ≤ D) : IsCanonicalNF M Q N γ D := by
  zucdw
  refine ⟨h1, Model.DegLe.mono M h2 hD, h3, isDecomp_mono h4 ?_⟩
  unfold decDepth
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hD) 1
theorem semigranular_mono {M : Model} {F : Set ztf} {γ γ' : ℕ} (h : M.Semigranular F γ)
    (hγ : γ ≤ γ') : M.Semigranular F γ' := fun U hU => (h U hU).trans hγ
theorem lemma41Nat_mono {g g' : ℕ} (h : g ≤ g') : lemma41Nat g ≤ lemma41Nat g' := by
  unfold lemma41Nat
  apply Nat.ceil_mono
  have h1 : (g : ℝ) ≤ g' := by_simp_all
  have h2 : ((Nat.clog 2 g : ℕ) : ℝ) ≤ (Nat.clog 2 g' : ℕ) := by
    exact_mod_cast Nat.clog_mono_right 2 h
  have h3 : (2 : ℝ) ^ ztme ≤ (2 : ℝ) ^ ztlci :=
    Real.rpow_le_rpow_of_exponent_le by_norm_num by_nlinarith
  have h0 : ztcrf := Nat.cast_nonneg g
  zueqw
  have hp : ztxst := Real.rpow_pos_of_pos by_norm_num _
  have hg2 : (g : ℝ) ^ 2 ≤ (g' : ℝ) ^ 2 := by_nlinarith
  calc (g : ℝ) ^ 2 * zttu * (2 : ℝ) ^ ztme
      ≤ (g' : ℝ) ^ 2 * ztlcl * (2 : ℝ) ^ ztme := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        exact mul_le_mul hg2 by_linarith by_linarith by_positivity
    _ ≤ (g' : ℝ) ^ 2 * ztlcl * (2 : ℝ) ^ ztlci :=
        mul_le_mul_of_nonneg_left h3 by_positivity
variable (g : ℕ)
/-- The real bound below `lemma41Nat`. -/
theorem real_le_lemma41Nat :
    (g : ℝ) ^ 2 * zttu * (2 : ℝ) ^ ztme ≤ lemma41Nat g :=
  Nat.le_ceil _
theorem le_lemma41Nat : g ≤ lemma41Nat g := by
  zuevb
  · omega
  have h := real_le_lemma41Nat g
  have h1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ztme :=
    Real.one_le_rpow by_norm_num by_positivity
  have h3 : ztcre := Nat.cast_nonneg _
  have : (g : ℝ) ≤ (lemma41Nat g : ℝ) := by
    calc (g : ℝ) ≤ (g : ℝ) ^ 2 * zttu * 1 := by_nlinarith
      _ ≤ _ := by
        apply le_trans _ h
        exact mul_le_mul_of_nonneg_left h2 by_positivity
  simp_all
theorem kcost_mono {K K' : ℕ} (h : K ≤ K') :
    K * ztho ≤ K' * ztqao :=
  Nat.mul_le_mul h (Nat.add_le_add_right zttas 1)

/-- **The size of a grade-`g` normal form against Lemma 4.1's bound.** -/
theorem kcost_le {g K : ℕ} (hg : 1 ≤ g) (hK : K * 2 ^ Cost.ceilBeta g ≤ 2520 * 2 ^ g) :
    K * ztho ≤ 35280 * lemma41Nat g := by
  set cb := Cost.ceilBeta g with hcb
  have hcbg : cb ≤ g := Cost.ceilBeta_le g
  set e := g - cb with he
  have hpow : 2 ^ g = 2 ^ e * 2 ^ cb := by zunvh; simp_all
  have hKe : K ≤ 2520 * 2 ^ e := by
    rw [hpow, ← Nat.mul_assoc] at hK
    simp_all
  have hlog : Nat.clog 2 K ≤ 12 + e := by
    zudwq
    grind
  have h1 : K * ztho ≤ 2520 * 2 ^ e * ztned :=
    Nat.mul_le_mul hKe by_omega
  -- the real comparison
  have hcbr : (g : ℝ) / 5 ≤ (cb : ℝ) := by
    have := Nat.le_ceil ztnkh
    zukoz
    rw [hcb]; unfold Cost.ceilBeta; rw [Cost.beta_eq]; linarith
  have her : (e : ℝ) ≤ (74 : ℝ) / 75 * g := by
    rw [he, Nat.cast_sub hcbg]
    grind
  have h2e : ((2 ^ e : ℕ) : ℝ) ≤ (2 : ℝ) ^ ztme := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    simp_all
  zukcd
  have hge : (e : ℝ) ≤ g := by_simp_all
  have h13 : ((13 + e : ℕ) : ℝ) ≤ 14 * (g : ℝ) ^ 2 * zttu := by
    push_cast
    zueqw
    nlinarith
  have hreal := real_le_lemma41Nat g
  have hp : (0 : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : ((2520 * 2 ^ e * ztned : ℕ) : ℝ) ≤ ((35280 * lemma41Nat g : ℕ) : ℝ) := by
    push_cast
    zueqw
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ ztme := by_positivity
    calc (2520 : ℝ) * 2 ^ e * ztned
        = 2520 * ((2 ^ e : ℕ) : ℝ) * ((13 + e : ℕ) : ℝ) := by_simp
      _ ≤ 2520 * (2 : ℝ) ^ ztme *
          (14 * (g : ℝ) ^ 2 * zttu) := by
        apply mul_le_mul by_linarith h13 by_positivity by_positivity
      _ = 35280 * ((g : ℝ) ^ 2 * zttu *
          (2 : ℝ) ^ ztme) := by_ring
      _ ≤ 35280 * (lemma41Nat g : ℝ) := by_linarith
  have := (Nat.cast_le (α := ℝ)).1 key
  omega
end
end DrvP
end Chazelle.Core
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs
@[expose] public section
def L41M (O : OracleIface) (s : Stmt) (κ : ℕ) : Prop :=
  Meets s l41Bands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem ztbdk ztm ∧
      rd c bL41 3 ≤ c.nmem ztbdk ∧ lemma41Start ≤ rd c bL41 3 ∧
      rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
      2 ^ ztbwz < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
    (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
      Robust ztdo c'.nmem ztwr ∧
      IsCanonicalNF ztc zta N ztbqg 4)
    ztgit
theorem lemma41Spec_iff (O : OracleIface) : Lemma41Spec O ↔ ∃ s κ, L41M O s κ := Iff.rfl

/-- The judgement of `BruteSpec`. -/
def BruteM (s : Stmt) (κ : ℕ) : Prop :=
  Meets s bruteBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
      rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
      ztuu)
    (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
      Robust ztdo c'.nmem ztwq ∧
      IsCanonicalNF ztc zta N ztczy 4)
    ztgrj
theorem bruteSpec_iff : BruteSpec ↔ ∃ s κ, BruteM s κ := Iff.rfl

/-- The judgement of `BuildNFSpec`. -/
def BuildM (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P ztm c.nmem ztue ∧
      ∃ M L, ModelDescAt c.nmem ztue zta M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem ztbis L ∧ ChordTriplesOK M zta L)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem ztue zta M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem ztbis L →
        ∃ N, c.nreg ALLOC ≤ rd c' bBuild 3 ∧ NFWithin c'.nmem ztdph ztdo N ∧
          IsNF M zta N ∧ N.chords.map ztwma = L ∧ N.dec = [])
    ztzj
theorem buildNFSpec_iff : BuildNFSpec ↔ ∃ s κ, BuildM s κ := Iff.rfl

/-- The judgement of `GranularizeSpec`. -/
def GranM (s : Stmt) (κ : ℕ → ℕ) : Prop :=
  Meets s granBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
      ModelDescWF P ztm c.nmem ztqa ∧
      ∃ M N, ModelDescAt c.nmem ztqa zta M ∧ GoodModel M ∧
        NFWithin c.nmem ztbdi ztm N ∧ IsNF M zta N ∧
        M.DegLe ztwiv ztqb ∧
        M.Semigranular ztwiv ztbdj)
    (fun P c c' => ∀ M N, ModelDescAt c.nmem ztqa zta M → NFAt c.nmem ztbdi N →
      ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem ztcoh ztdo N' ∧
        N'.F M zta ⊆ N.F M zta ∧
        IsCanonicalNF M zta N' ztbdj ztqb)
    (fun _ c => κ ztqb *
      ztin)
theorem granularizeSpec_iff : GranularizeSpec ↔ ∃ s κ, GranM s κ := Iff.rfl

/-! ## The program -/

/-- The empty list of a connector. -/
def connS : Stmt := block [.constN 218016 0, .constN 218017 0]

/-- `218019 := ⌈log₂ m⌉` (`218023 = 2^218019`). -/
def clogS : Stmt := .seq ztkrc
  (.whileLtN 218023 218002 ztiqp)

/-- Lemma 4.1 on the leaf, at grade `⌈log₂ m⌉`. -/
def l41Call (sL : Stmt) : Stmt := .seq clogS (.seq (block [.copyN 160000 218008,
  .copyN 160001 218004, .copyN 160002 218002, .copyN 160003 218019])
  (.seq sL (block [.copyN 218015 160004])))

/-- Brute force on the leaf (`γ' = 1` for one edge, else `2`). -/
def bruteCall (sB : Stmt) : Stmt :=
  .seq ztfmf
    (.seq ztkrw
      (.seq sB (block [.copyN 218015 180003])))

/-- The normal form of a leaf, then its wall filter. -/
def leafS (sL sB : Stmt) : Stmt := .seq ztyzz dropS

/-- The chord list of a piece. -/
def listS (sL sB : Stmt) : Stmt := .ifLtN 218003 218021 connS (leafS sL sB)

/-- The build of the normal form from the list. -/
def buildS (sBd : Stmt) : Stmt := .seq (block [.copyN 40000 218010, .copyN 40001 218016,
  .copyN 40002 218017]) (.seq sBd (block [.copyN 218018 40003]))

/-- The granularity enforcement (cap `4`, target `γ`). -/
def granS (sG : Stmt) : Stmt := .seq (block [.copyN 90000 218010, .copyN 90001 218018,
  .constN 90002 4, .copyN 90003 218007]) (.seq sG (block [.copyN 218011 90004]))

/-- The top offset. -/
def topS : Stmt := .ifLtN 218002 218022 scanS gTop

/-- The descriptor part: count, top, bit, descriptor. -/
def frontS : Stmt := .seq cntS (.seq topS (.seq betaS descS))

/-- **The procedure of a piece.** -/
def pieceS (sL sB sBd sG : Stmt) : Stmt :=
  .seq frontS (.seq zttsj (.seq ztvfx ztvrl))

/-! ## The grade loop -/
section exec
variable {P : Polygon} {W : ℕ}

/-- **The grade** `⌈log₂ m⌉`. -/
theorem clogS_exec (c : Config) (hw : WordsBounded W c) {m : ℕ} (h02 : c.nreg 218002 = m)
    (hm : 1 ≤ m) (h21 : c.nreg 218021 = 1) (hmW : 2 * m ≤ W) :
    ∃ c' k, Exec P W clogS c c' k ∧ k ≤ 4 * Nat.clog 2 m + 4 ∧
      c'.nreg 218019 = Nat.clog 2 m ∧
      (∀ r, r ≠ 218019 → r ≠ 218023 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v19, v23, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      ztkrc c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 218019 = 0 ∧
      c₁.nreg 218023 = 1 ∧ (∀ r, r ≠ 218019 → r ≠ 218023 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals first | omega | skip
    simp_all
  let I : Config → Prop := fun d => WordsBounded W d ∧ d.nreg 218023 = 2 ^ d.nreg 218019 ∧
    (1 ≤ d.nreg 218019 → 2 ^ (d.nreg 218019 - 1) < m) ∧
    (∀ r, r ≠ 218019 → r ≠ 218023 → d.nreg r = c.nreg r) ∧ d.nmem = c.nmem ∧
    d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  have hI₁ : ztkzz := ⟨e₁.wb_right, by_simp_all, by_omega, r₁, m₁⟩
  obtain ⟨c₂, k₂, e₂, ⟨w₂, p₂, l₂, r₂, m₂, rr₂, rm₂, o₂⟩, hx₂, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (W := W) (a := 218023) (b := 218002)
    (body := block [.addN 218023 218023 218023, .addN 218019 218019 218021]) I
    (fun d => Nat.clog 2 m - d.nreg 218019) 2 ztoe (fun d ⟨wd, pd, ld, rd', md, rrd, rmd, od⟩ ht => by
      have h2 : d.nreg 218002 = m := by_simp_all
      have h21' : d.nreg 218021 = 1 := by_simp_all
      zvmxx at ht
      have hw := wd
      obtain ⟨d', k, e, hk, v23', v19', r', m'⟩ : ∃ d' k, Exec P W
          ztiqp d d' k ∧ k = 2 ∧
          d'.nreg 218023 = 2 * d.nreg 218023 ∧ d'.nreg 218019 = d.nreg 218019 + 1 ∧
          (∀ r, r ≠ 218019 → r ≠ 218023 → d'.nreg r = d.nreg r) ∧
          (d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output) := by
        exec_block
        · grind
        · config_simp; rw [h21']
          have : d.nreg 218019 < 2 ^ d.nreg 218019 := Nat.lt_two_pow_self
          omega
        refine ⟨rfl, by config_simp; ring, by_simp_all, fun r h1 h2 => ?_,
          rfl, rfl, rfl, rfl⟩
        simp_all
      obtain ⟨m'', rr'', rm'', o''⟩ := m'
      refine ⟨d', k, e, ⟨e.wb_right, ?_, ?_, fun r h1 h2 => (r' r h1 h2).trans (rd' r h1 h2),
        m''.trans md, rr''.trans rrd, rm''.trans rmd, o''.trans od⟩, by_omega, ?_⟩
      · grind
      · simp_all
      · rw [v19']
        rw [pd] at ht
        have : d.nreg 218019 < Nat.clog 2 m := by
          zux

          zuhwc
          have h4 : 2 ^ Nat.clog 2 m ≤ 2 ^ d.nreg 218019 := Nat.pow_le_pow_right by_norm_num hc
          omega
        omega) hI₁
  have h2 : c₂.nreg 218002 = m := by_simp_all
  rw [h2, p₂] at hx₂
  have hg : c₂.nreg 218019 = Nat.clog 2 m := by
    zudmc
    · zube

      have := l₂ by_omega
      zuhwc
      have h4 : 2 ^ Nat.clog 2 m ≤ 2 ^ (c₂.nreg 218019 - 1) :=
        Nat.pow_le_pow_right by_norm_num by_omega
      omega
    · exact Nat.clog_le_of_le_pow by_omega
  have hk₂' : k₂ ≤ 4 * Nat.clog 2 m + 2 := by
    omega
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by_omega, hg, r₂, m₂, rr₂, rm₂, o₂⟩
end exec
end
end DrvP
end Chazelle.Core
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs NFLoc SignK WalkKey
@[expose] public section
def Btp (r : ℕ) : Bool :=
  decide ztgze || Bk r || decide ztgxw ||
    decide zttxr || decide (218030 ≤ r ∧ r < 218050)

/-- The registers written by the count, the top and the bit. -/
def Ball (r : ℕ) : Bool := Bsc r || Btp r || Bbit r
variable {r : ℕ}
theorem bscan_btp (h : Bscan r = true) : Btp r = true := by
  simp only [Bscan, Btp, Bhost, Bk, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega
theorem bg_btp (h : Bg r = true) : Btp r = true := by
  simp only [Bg, Btp, Bk, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢; omega
theorem frameB_mono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' := by
  refine ⟨fun r hr => h.1 r ?_, fun r hr => h.2.1 r ?_, h.2.2⟩
  · grind
  grind
theorem ball_band (h : Ball r = true) : bandOf r ∈ DrvR.drvBands := by
  simp only [Ball, Bsc, Btp, Bbit, Bk, Bool.or_eq_true, decide_eq_true_eq] at h
  zunsb; unfold bandOf; omega
theorem ball_false (h1 : r < 10000 ∨ 10500 ≤ r) (h2 : r < 50046 ∨ 50080 ≤ r)
    (h3 : r < 170000 ∨ 170100 ≤ r) (h4 : r < 218012 ∨ 218100 ≤ r) : Ball r = false := by
  simp only [Ball, Bsc, Btp, Bbit, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The descriptor part of a piece.** -/
theorem frontS_exec {O : OracleIface} (c : Config) (hw : WordsBounded W c)
    (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hgr : (gradeCtx O).holds P c.nmem ztcuu ztm)
    (hm1 : 1 ≤ c.nreg 218002) {H : Host}
    (hH : Robust ztm c.nmem ztfbw)
    (hHA : c.nreg 218000 + 3 * H.length + 4 ≤ c.nreg ALLOC) (hl : H.length ≤ 64)
    (hwf : HostWF (Qof P).n H)
    (hsm : c.nreg 218001 + c.nreg 218002 + 1 ≤ (H.pts (Qof P).n).length)
    (hleaf : ¬ c.nreg 218002 < 65 → c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧
      c.nreg 218005 ≤ c.nmem ztcuu ∧ c.nreg 218004 + c.nreg 218002 + 1 ≤ (Qof P).n ∧
      ∀ k, k ≤ c.nreg 218002 →
        (H.pts (Qof P).n).getD zthuq ztga = .vtx zthur)
    (hroom : c.nreg ALLOC + 1204 * c.nreg 218005 + 140000 ≤ W)
    (CH : Chain) (hCH : CH.P = H.poly zta) (hCs : CH.s = c.nreg 218001)
    (hCm : CH.m = c.nreg 218002) :
    ∃ c' k, Exec P W frontS c c' k ∧ k ≤ 1204 * c.nreg 218005 + 140000 ∧
      Frame DrvR.drvBands c c' k ∧
      c'.nreg 218010 = c.nreg ALLOC ∧ c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      (∀ r, 218000 ≤ r → r < 218010 → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 218000 ∨ 219000 ≤ r) → ztcu → (r < 50046 ∨ 50080 ≤ r) →
        ztcau → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nreg 218020 = 0 ∧ c'.nreg 218021 = 1 ∧ c'.nreg 218022 = 65 ∧
      zth ∧
      c'.nmem ztm = 0 ∧ c'.nmem ztccv = c.nreg 218000 ∧
      c'.nmem zteep = CH.s ∧ c'.nmem zteeq = CH.m ∧
      c'.nmem ztllf = CH.topIdx ∧
      (c'.nmem ztllg = 1 ↔ CH.sideBeta = true) := by
  have hn := qof_n P
  zvmxq at hwf hsm hleaf
  zuixh
  zudwh
  zuhea
  obtain ⟨HB, hHB⟩ : ∃ HB, c.nreg 218000 = HB := by_simp_all
  zuctb

  zugrc
  rw [hHB] at hH hHA ⊢
  zvmyz at hsm hleaf hCs
  zvmwi at hm1 hsm hleaf hCm
  zuikt
  have E : ScE P W H c.nmem HB := ⟨hG, hW, hH.holds, hwf, hl, by_omega⟩
  -- 1. the count
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, v12, v20, v21, v22, E₁⟩ := cntS_exec (P := P) c hw (H := H)
    (by rw [hHB]; exact hH.holds) by_omega E.hN by_omega
  rw [hHB] at E₁
  have k₁' := F₁.1
  have g₁ : ∀ r, 218000 ≤ r → r < 218012 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    k₁' r (by simp only [Bsc, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  zud
  -- 2. the top
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, E₂, hT, hTm⟩ : ∃ c₂ k₂, Exec P W topS c₁ c₂ k₂ ∧
      k₂ ≤ 1204 * μ + 129240 ∧ FrameB Btp c₁ c₂ ∧ HostEnv W HB H.length c.nmem c₂ ∧
      c₂.nreg 218013 = CH.topIdx ∧ c₂.nreg 218013 ≤ m := by
    unfold topS
    by_cases h64 : c₁.nreg 218002 < c₁.nreg 218022
    · have hm64 : m < 65 := by
        simp_all
      refine spec_ifLtN_true h64 ?_
      have a01 : c₁.nreg 218001 = s := by_simp_all
      have a02 : ztuqf := by_simp_all
      obtain ⟨c₂, k₂, e₂, hk₂, F₂, E₂, hT, hle, hlt⟩ := scanS_exec E c₁ E₁ v20 v21
        by_omega
      rw [a01, a02] at hle
      rw [a01] at hlt
      rw [a02] at hk₂ hT
      refine ⟨c₂, k₂, e₂, by_omega, frameB_mono F₂ (fun r hr => bscan_btp hr), E₂, ?_, hT⟩
      exact (hchain_topIdx hCH by_omega by_omega
        by_simp_all by_simp_all).symm
    · have hm64 : ¬ m < 65 := by
        simp_all
      refine spec_ifLtN_false h64 ?_
      obtain ⟨hμm, hμΛ, ham, hpts⟩ := hleaf hm64
      have hμ1 : 1 ≤ μ := by
        grind
      obtain ⟨c₂, k₂, e₂, hk₂, F₂, hT, hle⟩ := gTop_exec
        (s := ⟨c.nreg ALLOC, c.nmem, c.nreg 218008⟩) c₁ w₁ hG hW
        ztdnp ztnsw hgr
        by_simp_all hμ1
        by_simp_all hμΛ
        by_simp_all
      rw [g₁ 218002 by_norm_num by_norm_num, hm] at hT hle
      rw [g₁ 218004 by_norm_num by_norm_num] at hle
      have hg := F₂.1
      have E₂ : HostEnv W HB H.length c.nmem c₂ := by
        have g : ∀ r, 50060 ≤ r → r < 50070 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
          hg r (by simp only [Bg, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
            beq_eq_false_iff_ne]; omega)
        exact ⟨e₂.wb_right, by zumwu; exact E₁.h60,
          by zumwu; exact E₁.h61,
          by zumwu; exact E₁.h67,
          by zumwu; exact E₁.h68,
          by zumwu; exact E₁.h69, by rw [F₂.2.2.1]; exact E₁.mem⟩
      refine ⟨c₂, k₂, e₂, by_omega, frameB_mono F₂ (fun r hr => bg_btp hr), E₂, ?_, hT⟩
      zudyf
      refine (hchain_topIdx_leaf hCH by_omega hD (a := c.nreg 218004)
        by_omega ztjwb by_omega by_grind).symm
      rw [hCs]; unfold pt; grind
  zue
  have g₂ : ∀ r, 218000 ≤ r → r < 218013 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂.1 r zthtw
  have g₂' : ∀ r, 218020 ≤ r → r < 218023 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂.1 r zthtw
  -- 3. the bit
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b₃, hb₃⟩ := betaS_exec E c₂ E₂
    by_simp_all
    by_simp_all
    by_simp_all
    by_grind
  rw [g₂ 218001 by_norm_num by_norm_num, g₁ 218001 by_norm_num by_norm_num, hs, hT] at hb₃
  zubj
  have g₃ : ∀ r, 218000 ≤ r → r < 218014 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    F₃.1 r zthtv
  have g₃' : ∀ r, 218020 ≤ r → r < 218023 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    F₃.1 r zthtv
  have hβ : (c₃.nreg 218014 = 1 ↔ CH.sideBeta = true) := by
    rw [hb₃]
    rcases Nat.eq_zero_or_pos CH.topIdx with h0 | h0
    · rw [Brute.sideBeta_of_top_zero h0, h0]; simp
    · rw [hchain_beta hCH h0 by_omega,
        hCs]
      grind
  -- 4. the descriptor
  have c₃20 : c₃.nreg 218020 = 0 := by
    rw [g₃' _ by_norm_num by_norm_num, g₂' _ by_norm_num by_norm_num, v20]
  have c₃21 : c₃.nreg 218021 = 1 := by
    rw [g₃' _ by_norm_num by_norm_num, g₂' _ by_norm_num by_norm_num, v21]
  have c₃22 : c₃.nreg 218022 = 65 := by
    rw [g₃' _ by_norm_num by_norm_num, g₂' _ by_norm_num by_norm_num, v22]
  have F₁₃ : FrameB Ball c c₃ :=
    (frameB_mono F₁ ztesp).trans
      ((frameB_mono F₂ ztesp).trans
        (frameB_mono F₃ ztesp))
  have hA₃ : ztcke := F₁₃.1 _ by_decide
  obtain ⟨c₄, k₄, e₄, hk₄, v10, v99, r₄, rr₄, rm₄, o₄, ml₄, d0, d1, d2, d3, d4, d5⟩ :=
    descS_exec (P := P) c₃ w₃ c₃20 c₃21 by_omega
  rw [hA₃] at v10 v99 ml₄ d0 d1 d2 d3 d4 d5
  have ex : Exec P W frontS c c₄ _ := .seq e₁ ztcb
  have gin : ∀ r, 218000 ≤ r → r < 218010 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [g₃ r h1 by_omega, g₂ r h1 by_omega, g₁ r h1 by_omega]
  refine ⟨c₄, _, ex, by_omega, ?_, v10, v99, fun r h1 h2 => ?_, fun r h1 h2 h3 h4 h5 => ?_, ?_,
    ?_, ?_, fun a ha => ?_, d0, ?_, ?_, ?_, ?_, ?_⟩
  · -- the frame
    have G₁ : Frame DrvR.drvBands c c₃ ztxee :=
      DrvT.frame_drv ⟨F₁₃.1, F₁₃.2.1, F₁₃.2.2.2.1, F₁₃.2.2.2.2⟩ (fun r hr => ball_band hr)
        by_decide (fun a _ => by rw [F₁₃.2.2.1])
    have G₂ : ztsbi := by
      have ml₄' : ∀ a, a < c₃.nreg ALLOC → c₄.nmem a = c₃.nmem a := fun a ha =>
        ml₄ a by_omega
      refine ⟨fun r hr hra => ?_, by_grind, ml₄', by_grind, o₄,
        by omega, by_omega⟩
      refine r₄ r ?_ ?_ hra
      · zukog
      · zukog
    exact G₁.trans G₂ |>.mono by_simp by_omega
  · rw [r₄ r by_omega by_omega ztu, gin r h1 h2]
  · rw [r₄ r by_omega by_omega h5, F₁₃.1 r (ball_false h2 h3 h4 by_omega)]
  · zudao
  · zudao
  · zudao
  · rw [ml₄ a ha, F₁₃.2.2.1]
  · rw [d1, gin _ by_norm_num by_norm_num, hHB]
  · rw [d2, gin _ by_norm_num by_norm_num, hs, hCs]
  · rw [d3, gin _ by_norm_num by_norm_num, hm, hCm]
  · rw [d4, g₃ _ by_norm_num by_norm_num, hT]
  · rw [d5]; exact hβ
end exec
end
end DrvP
public section
theorem restoreSpec : RestoreSpec := restoreSpec_of_find buildNFOK Restore.findSpec

/-- **The merge (Lemma 3.5) from the sweep.** -/
theorem mergeSpec_of_sweep (hS : SweepSpecH) : MergeSpec :=
  MergeAsm.mergeSpec_of (FuseAsm.fuseSpec_of hS buildNFOK) restoreSpec (Gran.granularize' buildNFOK)

/-- **The up phase from the sweep**, for every valid oracle interface. -/
theorem upPhase_of_sweep (hS : SweepSpecH) {O : OracleIface} (hV : O.Valid) :
    UpPhaseSpec ztsy :=
  Up.upPhase_of' ztvza hV ztjmv brute

/-- **Reduction of the main theorem** to the sweep (WP-D) and the down phase (WP-M). -/
theorem linear_of_sweep_down (hS : SweepSpecH)
    (hD : ∀ O : OracleIface, O.Valid → DownPhaseSpecH ztsy) :
    LinearTimeTriangulation := by
  obtain ⟨O, hV⟩ := oracleSpec
  exact linear_of_core
    (core_of_phasesH setupSpec ⟨gradeCtx O, upPhase_of_sweep hS hV, hD O hV⟩ outputSpecH
      goodShearExists shearInvariance)
    Chazelle.Final.finalStage shearInvariance
end
end Chazelle.Core
section
set_option hygiene false
local macro "zqblu" : tactic => `(tactic| (have hT := htwin CQ hCQ hCs hCm
                                           obtain ⟨hok, hdeg, hwt⟩ := leaf_list hG hCQ hT hCHs hcan
                                           have hK := k0_count by_simp_all hcan
                                           rw [hCm] at hK))
local macro "zqblv" : tactic => `(tactic| exact ⟨c₁, _, ex, by_omega, by_omega, r, exec_frameB ex by_decide⟩)
local macro "zqblw" : tactic => `(tactic| obtain ⟨μ, hμ⟩ : ztjbx := by_simp_all)
set_option hygiene true

/-!
# Down-phase pieces (D4), part 11: the normal form of a leaf and the chord list of a piece

* `bruteCall_exec`: brute force on the leaf `v_a … v_{a+m}` (`m ≤ 64`), `γ' = 1` or `2`;
* `l41Call_exec`: Lemma 4.1 on the leaf (`m > 64`) at grade `g = ⌈log₂ m⌉ ≤ μ`;
* `listS_exec`: the chord list of a piece: empty for a connector, the wall-filtered chords of
  the leaf's normal form for a leaf (`leaf_list`), with its validity in the chain model of the
  piece, degree `≤ 4`, `γ`-semigranularity and the size bound against `lemma41Nat μ`.
-/
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs NFLoc SignK WalkKey
open BuildRegions (famOf)
@[expose] public section
section exec
variable {P : Polygon} {W : ℕ}

/-- A store-free piece of the program writing registers of the driver's bands only. -/
theorem frame_of_wr {s : Stmt} {B : ℕ → Bool} {c c' : Config} {k : ℕ} (e : Exec P W s c c' k)
    (hs : wr B s = true) (hB : ∀ r, B r = true → bandOf r ∈ DrvR.drvBands)
    (hA : B ALLOC = false) : Frame DrvR.drvBands c c' k :=
  let F := exec_frameB e hs
  DrvT.frame_drv ⟨F.1, F.2.1, F.2.2.2.1, F.2.2.2.2⟩ hB hA ztbmr
theorem band21_not_brute : (21 : ℕ) ∉ bruteBands := by_decide
theorem band21_not_l41 : (21 : ℕ) ∉ l41Bands := by_decide
theorem brute_sub : bruteBands ⊆ DrvR.drvBands := by_decide
theorem l41_sub : l41Bands ⊆ DrvR.drvBands := by_decide
theorem rdB0 (c : Config) : rd c bBrute 0 = c.nreg 180000 := rfl
theorem rdB1 (c : Config) : rd c bBrute 1 = c.nreg 180001 := rfl
theorem rdB2 (c : Config) : rd c bBrute 2 = c.nreg 180002 := rfl
theorem rdB3 (c : Config) : rd c bBrute 3 = c.nreg 180003 := rfl
theorem rdL0 (c : Config) : rd c bL41 0 = c.nreg 160000 := rfl
theorem rdL1 (c : Config) : rd c bL41 1 = c.nreg 160001 := rfl
theorem rdL2 (c : Config) : rd c bL41 2 = c.nreg 160002 := rfl
theorem rdL3 (c : Config) : rd c bL41 3 = c.nreg 160003 := rfl
theorem rdL4 (c : Config) : rd c bL41 4 = c.nreg 160004 := rfl
set_option maxHeartbeats 4000000 in
/-- **Brute force on a short leaf.** -/
theorem bruteCall_exec {sB : Stmt} {κB : ℕ} (hBm : BruteM sB κB) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (h21 : c.nreg 218021 = 1) (hm1 : 1 ≤ c.nreg 218002) (hm64 : c.nreg 218002 ≤ 64)
    (ham : c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n)
    (hroom : c.nreg ALLOC + κB * 274625 + 10 ≤ W) :
    ∃ c' k, Exec P W zthti c c' k ∧ k ≤ κB * 274625 + 10 ∧
      Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → r ≠ 218015 → c'.nreg r = c.nreg r) ∧
      ∃ CQ N₀ γ', CQ.P = Qof P ∧ CQ.s = c.nreg 218004 ∧ CQ.m = c.nreg 218002 ∧
        Robust ztdo c'.nmem ztfby ∧
        IsCanonicalNF ztmhi zta N₀ γ' 4 ∧
        ((c.nreg 218002 = 1 ∧ γ' = 1) ∨ (2 ≤ c.nreg 218002 ∧ γ' = 2)) := by
  have hW1 : 10 ≤ W := by_omega
  -- the granularity
  obtain ⟨c₁, k₁, e₁, hk₁, v02, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      ztfmf c c₁ k₁ ∧
      k₁ ≤ 3 ∧ ((c.nreg 218002 = 1 ∧ c₁.nreg 180002 = 1) ∨
        (2 ≤ c.nreg 218002 ∧ c₁.nreg 180002 = 2)) ∧
      ztedf ∧ FrameB (fun r => r == 180002) c c₁ := by
    by_cases h : c.nreg 218021 < c.nreg 218002
    · obtain ⟨c₁, k₁, e₁, hk₁, v, r⟩ : ∃ c₁ k₁, Exec P W (block [.constN 180002 2]) c c₁ k₁ ∧
          k₁ = 1 ∧ c₁.nreg 180002 = 2 ∧ ztedf := by
        exec_block
        · omega
        simp_all
      have ex := Exec.ifLtN_true (e := block [.constN 180002 1]) h e₁
      zqblv
    · obtain ⟨c₁, k₁, e₁, hk₁, v, r⟩ : ∃ c₁ k₁, Exec P W (block [.constN 180002 1]) c c₁ k₁ ∧
          k₁ = 1 ∧ c₁.nreg 180002 = 1 ∧ ztedf := by
        exec_block
        · omega
        simp_all
      have ex := Exec.ifLtN_false (t := block [.constN 180002 2]) h e₁
      zqblv
  zud
  -- the inputs
  obtain ⟨c₂, k₂, e₂, hk₂, v00, v01, v02'⟩ : ∃ c₂ k₂, Exec P W
      ztkrw c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg 180000 = c.nreg 218004 ∧ c₂.nreg 180001 = c.nreg 218002 ∧
      c₂.nreg 180002 = c₁.nreg 180002 := by
    exec_block
    simp_all
  zue
  have F₁₂ : FrameB (fun r => decide _) c c₂ :=
    (exec_frameB ztsxa by_decide : FrameB (fun r => decide ztnez)
      c c₂)
  have hA₂ : ztbae := F₁₂.1 _ by_decide
  -- the call
  have hγ1 : 1 ≤ c₂.nreg 180002 ∧ (c₂.nreg 180001 = 1 ∨ 2 ≤ c₂.nreg 180002) := by
    omega
  have hpow : ztrod ^ 3 ≤ 274625 := by
    rw [v01]
    calc (c.nreg 218002 + 1) ^ 3 ≤ 65 ^ 3 := Nat.pow_le_pow_left by_omega 3
      _ = 274625 := by_norm_num
  have hcost : κB * ztrod ^ 3 ≤ κB * 274625 := Nat.mul_le_mul_left _ hpow
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨CQ, N₀, hCQ, hCs, hCm, hN₀, hcan⟩, F₃⟩ := hBm P W c₂ w₂
    ⟨hG, hW, by rw [rdB1, v01]; omega, by rw [rdB0, rdB1, v00, v01]; omega,
      by rw [rdB2]; omega, by rw [rdB1, rdB2]; omega⟩
    (by show c₂.nreg ALLOC + κB * ztpdk ^ 3 ≤ W
        rw [rdB1, hA₂]; omega)
  replace hk₃ : k₃ ≤ κB * 274625 := hk₃.trans (by show κB * ztpdk ^ 3 ≤ _
                                                  rw [rdB1]; omega)
  zubj
  -- the output
  obtain ⟨c₄, k₄, e₄, hk₄, v15, r₄⟩ : ∃ c₄ k₄, Exec P W (block [.copyN 218015 180003]) c₃ c₄ k₄ ∧
      k₄ = 1 ∧ c₄.nreg 218015 = c₃.nreg 180003 ∧
      c₄ = { c₃ with nreg := upd c₃.nreg 218015 (c₃.nreg 180003) } := by
    exec_block
    simp
  have ex : Exec P W zthti c c₄ _ :=
    .seq e₁ ztcb
  have G₁ : ztzop := DrvT.frame_drv
    ⟨F₁₂.1, F₁₂.2.1, F₁₂.2.2.2.1, F₁₂.2.2.2.2⟩
    (fun r hr => by zvmwo at hr; zunsb; unfold bandOf
                    omega) by_decide (fun a _ => by rw [F₁₂.2.2.1])
  have G₂ := F₃.mono brute_sub le_rfl
  have G₃ := frame_of_wr e₄ (B := fun r => r == 218015)
    by_decide ztbsr by_decide
  refine ⟨c₄, _, ex, by_omega, (G₁.trans ztmbd).mono by_simp by_omega, ?_,
    CQ, N₀, c₂.nreg 180002, hCQ, by rw [hCs, rdB0, v00], by rw [hCm, rdB1, v01], ?_, ?_, ?_⟩
  · intro r hr h15
    zuezf
    rw [F₃.1 r ztcmf ztcug,
      F₁₂.1 r ztdua]
  · zugxb
    have hA₄ : upd c₃.nreg 218015 (c₃.nreg 180003) ALLOC = c₃.nreg ALLOC := by_rfl
    zuovw
    rw [rdB3] at hN₀
    omega
  · rw [rdB2] at hcan; omega
  omega
theorem seven_le_clog {m : ℕ} (hm : 65 ≤ m) : 7 ≤ Nat.clog 2 m := by
  zubq

  have h1 : ztizy := Nat.le_pow_clog by_norm_num m
  have h2 : 2 ^ Nat.clog 2 m ≤ 2 ^ 6 := Nat.pow_le_pow_right by_norm_num by_omega
  grind
variable {O : OracleIface} {sL sB : Stmt} {κL κB : ℕ}
set_option maxHeartbeats 4000000 in
/-- **Lemma 4.1 on a long leaf.** -/
theorem l41Call_exec {sL : Stmt} {κL : ℕ} (hLm : L41M O sL κL) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hgr : (gradeCtx O).holds P c.nmem ztcuu ztm)
    (h21 : c.nreg 218021 = 1) (hm65 : 65 ≤ c.nreg 218002) {μ : ℕ}
    (hμm : c.nreg 218002 ≤ 2 ^ μ) (hμΛ : μ ≤ c.nmem ztcuu)
    (ham : c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n)
    (hroom : c.nreg ALLOC + 4 * μ + 9 + κL * ztud ≤ W) :
    ∃ c' k, Exec P W zthyo c c' k ∧ k ≤ 4 * μ + 9 + κL * ztud ∧
      Frame DrvR.drvBands c c' k ∧
      ztede ∧
      ∃ CQ N₀ g, CQ.P = Qof P ∧ CQ.s = c.nreg 218004 ∧ CQ.m = c.nreg 218002 ∧
        Robust ztdo c'.nmem ztfby ∧
        IsCanonicalNF ztmhi zta N₀ ztcvr 4 ∧ 1 ≤ g ∧ g ≤ μ ∧
        c.nreg 218002 ≤ 2 ^ g := by
  zuixh
  zudwh
  obtain ⟨m, hm⟩ : ztjbs := by_simp_all
  zvmwi at hm65 hμm ham ⊢
  set g := Nat.clog 2 m with hg
  have hg7 := seven_le_clog hm65
  have hgμ := Nat.clog_le_of_le_pow hμm
  have hmg : m ≤ 2 ^ g := Nat.le_pow_clog by_norm_num m
  have hgm : 2 ^ ztfe < m := by
    have := Nat.pow_pred_clog_lt_self (b := 2) by_norm_num (x := m) by_omega
    omega
  -- the grade
  obtain ⟨c₁, k₁, e₁, hk₁, v19, r₁, m₁, rr₁, rm₁, o₁⟩ := clogS_exec (P := P) c hw hm by_omega
    h21 by_omega
  rw [← hg] at v19 hk₁
  zud
  -- the inputs
  obtain ⟨c₂, k₂, e₂, hk₂, v0, v1, v2, v3, r₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      (block [.copyN 160000 218008, .copyN 160001 218004, .copyN 160002 218002,
        .copyN 160003 218019]) c₁ c₂ k₂ ∧ k₂ = 4 ∧
      c₂.nreg 160000 = c.nreg 218008 ∧ c₂.nreg 160001 = c.nreg 218004 ∧
      c₂.nreg 160002 = m ∧ c₂.nreg 160003 = g ∧
      (∀ r, (r < 160000 ∨ 160004 ≤ r) → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · zufx
  zue
  have hA₂ : ztbae := by
    rw [r₂ _ by_decide, r₁ _ by_decide by_decide]
  have hm₂ : ztckc := by_simp_all
  have hcost : κL * ztcnv ≤ κL * ztud :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (lemma41Nat_mono hgμ) 1)
  -- the call
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨CQ, N₀, hCQ, hCs, hCm, hN₀, hcan⟩, F₃⟩ := hLm P W c₂ w₂
    ⟨hG, hW, by rw [rdL0, v0, hm₂, hA₂]; omega, by rw [rdL0, rdL3, v0, v3, hm₂]; omega,
      by rw [rdL3, v3]; exact hg7, by rw [rdL1, rdL2, v1, v2]; omega,
      by zunsd; omega, by zunsd; omega⟩
    (by show c₂.nreg ALLOC + κL * zthyq ≤ W
        rw [rdL3, v3, hA₂]; omega)
  replace hk₃ : k₃ ≤ κL * ztud := hk₃.trans (by
    show κL * zthyq ≤ _
    rw [rdL3, v3]; omega)
  rw [rdL1, v1] at hCs
  rw [rdL2, v2] at hCm
  rw [rdL3, v3] at hcan
  rw [rdL4] at hN₀
  zubj
  -- the output
  obtain ⟨c₄, k₄, e₄, hk₄, v15, r₄⟩ : ∃ c₄ k₄, Exec P W (block [.copyN 218015 160004]) c₃ c₄ k₄ ∧
      k₄ = 1 ∧ c₄.nreg 218015 = c₃.nreg 160004 ∧
      c₄ = { c₃ with nreg := upd c₃.nreg 218015 (c₃.nreg 160004) } := by
    exec_block
    simp
  have ex : Exec P W zthyo c c₄ _ :=
    .seq e₁ ztcb
  have G₁ : ztzop := by
    refine ⟨fun r hr hra => ?_, by_simp_all, by_simp_all,
      by simp_all, by_simp_all, by rw [hA₂], by_omega⟩
    have h1 : r < 160000 ∨ 160004 ≤ r := by
      by_contra h; exact hr (by zunsb; unfold bandOf; omega)
    rw [r₂ r h1, r₁ r ztwmm ztwmm]
  have G₂ := F₃.mono l41_sub le_rfl
  have G₃ := frame_of_wr e₄ (B := fun r => r == 218015)
    by_decide ztbsr by_decide
  refine ⟨c₄, _, ex, by_omega, (G₁.trans ztmbd).mono by_simp by_omega, ?_,
    CQ, N₀, g, hCQ, hCs, hCm, ?_, hcan, by_omega, hgμ, hmg⟩
  · intro r hr h15 h19 h23
    zuezf
    rw [F₃.1 r ztcmf ztcug,
      r₂ r ztbej, r₁ r h19 h23]
  · zugxb
    have hA₄ : upd c₃.nreg 218015 (c₃.nreg 160004) ALLOC = c₃.nreg ALLOC := by_rfl
    simp_all

/-- Lemma 2.3 on the normal form of a leaf. -/
theorem k0_count {Q : Polygon} {CQ : Chain} {N₀ : NF} {γ' : ℕ} (hP : CQ.P.Simple)
    (hcan : IsCanonicalNF ztmhi Q N₀ γ' 4) :
    N₀.chords.length * (γ' + 1) ≤ 840 * (2 * CQ.m + 1) := by
  have := DownMath.trans_count hP hcan
  rwa [DrvT.ncard_F hcan.1.2.1] at this
theorem gradeGran_ge (g : ℕ) : 2 ^ Cost.ceilBeta g ≤ gradeGran g := by
  unfold gradeGran; omega
theorem gradeGran_ge_one (g : ℕ) : 1 ≤ gradeGran g :=
  (Nat.one_le_two_pow).trans (gradeGran_ge g)
theorem gradeGran_ge_two {g : ℕ} (hg : 1 ≤ g) : 2 ≤ gradeGran g := by
  have h1 := DrvT.le_gradeGran g
  have h2 : 1 ≤ 2 ^ Cost.ceilBeta g := Nat.one_le_two_pow
  have : ztxpt := rfl
  have hf : ztlav := rfl
  grind
set_option maxHeartbeats 4000000 in
/-- **The normal form of a leaf** (brute force or Lemma 4.1) and the facts of its wall-filtered
chord list in the chain model of the piece. -/
theorem nf0_exec (hLm : L41M O sL κL)
    (hBm : BruteM sB κB) (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : hostWords P.n ≤ W)
    (hgr : (gradeCtx O).holds P c.nmem ztcuu ztm)
    (h21 : c.nreg 218021 = 1) (h22 : c.nreg 218022 = 65) (hm1 : 1 ≤ c.nreg 218002)
    (hμm : c.nreg 218002 ≤ 2 ^ c.nreg 218005) (hμΛ : c.nreg 218005 ≤ c.nmem ztcuu)
    (ham : c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n)
    (hγ : 2 * gradeGran ztmgb ≤ c.nreg 218007)
    (CH : Chain) (hCHs : CH.P.Simple)
    (htwin : ∀ CQ : Chain, CQ.P = Qof P → CQ.s = c.nreg 218004 → CQ.m = c.nreg 218002 →
      BoxT.Twin CQ CH)
    (hroom : c.nreg ALLOC + κB * 274625 + 12 + 4 * c.nreg 218005 +
      κL * ztbes ≤ W) :
    ∃ c' k, Exec P W ztyzz c c' k ∧
      k ≤ κB * 274625 + 12 + 4 * c.nreg 218005 + κL * ztbes ∧
      Frame DrvR.drvBands c c' k ∧
      ztede ∧
      ∃ N₀ : NF, Robust ztdo c'.nmem ztfby ∧
        ChordTriplesOK ztcpt zta ztdkt ∧
        (chainModel CH).DegLe
          ztxod 4 ∧
        (chainModel CH).Semigranular
          ztxod zthus ∧
        N₀.chords.length * ztqap ≤
          1950480 * ztbes ∧
        N₀.chords.length ≤ 108360 * ztbes := by
  zqblw
  zvnhc at hμm hμΛ hγ hroom ⊢
  zufgc
  by_cases h64 : c.nreg 218002 < c.nreg 218022
  · zukrt
    obtain ⟨c₁, k₁, e₁, hk₁, F₁, r₁, CQ, N₀, γ', hCQ, hCs, hCm, hN₀, hcan, hγ'⟩ :=
      bruteCall_exec hBm c hw hG hW h21 hm1 by_omega ham by_omega
    zqblu
    have hK₀ : N₀.chords.length ≤ 108360 := by
      grind
    have hKc : N₀.chords.length * ztqap ≤ 1950480 := by
      have h1 := kcost_mono hK₀
      tauto
    have hγle : 2 * γ' ≤ c.nreg 218007 := by
      rcases hγ' with ⟨h1, rfl⟩ | ⟨h2, rfl⟩
      · have := gradeGran_ge_one μ; omega
      · have hμ1 : 1 ≤ μ := by
          grind
        have := gradeGran_ge_two hμ1; omega
    refine ⟨c₁, _, Exec.ifLtN_true by_omega e₁, by_omega,
      Frame.mono F₁ le_rfl by_omega, by_simp_all, N₀, hN₀, hok, hdeg,
      semigranular_mono hwt hγle, ?_, ?_⟩
    · omega
    omega
  · zukrt
    obtain ⟨c₁, k₁, e₁, hk₁, F₁, r₁, CQ, N₀, g, hCQ, hCs, hCm, hN₀, hcan, hg1, hgμ, hmg⟩ :=
      l41Call_exec hLm c hw hG hW hgr h21 by_omega hμm hμΛ ham by_omega
    zqblu
    have hK2 : N₀.chords.length * 2 ^ Cost.ceilBeta g ≤ 2520 * 2 ^ g := by
      have h1 : N₀.chords.length * 2 ^ Cost.ceilBeta g ≤ N₀.chords.length * ztlpj :=
        Nat.mul_le_mul_left _ (by have := gradeGran_ge g; omega)
      grind
    have hKc := kcost_le hg1 hK2
    have hmono := lemma41Nat_mono hgμ
    have hγle := (Nat.mul_le_mul_left 2 (gradeGran_mono hgμ)).trans hγ
    refine ⟨c₁, _, Exec.ifLtN_false by_omega e₁, by_omega,
      Frame.mono F₁ le_rfl by_omega, r₁, N₀, hN₀, hok, hdeg, semigranular_mono hwt hγle, ?_, ?_⟩
    · omega
    grind

/-- The constant of the chord list of a piece. -/
def κLst (κL κB : ℕ) : ℕ := κB * 274625 + κL + 4659540
set_option maxRecDepth 100000 in
theorem lst_cost (κL κB μ X : ℕ) (hX : μ + 1 ≤ X) :
    κB * 274625 + 12 + 4 * μ + κL * X + 43 * ztsqx + 22 ≤ κLst κL κB * X := by
  unfold κLst
  have e : (κB * 274625 + κL + 4659540) * X = κB * 274625 * X + κL * X + 4659540 * X := by_ring
  zui
  have h2 : 43 * ztsqx = 4659480 * X := by_ring
  zuczw
  have h1 : κB * 274625 ≤ κB * 274625 * X := Nat.le_mul_of_pos_right _ by_omega
  grind
set_option maxHeartbeats 4000000 in
/-- **The chord list of a piece**: empty (connector) or the wall-filtered chords of the normal
form of the leaf, at `218016` (length `218017`), below the allocator. -/
theorem listS_exec (hLm : L41M O sL κL)
    (hBm : BruteM sB κB) (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : hostWords P.n ≤ W)
    (hgr : (gradeCtx O).holds P c.nmem ztcuu ztm)
    (h21 : c.nreg 218021 = 1) (h22 : c.nreg 218022 = 65)
    (hm1 : 1 ≤ c.nreg 218002) (hkind : c.nreg 218003 ≤ 1)
    (hleaf : c.nreg 218003 = 1 → c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧
      c.nreg 218005 ≤ c.nmem ztcuu ∧ c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n ∧
      2 * gradeGran ztmgb ≤ c.nreg 218007)
    (hconn : c.nreg 218003 = 0 → c.nreg 218002 ≤ 64 ∧ 2 * c.nreg 218002 ≤ c.nreg 218007)
    (CH : Chain) (hCHs : CH.P.Simple) (hCm : CH.m = c.nreg 218002)
    (htwin : c.nreg 218003 = 1 → ∀ CQ : Chain, CQ.P = Qof P → CQ.s = c.nreg 218004 →
      CQ.m = c.nreg 218002 → BoxT.Twin CQ CH)
    (hroom : c.nreg ALLOC + κLst κL κB * ztbes ≤ W) :
    ∃ c' k, Exec P W zttsj c c' k ∧
      k ≤ κLst κL κB * ztbes ∧ Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → (r < 218015 ∨ 218024 ≤ r) → (r < 218070 ∨ 218081 ≤ r) →
        c'.nreg r = c.nreg r) ∧
      ∃ L : List zte, ChordListAt c'.nmem (c'.nreg 218016) L ∧
        c'.nreg 218017 = L.length ∧ c'.nreg 218016 + 3 * L.length ≤ c'.nreg ALLOC ∧
        ChordTriplesOK ztcpt zta L ∧
        (chainModel CH).DegLe ztzlu 4 ∧
        (chainModel CH).Semigranular ztzlu zthus ∧
        L.length * ztjki ≤ 1950480 * ztbes := by
  zqblw
  zuikt
  have hμl := le_lemma41Nat μ
  unfold listS
  by_cases hk : c.nreg 218003 < c.nreg 218021
  · -- a connector
    have hk0 : c.nreg 218003 = 0 := by_omega
    obtain ⟨h64, h2m⟩ := hconn hk0
    obtain ⟨c₁, k₁, e₁, hk₁, v16, v17, r₁⟩ : ∃ c₁ k₁, Exec P W connS c c₁ k₁ ∧ k₁ = 2 ∧
        c₁.nreg 218016 = 0 ∧ c₁.nreg 218017 = 0 ∧
        (∀ r, r ≠ 218016 → r ≠ 218017 → c₁.nreg r = c.nreg r) := by
      unfold connS
      exec_block
      all_goals first | omega | skip
      simp_all
    have ex := Exec.ifLtN_true (e := leafS sL sB) hk e₁
    obtain ⟨hok, hdeg, hwt⟩ := conn_list hCHs (γ := c.nreg 218007) by_omega
    have G₁ := frame_of_wr e₁
      (B := fun r => decide (218016 ≤ r ∧ r < 218018))
      by_rfl (fun r hr => by
        zvmwo at hr; zunsb; unfold bandOf; omega)
      by_decide
    refine ⟨c₁, _, ex, ?_, G₁.mono le_rfl by_omega, by_grind,
      [], fun i hi => by_simp_all, by_omega, by_simp_all, hok, hdeg, hwt,
      by simp⟩
    have := lst_cost κL κB μ ztud by_omega
    omega
  · -- a leaf
    have hk1 : c.nreg 218003 = 1 := by_omega
    obtain ⟨hμm, hμΛ, ham, hγ⟩ := hleaf hk1
    zumjp
    unfold leafS
    have hroom' : c.nreg ALLOC + κB * 274625 + 12 + 4 * c.nreg 218005 +
        κL * ztbes ≤ W := by
      zujkb
      have := lst_cost κL κB μ ztud by_omega
      omega
    obtain ⟨c₁, k₁, e₁, hk₁, F₁, r₁, N₀, hN₀, hok, hdeg, hwt, hKc, hK₀⟩ := nf0_exec hLm hBm c hw
      hG hW hgr h21 h22 hm1 by_simp_all by_omega ham
      by_simp_all CH hCHs (htwin hk1) hroom'
    zvnhc at hk₁ hKc hK₀
    zud
    have h21₁ : c₁.nreg 218021 = 1 := by
      rw [r₁ _ by_decide by_decide by_decide by_decide]; omega
    have hA₁ := F₁.2.2.2.2.2.2
    obtain ⟨c₂, k₂, e₂, hk₂, hk₂', v16, v17, v99, hCL, hlow, r₂, rr₂, rm₂, o₂⟩ :=
      dropS_exec c₁ w₁ hN₀ h21₁ (by
        have := lst_cost κL κB μ ztud by_omega
        omega)
    set L := BoxT.dropWalls _ with hL
    have hLK : L.length ≤ N₀.chords.length := by
      have := List.length_filter_le keepW (DrvT.triplesOf N₀)
      unfold DrvT.triplesOf at this; rw [List.length_map] at this
      rw [hL, dropWalls_eq]; exact this
    have G₂ : ztiyg := by
      refine ⟨fun r hr hra => ?_, by_grind, hlow, by_grind, o₂,
        by omega, by_omega⟩
      have hb : bandOf r ≠ 21 := fun h => hr ztik
      exact r₂ r zthfw zthfw
        zthfw hra
    refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, ?_, (F₁.trans G₂).mono by_simp by_omega, ?_, L, ?_, ?_, ?_,
      hok, hdeg, hwt, (kcost_mono hLK).trans hKc⟩
    · have := lst_cost κL κB μ ztud by_omega
      omega
    · intro r hr h1 h2
      rw [r₂ r by_omega by_omega h2 ztcug,
        r₁ r hr by_omega by_omega by_omega]
    · grind
    · rw [v17]
    omega
end exec
end
end DrvP
end Chazelle.Core
end
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs NFLoc SignK WalkKey
@[expose] public section
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
theorem rdBd0 : rd c bBuild 0 = c.nreg 40000 := rfl
theorem rdBd1 : rd c bBuild 1 = c.nreg 40001 := rfl
theorem rdBd2 : rd c bBuild 2 = c.nreg 40002 := rfl
theorem rdBd3 : rd c bBuild 3 = c.nreg 40003 := rfl
theorem rdG0 : rd c bGran 0 = c.nreg 90000 := rfl
theorem rdG1 : rd c bGran 1 = c.nreg 90001 := rfl
theorem rdG2 : rd c bGran 2 = c.nreg 90002 := rfl
theorem rdG3 : rd c bGran 3 = c.nreg 90003 := rfl
theorem rdG4 : rd c bGran 4 = c.nreg 90004 := rfl
theorem build_sub : ({bBuild, bSort, bSign} : Finset ℕ) ⊆ DrvR.drvBands := by_decide
theorem gran_sub : granBands ⊆ DrvR.drvBands := by_decide
theorem band21_not_build : (21 : ℕ) ∉ ({bBuild, bSort, bSign} : Finset ℕ) := by_decide
theorem band21_not_gran : (21 : ℕ) ∉ granBands := by_decide

/-- A frame of a block of register copies into one band of the driver. -/
theorem frame_copies {s : Stmt} {c c' : Config} {k : ℕ} (e : Exec P W s c c' k) {lo hi : ℕ}
    (hs : wr (fun r => decide (lo ≤ r ∧ r < hi)) s = true)
    (hband : ∀ r, lo ≤ r → r < hi → bandOf r ∈ DrvR.drvBands) (hA : ¬ (lo ≤ ALLOC ∧ ALLOC < hi)) :
    Frame DrvR.drvBands c c' k :=
  frame_of_wr e hs ztcvp
    by_simp_all
set_option maxHeartbeats 4000000 in
/-- **The build.** -/
theorem buildS_exec {sBd : Stmt} {κBd : ℕ} (hBd : BuildM sBd κBd) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hD : ModelDescWF P ztm c.nmem ztmgc) {M : Model}
    {L : List zte} (hM : ModelDescAt c.nmem ztmgc zta M)
    (hGM : GoodModel M) (hK : c.nreg 218017 = L.length)
    (hB : c.nreg 218016 + 3 * L.length ≤ c.nreg ALLOC)
    (hCL : ChordListAt c.nmem (c.nreg 218016) L) (hok : ChordTriplesOK M zta L)
    (hroom : c.nreg ALLOC + κBd * ztbma + 4 ≤ W) :
    ∃ c' k, Exec P W ztvfx c c' k ∧
      k ≤ κBd * ztbma + 4 ∧ Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → r ≠ 218018 → c'.nreg r = c.nreg r) ∧
      ∃ N, c.nreg ALLOC ≤ c'.nreg 218018 ∧ NFWithin c'.nmem (c'.nreg 218018) ztdo N ∧
        IsNF M zta N ∧ N.chords.map ztwma = L := by
  obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, r₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 40000 218010, .copyN 40001 218016, .copyN 40002 218017]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 40000 = c.nreg 218010 ∧ c₁.nreg 40001 = c.nreg 218016 ∧
      c₁.nreg 40002 = c.nreg 218017 ∧ (∀ r, (r < 40000 ∨ 40003 ≤ r) → c₁.nreg r = c.nreg r) := by
    exec_block
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, fun r hr => ?_⟩
    zufx
  zud
  have G₁ : ztmtc := frame_copies e₁ (lo := 40000) (hi := 40003)
    by_decide zthhd
    by_decide
  have hm₁ : ztwh := (exec_frameB e₁ (B := fun r => decide (40000 ≤ r ∧ r < 40003))
    by_decide).2.2.1
  zuhwl
  obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hBd P W c₁ w₁
    ⟨hG, hW, by rw [rdBd0, v0, hm₁, hA₁]; exact hD, M, L, by zunyg; exact hM, hGM,
      by rw [rdBd2, v2, hK], by rw [rdBd1, v1, hA₁]; exact hB, by zunyh; omega,
      hok⟩
    (by show c₁.nreg ALLOC + κBd * ztfuh ≤ W
        rw [rdBd2, v2, hK, hA₁]; omega)
  replace hk₂ : k₂ ≤ κBd * ztbma := by
    have : k₂ ≤ κBd * ztfuh := hk₂
    rw [rdBd2, v2, hK] at this; omega
  obtain ⟨N, hN1, hN2, hN3, hN4, -⟩ := hpost M L (by zunyg; exact hM)
    (by rw [rdBd2, v2, hK]) (by zunyh; omega)
  rw [rdBd3] at hN1 hN2
  zue
  obtain ⟨c₃, k₃, e₃, hk₃, v18, r₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 218018 40003]) c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 218018 = c₂.nreg 40003 ∧
      c₃ = { c₂ with nreg := upd c₂.nreg 218018 (c₂.nreg 40003) } := by
    exec_block
    simp
  have G₂ : ztiyg := F₂.mono build_sub le_rfl
  have G₃ : ztmtd := frame_of_wr e₃ (B := fun r => r == 218018)
    by_decide ztbsr by_decide
  zuffy
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega,
    (G₁.trans ztmbd).mono by_simp by_omega, fun r hr h18 => ?_, N, ?_, ?_, hN3, hN4⟩
  · zuodv; simp only [upd, ite_eq_right h18]
    rw [F₂.1 r ztcmf ztcug,
      r₁ r ztbej]
  · omega
  grind
set_option maxHeartbeats 4000000 in
/-- **The granularity enforcement** (cap `4`, target `γ` from `218007`). -/
theorem granS_exec {sG : Stmt} {κG : ℕ → ℕ} (hGm : GranM sG κG) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hD : ModelDescWF P ztm c.nmem ztmgc) {M : Model} {N : NF}
    (hM : ModelDescAt c.nmem ztmgc zta M) (hGM : GoodModel M)
    (hN : NFWithin c.nmem (c.nreg 218018) ztm N) (hNF : IsNF M zta N)
    (hdeg : M.DegLe ztwiv 4) (hwt : M.Semigranular ztwiv zthus)
    (hroom : c.nreg ALLOC + κG 4 * ztenk + 5
      ≤ W) :
    ∃ c' k, Exec P W ztvrl c c' k ∧
      k ≤ κG 4 * ztenk + 5 ∧
      Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → r ≠ 218011 → c'.nreg r = c.nreg r) ∧
      ∃ N', c.nreg ALLOC ≤ c'.nreg 218011 ∧
        NFWithin c'.nmem ztqhb ztdo N' ∧
        IsCanonicalNF M zta N' zthus 4 := by
  have hW1 : ztpil := by_omega
  obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, v3, r₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 90000 218010, .copyN 90001 218018, .constN 90002 4, .copyN 90003 218007])
      c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 90000 = c.nreg 218010 ∧ c₁.nreg 90001 = c.nreg 218018 ∧ c₁.nreg 90002 = 4 ∧
      c₁.nreg 90003 = c.nreg 218007 ∧ (∀ r, (r < 90000 ∨ 90004 ≤ r) → c₁.nreg r = c.nreg r) := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, fun r hr => ?_⟩
    zufx
  zud
  have G₁ : ztmtc := frame_copies e₁ (lo := 90000) (hi := 90004)
    by_decide zthhd
    by_decide
  have hm₁ : ztwh := (exec_frameB e₁ (B := fun r => decide (90000 ≤ r ∧ r < 90004))
    by_decide).2.2.1
  zuhwl
  have hK : c₁.nmem (c₁.nreg 90001) = N.chords.length := by
    rw [hm₁, v1]; exact hN.nfAt.1
  obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hGm P W c₁ w₁
    ⟨hG, hW, by zuojg; omega, by rw [rdG0, v0, hm₁, hA₁]; exact hD, M, N,
      by zunyi; exact hM, hGM, by rw [rdG1, v1, hm₁, hA₁]; exact hN, hNF,
      by zuojg; omega, by rw [rdG3, v3]; omega⟩
    (by show c₁.nreg ALLOC + κG ztrwh * (c₁.nmem ztiai *
          ztyhu + 1) ≤ W
        rw [rdG2, rdG1, v2, hK, hA₁]; omega)
  replace hk₂ : k₂ ≤ κG 4 * ztenk := by
    have : k₂ ≤ κG ztrwh * (c₁.nmem ztiai *
        ztyhu + 1) := hk₂
    rw [rdG2, rdG1, v2, hK] at this; omega
  obtain ⟨N', hN1, hN2, -, hN3⟩ := hpost M N (by zunyi; exact hM)
    (by rw [rdG1, v1, hm₁]; exact hN.nfAt)
  rw [rdG4] at hN1 hN2
  rw [rdG3, rdG2, v3, v2] at hN3
  zue
  obtain ⟨c₃, k₃, e₃, hk₃, v11, r₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 218011 90004]) c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 218011 = c₂.nreg 90004 ∧
      c₃ = { c₂ with nreg := upd c₂.nreg 218011 (c₂.nreg 90004) } := by
    exec_block
    simp
  have G₂ : ztiyg := F₂.mono gran_sub le_rfl
  have G₃ : ztmtd := frame_of_wr e₃ (B := fun r => r == 218011)
    by_decide ztbsr by_decide
  zuffy
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega,
    (G₁.trans ztmbd).mono by_simp by_omega, fun r hr h11 => ?_, N', ?_, ?_, hN3⟩
  · zuodv; simp only [upd, ite_eq_right h11]
    rw [F₂.1 r ztcmf ztcug,
      r₁ r ztbej]
  · omega
  simp_all
end exec
end
end DrvP
end Chazelle.Core
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs NFLoc SignK WalkKey
open BuildRegions (famOf)
@[expose] public section
def κP (κL κB κBd : ℕ) (κG : ℕ → ℕ) : ℕ :=
  141204 + κLst κL κB + 1950481 * κBd + 1950481 * κG 4 + 9

/-- The arithmetic of the cost of a piece. -/
theorem piece_cost (κL κB κBd κG4 μ X K : ℕ) (hX : μ + 1 ≤ X) (hK : K ≤ 1950480 * X) :
    (1204 * μ + 140000) + κLst κL κB * X + (κBd * ztbr + 4) + (κG4 * ztbr + 5) ≤
      ztgxu * X := by
  have e : ztgxu * X =
      141204 * X + κLst κL κB * X + κBd * ztjeq + κG4 * ztjeq + 9 * X := by_ring
  zui
  have h1 : κBd * ztbr ≤ κBd * ztjeq := Nat.mul_le_mul_left _ by_omega
  have h2 : κG4 * ztbr ≤ κG4 * ztjeq := Nat.mul_le_mul_left _ by_omega
  omega
variable {Q : Polygon} {H : Host} {C : Chain} {O : OracleIface}
/-- The model descriptor of a piece is robust. -/
theorem desc_robust {m₀ m : ℕ → ℕ} {A E HB : ℕ}
    (hH : Robust A m₀ (fun m' => HostAt m' HB H)) (hlow : ∀ a, a < A → m a = m₀ a)
    (hAE : A + 6 ≤ E) (hP : C.P = H.poly Q)
    (d0 : m A = 0) (d1 : m ztbo = HB) (d2 : m ztbcl = C.s) (d3 : m zttf = C.m)
    (d4 : m ztckz = C.topIdx) (d5 : m ztgzp = 1 ↔ C.sideBeta = true) :
    Robust E m (fun m' => m' A = 0 ∧ ChainDescAt m' ztbo Q H C ∧ m' ztbo = HB) := by
  zubxa
  have e0 : m' A = m A := by_grind
  have e : ∀ i, 1 ≤ i → i < 6 → m' _ = m ztfna := fun i h1 hi => hm' _ by_omega
  have e1 : m' ztbo = HB := by_simp_all
  refine ⟨by_omega, ⟨?_, hP, ?_, ?_, ?_, ?_⟩, e1⟩
  · zvmxy; exact hH m' by_grind
  · grind
  · grind
  · grind
  grind

/-- The model descriptor of a piece is well formed. -/
theorem desc_wf {P : Polygon} {H : Host} {C : Chain} {m : ℕ → ℕ} {A E HB : ℕ}
    (hdesc : m A = 0 ∧ ChainDescAt m ztbo zta H C ∧ m ztbo = HB)
    (hAE : A + 6 ≤ E) (hHB : HB + 3 * H.length + 4 ≤ E) (hl : H.length ≤ 64)
    (hwf : HostWF P.n H) (hs : C.s < C.P.n) : ModelDescWF P E m A := by
  obtain ⟨h0, hd, h1⟩ := hdesc
  refine ⟨hAE, fun _ => ⟨by_omega, fun H' C' hd' => ?_⟩⟩
  have hH' := hostAt_unique hd'.1 hd.1
  subst hH'
  have hP : ztmsw := by rw [hd'.2.1, hd.2.1]
  have hs' : ztidk := by rw [← hd'.2.2.1, hd.2.2.1]
  simp_all
theorem modelDescAt_of {m : ℕ → ℕ} {A HB : ℕ}
    (hdesc : m A = 0 ∧ ChainDescAt m ztbo Q H C ∧ m ztbo = HB) :
    ModelDescAt m A Q ztc :=
  Or.inl by_grind
theorem gradeCtx_frame {P : Polygon} {m m' : ℕ → ℕ} {g A A' : ℕ}
    (h : (gradeCtx O).holds P m g A) (hm : ∀ a, a < A → m' a = m a) (hA : A ≤ A') :
    (gradeCtx O).holds P m' g A' :=
  (gradeCtx O).mono P m' g A A' hA ((gradeCtx O).local_ P m m' g A by_simp_all h)
set_option maxHeartbeats 16000000 in
/-- **The pieces of a region chain (D4)**, from Lemma 4.1. -/
theorem pieceSpec_of (hL : Lemma41Spec O) : DrvR.PieceSpec O := by
  classical
  obtain ⟨sL, κL, hLm⟩ := (lemma41Spec_iff O).1 hL
  obtain ⟨sB, κB, hBm⟩ := bruteSpec_iff.1 brute
  obtain ⟨sBd, κBd, hBdm⟩ := buildNFSpec_iff.1 buildNFOK
  obtain ⟨sG, κG, hGm⟩ := granularizeSpec_iff.1 granularize
  refine ⟨pieceS sL sB sBd sG, κP κL κB κBd κG, fun P W c hw hpre hroom => ?_⟩
  obtain ⟨hG, hW, hgr, hD4, hm1, hkind, H, hH, hHA, hl, hwf, hreg, hsimp, hsm, hleaf, hconn⟩ :=
    hpre
  zugou
  zugrc
  have hμX : μ + 1 ≤ lemma41Nat μ + 1 := by have := le_lemma41Nat μ; omega
  replace hroom : A + κP κL κB κBd κG * ztud ≤ W := by
    simp_all
  have hn : ztx := qof_n P
  have hNpts : (H.poly _).n = (H.pts (Qof P).n).length := DownMath.host_poly_n _ _
  let CH : Chain := ⟨H.poly zta, c.nreg 218001, c.nreg 218002, hm1, by_omega⟩
  have hCHP : CH.P = H.poly _ := rfl
  have hCHs : CH.s = c.nreg 218001 := rfl
  have hCHm : CH.m = c.nreg 218002 := rfl
  have hgh : c.nreg 218008 + 3 < A := by rw [← hA]; exact (ShootCut.grade_low hgr).1
  -- the leaf facts
  have hleaf' : ¬ c.nreg 218002 < 65 → c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧
      c.nreg 218005 ≤ c.nmem ztcuu ∧ c.nreg 218004 + c.nreg 218002 + 1 ≤ (Qof P).n ∧
      ∀ k, k ≤ c.nreg 218002 →
        (H.pts (Qof P).n).getD zthuq ztga = .vtx zthur := by
    grind
  have hcost0 := piece_cost κL κB κBd ztqzn μ _ 0 hμX ztbg
  have hκP : κP κL κB κBd κG = 141204 + κLst κL κB + 1950481 * κBd + 1950481 * κG 4 + 9 := rfl
  rw [← hκP] at hcost0
  -- 1. the descriptor part
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, d10, d99, gin₁, gout₁, v20, v21, v22, ml₁, d0, d1, d2, d3, d4,
    d5⟩ := frontS_exec c hw hG hW hgr hm1 hH hHA hl hwf hsm hleaf'
      by_omega CH hCHP hCHs hCHm
  zvmze at d10 d99 ml₁ d0 d1 d2 d3 d4 d5
  zvnhc at hk₁
  zud
  have i₁ : ∀ r, 218000 ≤ r → r < 218010 → c₁.nreg r = c.nreg r := gin₁
  -- 2. the chord list
  have hmem₁gh : c₁.nmem _ = c.nmem _ := ml₁ _ by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, gin₂, L, hCL, hK, hB, hok, hdeg, hwt, hKc⟩ :=
    listS_exec hLm hBm c₁ w₁ hG hW
      (by rw [i₁ _ by_norm_num by_norm_num, d99]
          exact gradeCtx_frame by_grind ml₁ by_omega)
      v21 v22 by_grind
      by_grind
      (fun hk => by
        grind)
      (fun hk => by
        grind)
      CH hsimp by_grind
      (fun hk CQ hQ hs hm => by
        rw [i₁ _ by_norm_num by_norm_num] at hk hs hm
        obtain ⟨-, -, a3, -, a5⟩ := hleaf hk
        zvmxq at a3
        refine twin_leaf hQ hs by_omega hCHP by_grind
          by_omega (fun k hk' => ?_)
        rw [hCHs]; unfold pt; grind)
      (by rw [d99, i₁ _ by_norm_num by_norm_num, hμ]
          omega)
  rw [i₁ _ by_norm_num by_norm_num, hμ] at hk₂ hKc
  rw [i₁ _ by_norm_num by_norm_num] at hwt
  zue
  -- the descriptor, robustly
  have hwf' : HostWF P.n H := by_grind
  have hR₁ : Robust ztbmq c₁.nmem (fun m => m A = 0 ∧
      ChainDescAt m ztbo zta H CH ∧ m ztbo = c.nreg 218000) := by
    rw [d99]
    exact desc_robust by_grind ml₁ le_rfl hCHP d0 d1 d2 d3 d4 d5
  have hs_lt : CH.s < CH.P.n := by_grind
  have hA₂ : A + 6 ≤ c₂.nreg ALLOC := by zuori; exact F₂.2.2.2.2.2.1
  have hR₂ := hR₁.frame F₂
  have r10₂ : c₂.nreg 218010 = A := by
    rw [gin₂ _ by_decide by_omega by_omega, d10]
  have hcost := piece_cost κL κB κBd ztqzn μ _
    _ hμX hKc
  rw [← hκP] at hcost
  have hk₂A : c₂.nreg ALLOC ≤ A + 6 + k₂ := by zuori; exact F₂.2.2.2.2.2.2
  -- 3. the build
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, gin₃, N₁, hN1, hN2, hN3, hN4⟩ := buildS_exec hBdm c₂ w₂ hG hW
    (by zuovx; exact desc_wf hR₂.holds hA₂ by_omega hl hwf' hs_lt)
    (by zuovx; exact modelDescAt_of hR₂.holds) ztzz hK hB hCL hok
    by_omega
  zubj
  -- 4. the granularity enforcement
  have r10₃ : c₃.nreg 218010 = A := by rw [gin₃ _ by_decide by_decide, r10₂]
  have r07₃ : c₃.nreg 218007 = c.nreg 218007 := by
    rw [gin₃ _ by_decide by_decide, gin₂ _ by_decide by_omega by_omega,
      i₁ _ by_norm_num by_norm_num]
  have hR₃ := hR₂.frame F₃
  have hA₃ : A + 6 ≤ c₃.nreg ALLOC := hA₂.trans F₃.2.2.2.2.2.1
  have hk₃A : c₃.nreg ALLOC ≤ c₂.nreg ALLOC + k₃ := F₃.2.2.2.2.2.2
  have hlenN : N₁.chords.length = L.length := by rw [← hN4, List.length_map]
  have hFN : N₁.F _ _ = famOf ztcpt zta L := BoxT.F_eq_famOf hN4
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, gin₄, N₂, hM1, hM2, hcan⟩ := granS_exec hGm c₃ w₃ hG hW
    (by zuovy; exact desc_wf hR₃.holds hA₃ by_omega hl hwf' hs_lt)
    (by zuovy; exact modelDescAt_of hR₃.holds) ztzz hN2 hN3
    by_grind by_grind
    (by rw [hlenN]
        omega)
  rw [hlenN] at hk₄
  rw [r07₃] at hcan
  have hR₄ := hR₃.frame F₄
  have hA₄ : A + 6 ≤ c₄.nreg ALLOC := hA₃.trans F₄.2.2.2.2.2.1
  have r10₄ : c₄.nreg 218010 = A := by rw [gin₄ _ by_decide by_decide, r10₃]
  have ex : ztiyf :=
    .seq e₁ ztcb
  have F := F₁.trans ztpyz
  refine ⟨c₄, _, ex, ?_, ⟨fun q hq hq' => ?_, ?_, ?_, ?_, fun H' C' hH' hP' hs' hm' => ?_⟩,
    by grind⟩
  · -- the cost
    show _ ≤ κP κL κB κBd κG * zthyq
    zujkb
    omega
  · -- the registers of the driver
    have hq21 : bandOf q = 21 := hq
    unfold bandOf at hq21
    rw [gin₄ q hq21 by_omega, gin₃ q hq21 by_omega, gin₂ q hq21 by_omega by_omega,
      gout₁ q hq' by_omega by_omega by_omega ztu]
  · omega
  · omega
  · zuovz; exact desc_wf hR₄.holds hA₄ by_omega hl hwf' hs_lt
  · -- the descriptor and the normal form of the chain
    have hHH := hostAt_unique hH' hH.holds
    zular
    have hCC : C' = CH := chain_eq by_omega by_omega by_omega
    subst hCC
    refine ⟨by zuovz; omega, N₂, hM2, canonical_cap hcan hD4⟩
end
end DrvP
end Chazelle.Core
namespace Chazelle.Core
namespace DrvP
@[expose] public section
theorem pieceSpec_of' {O : OracleIface} (hM : MergeSpec) (hV : O.Valid) : DrvR.PieceSpec O :=
  pieceSpec_of (L41.lemma41_of O hM ztjmv)
end
end DrvP
namespace DrvR
@[expose] public section
theorem lvCnt_le (l : ℕ) : lvCnt l ≤ DownMath.cntMax ztnfk ztzso :=
  DownMath.cnt_le_cntMax Nat.one_le_two_pow _ l

/-- **The down phase from a level and a base case** with the count `lvCnt` (the transition is
`DrvT.transSpec`). -/
theorem downPhaseH_of_level {X : MemCtx} (hX : X.CapLocal) {n₀ : ℕ}
    (hL : LevelSpec X lvCnt n₀) (hB : BaseSpec X lvCnt n₀) : DownPhaseSpecH X :=
  downPhaseH_of_parts hX lvCnt_le (DrvT.transSpec Nat.one_le_two_pow _) hL hB

/-- **The down phase** (`DownPhaseSpecH (gradeCtx O)`) from `MergeSpec`, valid oracles, and the
open components: the extraction (D6), the tail of a level (D12) and the base case (D9). -/
theorem downPhaseH_of (hM : MergeSpec) {O : OracleIface} (hV : O.Valid)
    (hX : ExtractRamSpec) (hT : LvTailSpec O) (hB : ∀ n₀, BaseSpec ztsy lvCnt n₀) :
    DownPhaseSpecH ztsy := by
  obtain ⟨n₀, hL⟩ := DrvLS.levelSpec_of DrvH.hostRamSpec
    (DrvG.regionSpec hM ztjmv (DrvP.pieceSpec_of' hM hV)) hX hT
    DownMath.hostR1Spec DrvLM.levelMathSpec DrvLC.lvCostSpec
  exact downPhaseH_of_level ztgjv hL (hB n₀)
end
end DrvR
public section
theorem linear_of_sweep_parts (hS : SweepSpecH) (hX : DrvR.ExtractRamSpec)
    (hT : ∀ O : OracleIface, O.Valid → DrvR.LvTailSpec O)
    (hB : ∀ O : OracleIface, O.Valid → ∀ n₀, DrvR.BaseSpec ztsy DrvR.lvCnt n₀) :
    LinearTimeTriangulation :=
  linear_of_sweep_down hS fun O hV =>
    DrvR.downPhaseH_of ztvza hV hX (hT O hV) (hB O hV)

/-- **Reduction of the main theorem** to the sweep, the extraction RAM (D6) and the base case
(D9): the tail of a level (D12) is proved (`DrvLT.lvTailSpec` from the interior oracles). -/
theorem linear_of_sweep_xb (hS : SweepSpecH) (hX : DrvR.ExtractRamSpec)
    (hB : ∀ O : OracleIface, O.Valid → ∀ n₀, DrvR.BaseSpec ztsy DrvR.lvCnt n₀) :
    LinearTimeTriangulation :=
  linear_of_sweep_parts hS hX
    (fun O hV => DrvLT.lvTailSpec (IOrc.interiorOracles_of ztjmv)) hB

/-- **Reduction of the main theorem** to the sweep, the extraction RAM (D6) and the region loop
of the base case (`DrvB.RegLoopSpec`): the top level of the base case is proved
(`DrvB.baseSpec_of_regLoop`). -/
theorem linear_of_sweep_xr (hS : SweepSpecH) (hX : DrvR.ExtractRamSpec)
    (hRL : DrvB.RegLoopSpec) : LinearTimeTriangulation :=
  linear_of_sweep_xb hS hX fun _ _ _ => DrvB.baseSpec_of_regLoop hRL
theorem linear_of_sweep_reg (hS : SweepSpecH) (hRL : DrvB.RegLoopSpec) :
    LinearTimeTriangulation :=
  linear_of_sweep_xr hS DrvX.extractRamSpec hRL

/-- **Reduction of the main theorem** to the sweep and one step of the region loop
(`DrvB.RegStepSpec`), via the region loop `DrvB.regLoopSpec_of`. -/
theorem linear_of_sweep_regStep (hS : SweepSpecH) {s : Machine.Stmt} {κR : ℕ}
    (hR : DrvB.RegStepSpec s κR) : LinearTimeTriangulation :=
  linear_of_sweep_reg hS (DrvB.regLoopSpec_of hR)

/-- **Reduction of the main theorem** to the sweep and the host expansion `DrvB.ExpSpec` of the
base case (the region step from `DrvB.regStepSpec_of` with the host RAM `DrvH.hostRamSpec`). -/
theorem linear_of_sweep_exp (hS : SweepSpecH) (hE : DrvB.ExpSpec) : LinearTimeTriangulation := by
  obtain ⟨s, κ, hR⟩ := DrvB.regStepSpec_of DrvH.hostRamSpec hE
  exact linear_of_sweep_regStep hS hR

/-- **Reduction of the main theorem to the sweep alone**: the down phase is fully proved
(`DrvB.expSpec`). -/
theorem linear_of_sweep (hS : SweepSpecH) : LinearTimeTriangulation :=
  linear_of_sweep_exp hS DrvB.expSpec
theorem linear_of_open (hStop : SweepEv.StopTask) (hWin : SweepEv.WinTask)
    (hKey : SweepEv.KeyTask) (hL0 : SweepEv.LoopStartTask) (hL1 : SweepEv.StepTask)
    (h0 : SweepIo.Cand0Spec) : LinearTimeTriangulation :=
  linear_of_sweep (SweepIo.sweepSpecH_of (SweepEv.sweepEvSpec_of_rest hStop hWin hKey hL0 hL1) h0
    (SweepIo.cand1Spec SweepIo.bruteSpec))

/-- **Reduction of the main theorem** after the window (`SweepEv.winTask`) and the next key
(`SweepEv.keyTask`): the stops, the start of the loop, one iteration and the side-0 candidates. -/
theorem linear_of_rest (hStop : SweepEv.StopTask) (hL0 : SweepEv.LoopStartTask)
    (hL1 : SweepEv.StepTask) (h0 : SweepIo.Cand0Spec) : LinearTimeTriangulation :=
  linear_of_open hStop SweepEv.winTask SweepEv.keyTask hL0 hL1 h0

/-- **Reduction of the main theorem** after one iteration (`SweepEv.stepTask`): the stops, the
start of the loop and the side-0 candidates. -/
theorem linear_of_three (hStop : SweepEv.StopTask) (hL0 : SweepEv.LoopStartTask)
    (h0 : SweepIo.Cand0Spec) : LinearTimeTriangulation :=
  linear_of_rest hStop hL0 SweepEv.stepTask h0

/-- **Reduction of the main theorem** after the side-0 candidates (`SweepIo.cand0Spec_of` with
`SweepIo.s0CandSpec` and `SweepIo.lab0`): the stops and the start of the loop. -/
theorem linear_of_two (hStop : SweepEv.StopTask) (hL0 : SweepEv.LoopStartTask) :
    LinearTimeTriangulation :=
  linear_of_three hStop hL0 (SweepIo.cand0Spec_of SweepIo.s0CandSpec SweepIo.lab0)

/-- **Reduction of the main theorem to the stops** (`SweepEv.StopTask`), the last open piece
of the sweep. -/
theorem linear_of_stops (hStop : SweepEv.StopTask) : LinearTimeTriangulation :=
  linear_of_two hStop SweepEv.loopStartTask

/-- **Reduction of the main theorem** to the per-origin step of the stops and their sort. -/
theorem linear_of_org_sort (hO : SweepEv.OrgTask) (hS : SweepEv.SortTask) :
    LinearTimeTriangulation :=
  linear_of_stops (SweepEv.stopTask_of hO hS)

/-- **Reduction of the main theorem to the per-origin step of the stops** (`SweepEv.OrgTask`),
the sort being proved (`SweepEv.sortTask`). -/
theorem linear_of_org (hO : SweepEv.OrgTask) : LinearTimeTriangulation :=
  linear_of_org_sort hO SweepEv.sortTask

/-- **Reduction of the main theorem to the final step of a stop origin** (`SweepEv.FinTask`):
the per-origin step is `SweepEv.orgTask_of'` with the two candidates `SweepEv.m2Task`,
`SweepEv.m1Task`. -/
theorem linear_of_fin (hF : SweepEv.FinTask) : LinearTimeTriangulation :=
  linear_of_org (SweepEv.orgTask_of' SweepEv.m2Task SweepEv.m1Task hF)
theorem linearTimeTriangulation : LinearTimeTriangulation :=
  linear_of_fin SweepEv.finTask
