module

public import Chazelle.Core.OutputTrap
public import Chazelle.Core.SignKernelRam
public import Chazelle.Core.Setup
public import Chazelle.Final.RamOrient

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

/-! ## Index arithmetic on the machine -/

/-- `d := wv b n s` (reversal flag in `220003`, `n - 1` in `220017`, `0` in `220002`). -/
def wvS (d s : ℕ) : Stmt := .ifLtN 220002 220003 (.instr (.subN d 220017 s)) (.instr (.copyN d s))

/-- `d := nxt n s` (`n` in `220000`, `1` in `220001`). -/
def nxtS (d s : ℕ) : Stmt :=
  .seq (.instr (.addN d s 220001)) (.ifLtN d 220000 .skip (.instr (.constN d 0)))

/-- `d := inp b n s` (temporary `220116`, `n - 2` in `220018`). -/
def inpS (d s : ℕ) : Stmt :=
  .ifLtN 220002 220003
    (.seq (.instr (.addN 220116 s 220001))
      (.ifLtN 220116 220000 (.instr (.subN d 220018 s)) (.instr (.copyN d 220017))))
    (.instr (.copyN d s))

/-- The constants of the index arithmetic hold. -/
def ArithRegs (c : Config) (b : Bool) (n : ℕ) : Prop :=
  c.nreg 220000 = n ∧ c.nreg 220001 = 1 ∧ c.nreg 220002 = 0 ∧ c.nreg 220003 = b.toNat ∧
    c.nreg 220017 = n - 1 ∧ c.nreg 220018 = n - 2

section helpers

variable {P : Polygon} {W : ℕ}

/-- Spec of `wvS`: cost `≤ 3`, `d := wv b n s`. -/
theorem wvS_spec {c : Config} (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (d s : ℕ) :
    ∃ c' k, Exec P W (wvS d s) c c' k ∧ k ≤ 3 ∧
      c' = { c with nreg := upd c.nreg d (wv b n (c.nreg s)) } := by
  obtain ⟨-, -, h2, h3, h17, -⟩ := hA
  unfold wvS
  cases b
  · refine spec_ifLtN_false (by rw [h2, h3]; decide) (spec_instr (Exec.copyN hc d s) fun _ => ?_)
    exact ⟨by omega, by simp [wv]⟩
  · refine spec_ifLtN_true (by rw [h2, h3]; decide) (spec_instr (Exec.subN hc d 220017 s) fun _ => ?_)
    exact ⟨by omega, by simp [wv, h17]⟩

/-- Spec of `nxtS`: cost `≤ 4`, `d := nxt n s`. -/
theorem nxtS_spec {c : Config} (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (d s : ℕ) (hd0 : d ≠ 220000) (_hd1 : d ≠ 220001) (hs : c.nreg s < n) (hn : n ≤ W) :
    ∃ c' k, Exec P W (nxtS d s) c c' k ∧ k ≤ 4 ∧
      c' = { c with nreg := upd c.nreg d (nxt n (c.nreg s)) } := by
  obtain ⟨h0, h1, -, -, -, -⟩ := hA
  unfold nxtS
  refine spec_seq (spec_instr (Exec.addN hc d s 220001 (by rw [h1]; omega)) fun hw₁ => ?_)
  by_cases hlt : c.nreg s + 1 < n
  · refine spec_ifLtN_true (by
      simp only [Machine.upd_same, Machine.upd_other _ _ _ (Ne.symm hd0), h0, h1]
      exact hlt) (spec_skip hw₁ ?_)
    refine ⟨by omega, ?_⟩
    simp [nxt, hlt, h1]
  · refine spec_ifLtN_false (by
      simp only [Machine.upd_same, Machine.upd_other _ _ _ (Ne.symm hd0), h0, h1]
      exact hlt) (spec_instr (Exec.constN hw₁ d 0 (Nat.zero_le _)) fun _ => ?_)
    refine ⟨by omega, ?_⟩
    simp [nxt, hlt]

/-- Spec of `inpS`: cost `≤ 6`, `d := inp b n s`; only `d` and `220116` written. -/
theorem inpS_spec {c : Config} (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (d s : ℕ) (_hd : d ≠ 220116) (hsX : s ≠ 220116) (hs : c.nreg s < n) (hn : n ≤ W) :
    ∃ c' k, Exec P W (inpS d s) c c' k ∧ k ≤ 6 ∧ c'.nreg d = inp b n (c.nreg s) ∧
      SignK.FrameB (fun r => decide (r = d ∨ r = 220116)) c c' := by
  obtain ⟨h0, h1, h2, h3, h17, h18⟩ := hA
  unfold inpS
  cases b
  · refine spec_ifLtN_false (by rw [h2, h3]; decide) (spec_instr (Exec.copyN hc d s) fun _ => ?_)
    refine ⟨by omega, by simp [inp], fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    simp only [decide_eq_false_iff_not, not_or] at hr
    simp [hr.1]
  · refine spec_ifLtN_true (by rw [h2, h3]; decide)
      (spec_seq (spec_instr (Exec.addN hc 220116 s 220001 (by rw [h1]; omega)) fun hw₁ => ?_))
    by_cases hlt : c.nreg s + 1 < n
    · refine spec_ifLtN_true (by simp [h0, h1, hlt])
        (spec_instr (Exec.subN hw₁ d 220018 s) fun _ => ?_)
      refine ⟨by omega, ?_, fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      · simp [inp, hlt, h18, hsX]
      · simp only [decide_eq_false_iff_not, not_or] at hr
        simp [hr.1, hr.2]
    · refine spec_ifLtN_false (by simp [h0, h1, hlt])
        (spec_instr (Exec.copyN hw₁ d 220017) fun _ => ?_)
      refine ⟨by omega, ?_, fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      · simp [inp, hlt, h17]
      · simp only [decide_eq_false_iff_not, not_or] at hr
        simp [hr.1, hr.2]

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
  .ifLtN 220107 220010 (block [.constN 220109 1, .copyN 220113 220104])
    (.ifLtN 220010 220107 (block [.constN 220109 1, .copyN 220113 220104])
      (block [.constN 220108 1, .copyN 220112 220104]))

/-- A side end (`wv p ≠ h`?, with `wv p` in `220116`): flag `F`, value `V := S`. -/
def lrS (F V S : ℕ) : Stmt :=
  .ifLtN 220116 220104 (block [.constN F 1, .copyN V S])
    (.ifLtN 220104 220116 (block [.constN F 1, .copyN V S]) .skip)

/-- **The scan of one exit chord.** -/
def chordBody : Stmt :=
  .seq loadS (.seq dnS (.seq (wvS 220116 220105) (.seq (lrS 220110 220114 220105)
    (.seq (wvS 220116 220106) (.seq (lrS 220111 220115 220106)
      (block [.addN 220100 220100 220001]))))))

section chord

variable {P : Polygon} {W : ℕ}

/-- Spec of `dnS`: a top chord sets the top flag and vertex, a bottom chord the bottom ones. -/
theorem dnS_spec {c : Config} (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W dnS c c' k ∧ k ≤ 6 ∧
      c' = if c.nreg 220107 = c.nreg 220010 then
        { c with nreg := upd (upd c.nreg 220108 1) 220112 (c.nreg 220104) }
      else { c with nreg := upd (upd c.nreg 220109 1) 220113 (c.nreg 220104) } := by
  unfold dnS
  rcases lt_trichotomy (c.nreg 220107) (c.nreg 220010) with h | h | h
  · refine spec_ifLtN_true h ?_
    exec_block
    · exact hW
    · exact ⟨by omega, by rw [Setup.iteF h.ne]⟩
  · refine spec_ifLtN_false (by omega) (spec_ifLtN_false (by omega) ?_)
    exec_block
    · exact hW
    · exact ⟨by omega, by rw [Setup.iteT h]⟩
  · refine spec_ifLtN_false (by omega) (spec_ifLtN_true h ?_)
    exec_block
    · exact hW
    · exact ⟨by omega, by rw [Setup.iteF h.ne']⟩

/-- Spec of `lrS`: when `wv p ≠ h`, set the flag `F` and `V := S`. -/
theorem lrS_spec {c : Config} (hc : WordsBounded W c) (hW : 1 ≤ W) (F V S : ℕ) (hSF : S ≠ F) :
    ∃ c' k, Exec P W (lrS F V S) c c' k ∧ k ≤ 6 ∧
      c' = if c.nreg 220116 = c.nreg 220104 then c
      else { c with nreg := upd (upd c.nreg F 1) V (c.nreg S) } := by
  unfold lrS
  rcases lt_trichotomy (c.nreg 220116) (c.nreg 220104) with h | h | h
  · refine spec_ifLtN_true h ?_
    exec_block
    · exact hW
    · refine ⟨by omega, ?_⟩
      rw [Setup.iteF h.ne, Machine.upd_other _ _ _ hSF]
  · refine spec_ifLtN_false (by omega) (spec_ifLtN_false (by omega) (spec_skip hc ?_))
    exact ⟨by omega, by rw [Setup.iteT h]⟩
  · refine spec_ifLtN_false (by omega) (spec_ifLtN_true h ?_)
    exec_block
    · exact hW
    · refine ⟨by omega, ?_⟩
      rw [Setup.iteF h.ne', Machine.upd_other _ _ _ hSF]

end chord

section chord2

variable {P : Polygon} {W : ℕ}

/-- Spec of `loadS`: the record of chord `m (LB + OFF + TI)` is loaded; cost `15`. -/
theorem loadS_spec {c : Config} (hc : WordsBounded W c) {lb off t cb kk : ℕ}
    (h1 : c.nreg 220001 = 1) (h19 : c.nreg 220019 = 2) (hLB : c.nreg 220008 = lb)
    (hOFF : c.nreg 220015 = off) (hTI : c.nreg 220100 = t) (hCB : c.nreg 220006 = cb)
    (hK : c.nmem (lb + off + t) = kk) (hb1 : lb + off + t ≤ W) (hb2 : cb + 5 * kk + 4 ≤ W) :
    ∃ c' k, Exec P W loadS c c' k ∧ k = 15 ∧ c'.nreg 220104 = c.nmem (cb + 5 * kk) ∧
      c'.nreg 220105 = c.nmem (cb + 5 * kk + 1) ∧ c'.nreg 220106 = c.nmem (cb + 5 * kk + 2) ∧
      c'.nreg 220107 = c.nmem (cb + 5 * kk + 4) ∧
      (∀ r, (r < 220101 ∨ 220107 < r) → r ≠ 220117 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold loadS
  exec_block
  all_goals try (config_simp; simp only [hLB, hOFF, hTI, hCB, h1, h19, hK]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr1 hr2 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [hLB, hOFF, hTI, hCB, hK]; congr 1; omega
  · config_simp; simp only [hLB, hOFF, hTI, hCB, hK, h1]; congr 1; omega
  · config_simp; simp only [hLB, hOFF, hTI, hCB, hK, h1]; congr 1; omega
  · config_simp; simp only [hLB, hOFF, hTI, hCB, hK, h1, h19]; congr 1; omega
  · simp (disch := omega) only [Machine.upd_other]

end chord2

section chord3

variable {P : Polygon} {W : ℕ}

/-- The registers the chord scan writes. -/
def scanB (r : ℕ) : Bool := decide (220100 ≤ r ∧ r ≤ 220117)

/-- The chord scan writes only its own registers. -/
theorem wr_chordBody : SignK.wr scanB chordBody = true := by decide

/-- **Spec of the scan of one exit chord.** -/
theorem chordBody_spec {c : Config} (hc : WordsBounded W c) {b : Bool}
    {n ri lb off t cb kk : ℕ} {rec : CRec} {a : Acc}
    (hA : ArithRegs c b n) (h19 : c.nreg 220019 = 2) (hRI : c.nreg 220010 = ri)
    (hLB : c.nreg 220008 = lb) (hOFF : c.nreg 220015 = off) (hTI : c.nreg 220100 = t)
    (hCB : c.nreg 220006 = cb) (hK : c.nmem (lb + off + t) = kk)
    (hrh : c.nmem (cb + 5 * kk) = rec.h) (hrl : c.nmem (cb + 5 * kk + 1) = rec.lp)
    (hrr : c.nmem (cb + 5 * kk + 2) = rec.rp) (hrd : c.nmem (cb + 5 * kk + 4) = rec.dn)
    (hb1 : lb + off + t ≤ W) (hb2 : cb + 5 * kk + 4 ≤ W) (ht : t + 1 ≤ W) (hW : 1 ≤ W)
    (hacc : AccIn c a) :
    ∃ c' k, Exec P W chordBody c c' k ∧ k ≤ 50 ∧ AccIn c' (accStep b n ri a rec) ∧
      c'.nreg 220100 = t + 1 ∧ SignK.FrameB scanB c c' := by
  obtain ⟨hA0, hA1, hA2, hA3, hA17, hA18⟩ := hA
  obtain ⟨c1, k1, e1, hk1, v104, v105, v106, v107, fr1, -, -, -, -⟩ :=
    loadS_spec (P := P) hc hA1 h19 hLB hOFF hTI hCB hK hb1 hb2
  have hw1 := e1.wb_right
  have f1 : ∀ r, (r < 220101 ∨ 220107 < r) → r ≠ 220117 → c1.nreg r = c.nreg r := fr1
  obtain ⟨c2, k2, e2, hk2, hc2⟩ := dnS_spec (P := P) hw1 hW
  have hw2 := e2.wb_right
  have hA2' : ArithRegs c2 b n := by
    subst hc2; split_ifs <;>
    exact ⟨by simp [f1, hA0], by simp [f1, hA1], by simp [f1, hA2], by simp [f1, hA3],
      by simp [f1, hA17], by simp [f1, hA18]⟩
  obtain ⟨c3, k3, e3, hk3, hc3⟩ := wvS_spec (P := P) hw2 hA2' 220116 220105
  have hw3 := e3.wb_right
  obtain ⟨c4, k4, e4, hk4, hc4⟩ := lrS_spec (P := P) hw3 hW 220110 220114 220105 (by decide)
  have hw4 := e4.wb_right
  have hA4 : ArithRegs c4 b n := by
    subst hc4 hc3; split_ifs <;>
    exact ⟨by simp [hA2'.1], by simp [hA2'.2.1], by simp [hA2'.2.2.1], by simp [hA2'.2.2.2.1],
      by simp [hA2'.2.2.2.2.1], by simp [hA2'.2.2.2.2.2]⟩
  obtain ⟨c5, k5, e5, hk5, hc5⟩ := wvS_spec (P := P) hw4 hA4 220116 220106
  have hw5 := e5.wb_right
  obtain ⟨c6, k6, e6, hk6, hc6⟩ := lrS_spec (P := P) hw5 hW 220111 220115 220106 (by decide)
  have hw6 := e6.wb_right
  have hone6 : c6.nreg 220001 = 1 := by
    subst hc6 hc5; split_ifs <;> simp [hA4.2.1]
  have hti6 : c6.nreg 220100 = t := by
    subst hc6 hc5 hc4 hc3 hc2; split_ifs <;> simp [f1, hTI]
  have e7 := Exec.addN (P := P) hw6 220100 220100 220001 (by rw [hone6, hti6]; exact ht)
  have e7' : Exec P W (block [.addN 220100 220100 220001]) c6
      { c6 with nreg := upd c6.nreg 220100 (c6.nreg 220100 + c6.nreg 220001) } 1 :=
    Exec.block_cons e7 (Exec.block_nil e7.wb_right)
  have eall : Exec P W chordBody c _ (k1 + (k2 + (k3 + (k4 + (k5 + (k6 + 1)))))) :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7')))))
  refine ⟨_, _, eall, by omega, ?_, by simp [hone6, hti6], SignK.exec_frameB eall wr_chordBody⟩
  -- the accumulator
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hacc
  have g104 : c1.nreg 220104 = rec.h := by rw [v104, hrh]
  have g105 : c1.nreg 220105 = rec.lp := by rw [v105, hrl]
  have g106 : c1.nreg 220106 = rec.rp := by rw [v106, hrr]
  have g107 : c1.nreg 220107 = rec.dn := by rw [v107, hrd]
  have g010 : c1.nreg 220010 = ri := by rw [f1 _ (by omega) (by omega), hRI]
  have gacc : ∀ r, 220108 ≤ r → r ≤ 220115 → c1.nreg r = c.nreg r :=
    fun r h1 h2 => f1 r (by omega) (by omega)
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
  ((L.take t).map N.chord).foldl (accStep b n ri) Acc.init

/-- One more chord of the list. -/
theorem scanAcc_succ (b : Bool) (n ri : ℕ) (N : NF) (L : List ℕ) {t : ℕ} (ht : t < L.length) :
    scanAcc b n ri N L (t + 1) = accStep b n ri (scanAcc b n ri N L t) (N.chord (L.getD t 0)) := by
  unfold scanAcc
  rw [List.take_add_one, List.map_append, List.foldl_append, List.getElem?_eq_getElem ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

/-- The invariant of the scan loop (`cs` the configuration on entry). -/
def ScanInv (W : ℕ) (b : Bool) (n ri : ℕ) (N : NF) (L : List ℕ) (cs c : Config) : Prop :=
  WordsBounded W c ∧ SignK.FrameB scanB cs c ∧ c.nreg 220100 ≤ L.length ∧
    AccIn c (scanAcc b n ri N L (c.nreg 220100))

/-- **Spec of the scan loop.** -/
theorem chordLoop_spec {cs : Config} {b : Bool} {n ri lb off cb : ℕ} {N : NF} {L : List ℕ}
    (hA : ArithRegs cs b n) (h19 : cs.nreg 220019 = 2) (hRI : cs.nreg 220010 = ri)
    (hLB : cs.nreg 220008 = lb) (hOFF : cs.nreg 220015 = off) (hCB : cs.nreg 220006 = cb)
    (hLEN : cs.nreg 220014 = L.length)
    (hK : ∀ t, t < L.length → cs.nmem (lb + off + t) = L.getD t 0 ∧ lb + off + t ≤ W ∧
      cb + 5 * L.getD t 0 + 4 ≤ W ∧
      cs.nmem (cb + 5 * L.getD t 0) = (N.chord (L.getD t 0)).h ∧
      cs.nmem (cb + 5 * L.getD t 0 + 1) = (N.chord (L.getD t 0)).lp ∧
      cs.nmem (cb + 5 * L.getD t 0 + 2) = (N.chord (L.getD t 0)).rp ∧
      cs.nmem (cb + 5 * L.getD t 0 + 4) = (N.chord (L.getD t 0)).dn)
    (hW : 1 ≤ W) (hI : ScanInv W b n ri N L cs cs) (h0 : cs.nreg 220100 = 0) :
    ∃ c' k, Exec P W chordLoop cs c' k ∧ k ≤ 52 * L.length + 2 ∧
      AccIn c' (scanAcc b n ri N L L.length) ∧ SignK.FrameB scanB cs c' := by
  have hfr : ∀ c : Config, SignK.FrameB scanB cs c → ∀ r, scanB r = false → c.nreg r = cs.nreg r :=
    fun c h r hr => h.1 r hr
  obtain ⟨c', k, he, hI', hex, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 220100) (b := 220014)
    (body := chordBody) (ScanInv W b n ri N L cs) (fun c => L.length - c.nreg 220100) 50
    (fun c h => h.1) (fun c h htest => by
      obtain ⟨hw, hf, hle, hacc⟩ := h
      have g : ∀ r, scanB r = false → c.nreg r = cs.nreg r := hfr c hf
      have e14 : c.nreg 220014 = L.length := by rw [g _ (by decide), hLEN]
      rw [e14] at htest
      set t := c.nreg 220100 with htdef
      obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := hK t htest
      have hm : c.nmem = cs.nmem := hf.2.2.1
      have hA' : ArithRegs c b n := by
        obtain ⟨a0, a1, a2, a3, a17, a18⟩ := hA
        exact ⟨by rw [g _ (by decide), a0], by rw [g _ (by decide), a1], by rw [g _ (by decide), a2],
          by rw [g _ (by decide), a3], by rw [g _ (by decide), a17], by rw [g _ (by decide), a18]⟩
      have hlen : L.length ≤ W := by rw [← e14]; exact hw.1 _
      obtain ⟨c'', k'', e'', hk'', hacc'', ht'', hfr''⟩ := chordBody_spec (P := P) hw hA'
        (by rw [g _ (by decide), h19]) (by rw [g _ (by decide), hRI]) (by rw [g _ (by decide), hLB])
        (by rw [g _ (by decide), hOFF]) rfl (by rw [g _ (by decide), hCB]) (by rw [hm]; exact hk1)
        (by rw [hm]; exact hk4) (by rw [hm]; exact hk5) (by rw [hm]; exact hk6)
        (by rw [hm]; exact hk7) hk2 hk3 (by omega) hW hacc
      refine ⟨c'', k'', e'', ⟨e''.wb_right, hf.trans hfr'', by omega, ?_⟩, hk'', by omega⟩
      rw [ht'', scanAcc_succ b n ri N L htest]
      exact hacc'') hI
  obtain ⟨hw', hf', hle', hacc'⟩ := hI'
  have e14 : c'.nreg 220014 = L.length := by rw [hf'.1 _ (by decide), hLEN]
  rw [e14] at hex
  have ht' : c'.nreg 220100 = L.length := by omega
  refine ⟨c', k, he, ?_, by rw [← ht']; exact hacc', hf'⟩
  rw [h0] at hk
  omega

end loop

/-! ## Completion of the record -/

/-- `d := if flag f then x else (if flag g then wv y else nxt z)`. -/
def pickS (d f x g y z : ℕ) : Stmt :=
  .ifLtN 220002 f (.instr (.copyN d x)) (.ifLtN 220002 g (wvS d y) (nxtS d z))

/-- `d := if flag f then x else wv (nxt z)` (temporary `220117`). -/
def cornerS (d f x z : ℕ) : Stmt :=
  .ifLtN 220002 f (.instr (.copyN d x)) (.seq (nxtS 220117 z) (wvS d 220117))

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

/-- Spec of `pickS`: cost `≤ 8`. -/
theorem pickS_spec {c : Config} (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (hn : n ≤ W) (d f x g y z : ℕ) (hd0 : d ≠ 220000) (hd1 : d ≠ 220001) {bf bg : Bool}
    (hf : c.nreg f = bf.toNat) (hg : c.nreg g = bg.toNat)
    (hz : bf = false → bg = false → c.nreg z < n) :
    ∃ c' k, Exec P W (pickS d f x g y z) c c' k ∧ k ≤ 8 ∧
      c' = { c with nreg := (upd c.nreg d
        (if bf then c.nreg x else if bg then wv b n (c.nreg y) else nxt n (c.nreg z))) } := by
  have h2 := hA.2.2.1
  unfold pickS
  cases bf
  · refine spec_ifLtN_false (by rw [h2, hf]; decide) ?_
    cases bg
    · refine spec_ifLtN_false (by rw [h2, hg]; decide) ?_
      obtain ⟨c', k, e, hk, rfl⟩ := nxtS_spec (P := P) hc hA d z hd0 hd1 (hz rfl rfl) hn
      exact ⟨_, _, e, by omega, by simp⟩
    · refine spec_ifLtN_true (by rw [h2, hg]; decide) ?_
      obtain ⟨c', k, e, hk, rfl⟩ := wvS_spec (P := P) hc hA d y
      exact ⟨_, _, e, by omega, by simp⟩
  · refine spec_ifLtN_true (by rw [h2, hf]; decide) (spec_instr (Exec.copyN hc d x) fun _ => ?_)
    exact ⟨by omega, by simp⟩

/-- Spec of `cornerS`: cost `≤ 9`; only `d` and `220117` written. -/
theorem cornerS_spec {c : Config} (hc : WordsBounded W c) {b : Bool} {n : ℕ} (hA : ArithRegs c b n)
    (hn : n ≤ W) (d f x z : ℕ) (_hd : d ≠ 220117) {bf : Bool} (hf : c.nreg f = bf.toNat)
    (hz : bf = false → c.nreg z < n) :
    ∃ c' k, Exec P W (cornerS d f x z) c c' k ∧ k ≤ 9 ∧
      c'.nreg d = (if bf then c.nreg x else wv b n (nxt n (c.nreg z))) ∧
      SignK.FrameB (fun r => decide (r = d ∨ r = 220117)) c c' := by
  have h2 := hA.2.2.1
  unfold cornerS
  cases bf
  · refine spec_ifLtN_false (by rw [h2, hf]; decide) ?_
    obtain ⟨c1, k1, e1, hk1, rfl⟩ := nxtS_spec (P := P) hc hA 220117 z (by decide) (by decide)
      (hz rfl) hn
    have hA1 : ArithRegs { c with nreg := upd c.nreg 220117 (nxt n (c.nreg z)) } b n := by
      obtain ⟨a0, a1, a2, a3, a17, a18⟩ := hA
      exact ⟨by simp [a0], by simp [a1], by simp [a2], by simp [a3], by simp [a17], by simp [a18]⟩
    obtain ⟨c2, k2, e2, hk2, rfl⟩ := wvS_spec (P := P) e1.wb_right hA1 d 220117
    refine ⟨_, _, e1.seq e2, by omega, by simp, fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    simp only [decide_eq_false_iff_not, not_or] at hr
    simp [hr.1, hr.2]
  · refine spec_ifLtN_true (by rw [h2, hf]; decide) (spec_instr (Exec.copyN hc d x) fun _ => ?_)
    refine ⟨by omega, by simp, fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    simp only [decide_eq_false_iff_not, not_or] at hr
    simp [hr.1]

end fin

section fin2

variable {P : Polygon} {W : ℕ}

/-- The registers the completion writes. -/
def finB (r : ℕ) : Bool := decide (220116 ≤ r ∧ r ≤ 220125)

/-- The completion writes only its own registers. -/
theorem wr_finS : SignK.wr finB finS = true := by decide

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
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hacc
  have hn1 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hpl
  set PLv := (if a.hL then a.pl else if a.hT then wv b n a.vt else nxt n a.pr) with hPLv
  have hPL : PLv < n := by
    rw [hPLv]; split_ifs
    · exact hpl
    · exact wv_lt hvt
    · exact nxt_lt hpr
  set PRv := (if a.hR then a.pr else if a.hB then wv b n a.vb else nxt n PLv) with hPRv
  have hPR : PRv < n := by
    rw [hPRv]; split_ifs
    · exact hpr
    · exact wv_lt hvb
    · exact nxt_lt hPL
  -- stage 1
  obtain ⟨c1, k1, e1, hk1, hc1⟩ := pickS_spec (P := P) hc hA hn 220120 220110 220114 220108 220112
    220115 (by decide) (by decide) a3 a1 (fun _ _ => by rw [a8]; exact hpr)
  have v1 : c1.nreg 220120 = PLv := by rw [hc1]; simp [a7, a5, a8, hPLv]
  have hA1 : ArithRegs c1 b n := by
    obtain ⟨b0, b1, b2, b3, b17, b18⟩ := hA
    rw [hc1]; exact ⟨by simp [b0], by simp [b1], by simp [b2], by simp [b3], by simp [b17],
      by simp [b18]⟩
  -- stage 2
  obtain ⟨c2, k2, e2, hk2, hc2⟩ := pickS_spec (P := P) (bf := a.hR) (bg := a.hB) e1.wb_right hA1
    hn 220121 220111 220115 220109 220113 220120 (by decide) (by decide) (by rw [hc1]; simp [a4])
    (by rw [hc1]; simp [a2]) (fun _ _ => by rw [v1]; exact hPL)
  have v2 : c2.nreg 220121 = PRv := by
    rw [hc2]; simp only [Machine.upd_same]; rw [v1, hc1]; simp [a8, a6, hPRv]
  have v2' : c2.nreg 220120 = PLv := by rw [hc2]; simp [v1]
  have hA2 : ArithRegs c2 b n := by
    obtain ⟨b0, b1, b2, b3, b17, b18⟩ := hA1
    rw [hc2]; exact ⟨by simp [b0], by simp [b1], by simp [b2], by simp [b3], by simp [b17],
      by simp [b18]⟩
  have g2 : ∀ r, r ≠ 220120 → r ≠ 220121 → c2.nreg r = c.nreg r := fun r h1 h2 => by
    rw [hc2, hc1]; simp [h1, h2]
  -- stage 3
  obtain ⟨c3, k3, e3, hk3, v3, f3⟩ := cornerS_spec (P := P) e2.wb_right hA2 hn 220122 220108
    220112 220121 (by decide) (by rw [g2 _ (by decide) (by decide)]; exact a1)
    (fun _ => by rw [v2]; exact hPR)
  have hA3 := hA2.frame f3 rfl rfl rfl rfl rfl rfl
  -- stage 4
  obtain ⟨c4, k4, e4, hk4, v4, f4⟩ := cornerS_spec (P := P) e3.wb_right hA3 hn 220123 220109
    220113 220120 (by decide) (by rw [f3.1 _ rfl, g2 _ (by decide) (by decide)]; exact a2)
    (fun _ => by rw [f3.1 _ rfl, v2']; exact hPL)
  have hA4 := hA3.frame f4 rfl rfl rfl rfl rfl rfl
  -- stage 5, 6
  obtain ⟨c5, k5, e5, hk5, v5, f5⟩ := inpS_spec (P := P) e4.wb_right hA4 220124 220120 (by decide)
    (by decide) (by rw [f4.1 _ rfl, f3.1 _ rfl, v2']; exact hPL) hn
  have hA5 := hA4.frame f5 rfl rfl rfl rfl rfl rfl
  obtain ⟨c6, k6, e6, hk6, v6, f6⟩ := inpS_spec (P := P) e5.wb_right hA5 220125 220121 (by decide)
    (by decide) (by rw [f5.1 _ rfl, f4.1 _ rfl, f3.1 _ rfl, v2]; exact hPR) hn
  have eall : Exec P W finS c c6 (k1 + (k2 + (k3 + (k4 + (k5 + k6))))) :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
  refine ⟨c6, _, eall, by omega, ?_, ?_, ?_, ?_, SignK.exec_frameB eall wr_finS⟩
  · rw [f6.1 220124 rfl, v5, f4.1 220120 rfl, f3.1 220120 rfl, v2']
    simp only [finish, hPLv]
  · rw [v6, f5.1 220121 rfl, f4.1 220121 rfl, f3.1 220121 rfl, v2]
    simp only [finish, hPRv, hPLv]
  · rw [f6.1 220122 rfl, f5.1 220122 rfl, f4.1 220122 rfl, v3, v2,
      g2 220112 (by decide) (by decide), a5]
    simp only [finish, hPRv, hPLv]
  · rw [f6.1 220123 rfl, f5.1 220123 rfl, v4, f3.1 220113 rfl, f3.1 220120 rfl, v2',
      g2 220113 (by decide) (by decide), a6]
    simp only [finish, hPLv]

end fin2

/-! ## Reading a robust normal form -/

/-- The memory `m` below `A`, the constant `X` above. -/
def mX (A : ℕ) (m : ℕ → ℕ) (X : ℕ) (y : ℕ) : ℕ := if y < A then m y else X

/-- `mX` below `A`. -/
theorem mX_of_lt {A : ℕ} {m : ℕ → ℕ} {X y : ℕ} (h : y < A) : mX A m X y = m y := by
  simp [mX, h]

/-- `mX` at or above `A`. -/
theorem mX_of_ge {A : ℕ} {m : ℕ → ℕ} {X y : ℕ} (h : A ≤ y) : mX A m X y = X := by
  simp [mX, not_lt.2 h]

/-- The facts of a normal form in memory that the output program reads, with the addresses it
computes below `A`. -/
structure NFReads (m : ℕ → ℕ) (A B : ℕ) (N : NF) : Prop where
  nr : m (B + 2) = N.nRegions ∧ B + 2 < A
  regs : ∀ r, r < N.nRegions →
    m (m (B + 5) + 5 * r + 2) = (N.region r).chords.length ∧ m (B + 5) + 5 * r + 2 < A
  lists : ∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
    m (m (B + 7) + m (m (B + 5) + 5 * r + 3) + t) = (N.region r).chords.getD t 0 ∧
      m (B + 7) + m (m (B + 5) + 5 * r + 3) + t < A ∧ m (B + 5) + 5 * r + 3 < A
  chords : ∀ k, k < N.nChords →
    m (m (B + 3) + 5 * k) = (N.chord k).h ∧ m (m (B + 3) + 5 * k + 1) = (N.chord k).lp ∧
      m (m (B + 3) + 5 * k + 2) = (N.chord k).rp ∧ m (m (B + 3) + 5 * k + 4) = (N.chord k).dn ∧
      m (B + 3) + 5 * k + 4 < A

/-- **A robust normal form is read below its bound.** -/
theorem nfReads_of_robust {A B : ℕ} {m : ℕ → ℕ} {N : NF} (h : Robust A m fun m' => NFAt m' B N) :
    NFReads m A B N := by
  have hm := h.holds
  have hX : ∀ X, NFAt (mX A m X) B N := fun X => h _ fun a ha => mX_of_lt ha
  refine ⟨⟨hm.2.2.1, ?_⟩, fun r hr => ⟨(hm.2.2.2.2.2.2.2.1 r hr).2.1, ?_⟩,
    fun r hr t ht => ⟨((hm.2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht).trans rfl, ?_, ?_⟩,
    fun k hk => ⟨(hm.2.2.2.2.2.1 k hk).1, (hm.2.2.2.2.2.1 k hk).2.1, (hm.2.2.2.2.2.1 k hk).2.2.1,
      (hm.2.2.2.2.2.1 k hk).2.2.2.2, ?_⟩⟩
  · by_contra hc; push Not at hc
    have := (hX (N.nRegions + 1)).2.2.1
    rw [mX_of_ge hc] at this; unfold NF.nRegions at this; omega
  · set v := (N.region r).chords.length
    have := ((hX (A + v + 1)).2.2.2.2.2.2.2.1 r hr).2.1
    by_contra hc; push Not at hc
    simp only [mX] at this; split_ifs at this <;> omega
  · set v := (N.region r).chords.getD t 0
    have := ((hX (A + v + 1)).2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht
    by_contra hc; push Not at hc
    simp only [mX] at this; split_ifs at this <;> omega
  · set v := (N.region r).chords.getD t 0
    have := ((hX (A + v + 1)).2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht
    by_contra hc; push Not at hc
    simp only [mX] at this; split_ifs at this <;> omega
  · set v := (N.chord k).dn
    have := ((hX (A + v + 1)).2.2.2.2.2.1 k hk).2.2.2.2
    by_contra hc; push Not at hc
    simp only [mX] at this; split_ifs at this <;> omega

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
def preB (r : ℕ) : Bool := decide (r = 220014 ∨ r = 220015 ∨ (220100 ≤ r ∧ r ≤ 220117))

/-- `regPre` writes only its own registers. -/
theorem wr_regPre : SignK.wr preB regPre = true := by decide

/-- Spec of `regPre`: the length and offset of the chord list of the region, the scan reset; cost `13`. -/
theorem regPre_spec {c : Config} (hc : WordsBounded W c) {ra : ℕ} (h19 : c.nreg 220019 = 2)
    (h20 : c.nreg 220020 = 3) (hRA : c.nreg 220013 = ra) (hb : ra + 3 ≤ W) :
    ∃ c' k, Exec P W regPre c c' k ∧ k = 13 ∧ c'.nreg 220014 = c.nmem (ra + 2) ∧
      c'.nreg 220015 = c.nmem (ra + 3) ∧ c'.nreg 220100 = 0 ∧ AccIn c' Acc.init ∧
      SignK.FrameB preB c c' := by
  have e : ∃ c' k, Exec P W regPre c c' k ∧ k = 13 ∧ c'.nreg 220014 = c.nmem (ra + 2) ∧
      c'.nreg 220015 = c.nmem (ra + 3) ∧ c'.nreg 220100 = 0 ∧ AccIn c' Acc.init := by
    unfold regPre
    exec_block
    all_goals try (config_simp; simp only [hRA, h19, h20]; omega)
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · config_simp; simp only [hRA, h19]
    · config_simp; simp only [hRA, h20]
    · config_simp
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> rfl
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4⟩ := e
  exact ⟨c', k, ex, hk, h1, h2, h3, h4, SignK.exec_frameB ex wr_regPre⟩

/-- Spec of `storeS`: the four words of the record at the output address, the addresses and the allocator advanced; cost `11`. -/
theorem storeS_spec {c : Config} (hc : WordsBounded W c) {o ra ri al : ℕ}
    (h1 : c.nreg 220001 = 1) (h11 : c.nreg 220011 = 4) (h12 : c.nreg 220012 = 5)
    (hO : c.nreg 220016 = o) (hRA : c.nreg 220013 = ra) (hRI : c.nreg 220010 = ri)
    (hAL : c.nreg 9999 = al) (hb1 : o + 4 ≤ W) (hb2 : ra + 5 ≤ W) (hb3 : ri + 1 ≤ W)
    (hb4 : al + 4 ≤ W) :
    ∃ c' k, Exec P W storeS c c' k ∧ k = 11 ∧
      c'.nmem = upd (upd (upd (upd c.nmem o (c.nreg 220124)) (o + 1) (c.nreg 220125)) (o + 2)
        (c.nreg 220122)) (o + 3) (c.nreg 220123) ∧
      c'.nreg 220016 = o + 4 ∧ c'.nreg 220013 = ra + 5 ∧ c'.nreg 220010 = ri + 1 ∧
      c'.nreg 9999 = al + 4 ∧
      (∀ r, r ≠ 220117 → r ≠ 220016 → r ≠ 220013 → r ≠ 220010 → r ≠ 9999 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold storeS
  exec_block
  all_goals try (config_simp; simp only [hO, hRA, hRI, hAL, h1, h11, h12]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [hO, h1]
  · config_simp; simp only [hO, h11]
  · config_simp; simp only [hRA, h12]
  · config_simp; simp only [hRI, h1]
  · config_simp; simp only [hAL, h11]
  · simp (disch := omega) only [Machine.upd_other]

end region

section region2

variable {P : Polygon} {W : ℕ}

/-- The values of the scan stay below `n`. -/
theorem fold_lt (b : Bool) (n ri : ℕ) (L : List CRec) (hL : ∀ c ∈ L, c.h < n ∧ c.lp < n ∧ c.rp < n)
    (a : Acc) (ha : a.vt < n ∧ a.vb < n ∧ a.pl < n ∧ a.pr < n) :
    (L.foldl (accStep b n ri) a).vt < n ∧ (L.foldl (accStep b n ri) a).vb < n ∧
      (L.foldl (accStep b n ri) a).pl < n ∧ (L.foldl (accStep b n ri) a).pr < n := by
  induction L generalizing a with
  | nil => exact ha
  | cons c L ih =>
    simp only [List.foldl_cons]
    apply ih (fun c' hc' => hL c' (List.mem_cons_of_mem _ hc'))
    obtain ⟨h1, h2, h3⟩ := hL c List.mem_cons_self
    obtain ⟨a1, a2, a3, a4⟩ := ha
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [accStep] <;> split_ifs <;> assumption

/-- The scan of the whole list is `accOf`. -/
theorem scanAcc_length (b : Bool) (n ri : ℕ) (N : NF) :
    scanAcc b n ri N (N.region ri).chords (N.region ri).chords.length = accOf b n N ri := by
  unfold scanAcc accOf; rw [List.take_length]

/-- The record `rec` is stored at `A` (four words). -/
def TrapAt (m : ℕ → ℕ) (A : ℕ) (rec : Final.TrapRec) : Prop :=
  m A = rec.left ∧ m (A + 1) = rec.right ∧ m (A + 2) = rec.top ∧ m (A + 3) = rec.bot

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
    (hC : RegConsts c0 b n N.nRegions cb lb T0) (hRd : NFReads m0 T0 B N) (hrb : m0 (B + 5) = rb)
    (hlb : m0 (B + 7) = lb) (hcb : m0 (B + 3) = cb)
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
  have g : ∀ r, regFree r → c.nreg r = c0.nreg r := hfr
  have hAc : ArithRegs c b n := by
    obtain ⟨a0, a1, a2, a3, a17, a18⟩ := hA
    exact ⟨by rw [g _ (by unfold regFree; omega), a0], by rw [g _ (by unfold regFree; omega), a1],
      by rw [g _ (by unfold regFree; omega), a2], by rw [g _ (by unfold regFree; omega), a3],
      by rw [g _ (by unfold regFree; omega), a17], by rw [g _ (by unfold regFree; omega), a18]⟩
  have c19 : c.nreg 220019 = 2 := by rw [g _ (by unfold regFree; omega), h19]
  have c20 : c.nreg 220020 = 3 := by rw [g _ (by unfold regFree; omega), h20]
  have c11 : c.nreg 220011 = 4 := by rw [g _ (by unfold regFree; omega), h4]
  have c12 : c.nreg 220012 = 5 := by rw [g _ (by unfold regFree; omega), h5]
  have c6 : c.nreg 220006 = cb := by rw [g _ (by unfold regFree; omega), hcb']
  have c8 : c.nreg 220008 = lb := by rw [g _ (by unfold regFree; omega), hlb']
  have hT0W : T0 ≤ W := by omega
  obtain ⟨hlenm, hlenA⟩ := hRd.regs ri ht
  rw [hrb] at hlenm hlenA
  -- stage 1
  obtain ⟨c1, k1, e1, hk1, v14, v15, v100, vacc, f1⟩ :=
    regPre_spec (P := P) hw c19 c20 hRA (by omega)
  have hw1 := e1.wb_right
  have g1 : ∀ r, preB r = false → c1.nreg r = c.nreg r := f1.1
  have m1 : c1.nmem = c.nmem := f1.2.2.1
  have hlen1 : c1.nreg 220014 = (N.region ri).chords.length := by rw [v14, hmem _ (by omega), hlenm]
  -- the chord data
  have hK : ∀ t, t < (N.region ri).chords.length → c1.nmem (lb + c1.nreg 220015 + t) = (N.region ri).chords.getD t 0 ∧
      lb + c1.nreg 220015 + t ≤ W ∧ cb + 5 * (N.region ri).chords.getD t 0 + 4 ≤ W ∧
      c1.nmem (cb + 5 * (N.region ri).chords.getD t 0) = (N.chord ((N.region ri).chords.getD t 0)).h ∧
      c1.nmem (cb + 5 * (N.region ri).chords.getD t 0 + 1) = (N.chord ((N.region ri).chords.getD t 0)).lp ∧
      c1.nmem (cb + 5 * (N.region ri).chords.getD t 0 + 2) = (N.chord ((N.region ri).chords.getD t 0)).rp ∧
      c1.nmem (cb + 5 * (N.region ri).chords.getD t 0 + 4) = (N.chord ((N.region ri).chords.getD t 0)).dn := by
    intro t htl
    obtain ⟨l1, l2, l3⟩ := hRd.lists ri ht t htl
    rw [hlb, hrb] at l1 l2
    rw [hrb] at l3
    have hoff : c1.nreg 220015 = m0 (rb + 5 * ri + 3) := by rw [v15, hmem _ l3]
    have hk := hent ri ht t htl
    obtain ⟨q1, q2, q3, q4, q5⟩ := hRd.chords _ hk
    rw [hcb] at q1 q2 q3 q4 q5
    rw [hoff, m1, hmem _ l2, l1, hmem _ (by omega), hmem _ (by omega), hmem _ (by omega),
      hmem _ (by omega)]
    exact ⟨rfl, by omega, by omega, q1, q2, q3, q4⟩
  have hA1 := hAc.frame f1 rfl rfl rfl rfl rfl rfl
  -- stage 2
  obtain ⟨c2, k2, e2, hk2, vacc2, f2⟩ := chordLoop_spec (P := P) (cs := c1) (L := (N.region ri).chords) (N := N)
    (ri := ri) hA1 (by rw [g1 _ rfl, c19]) (by rw [g1 _ rfl]) (by rw [g1 _ rfl, c8]) rfl
    (by rw [g1 _ rfl, c6]) hlen1 hK (by omega)
    ⟨hw1, SignK.FrameB.refl _ _, by rw [v100]; exact Nat.zero_le _, by rw [v100]; exact vacc⟩ v100
  have hw2 := e2.wb_right
  rw [scanAcc_length] at vacc2
  have hA2 := hA1.frame f2 rfl rfl rfl rfl rfl rfl
  -- stage 3
  have hbnd := fold_lt b n ri ((N.region ri).chords.map N.chord) (fun cr hcr => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hcr
      obtain ⟨t, htl, rfl⟩ := List.getElem_of_mem hk
      have e : (N.region ri).chords.getD t 0 = (N.region ri).chords[t] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
      exact e ▸ hrec _ (hent ri ht t htl)) Acc.init
    ⟨hn, hn, hn, hn⟩
  obtain ⟨c3, k3, e3, hk3, v124, v125, v122, v123, f3⟩ := finS_spec (P := P) hw2 hA2
    (by omega) vacc2 hbnd.2.2.1 hbnd.2.2.2 hbnd.1 hbnd.2.1
  have hw3 := e3.wb_right
  -- registers through the three stages
  have gg : ∀ r, preB r = false → scanB r = false → finB r = false → c3.nreg r = c.nreg r :=
    fun r a1 a2 a3 => by rw [f3.1 r a3, f2.1 r a2, f1.1 r a1]
  -- stage 4
  obtain ⟨c4, k4, e4, hk4, m4, v16, v13, v10, v9999, g4, rr4, rm4, o4⟩ := storeS_spec (P := P) hw3
    (o := T0 + 4 * ri) (ra := rb + 5 * ri) (ri := ri) (al := T0 + 4 * ri)
    (by rw [gg _ rfl rfl rfl, hAc.2.1]) (by rw [gg _ rfl rfl rfl, c11])
    (by rw [gg _ rfl rfl rfl, c12]) (by rw [gg _ rfl rfl rfl, hOUT]) (by rw [gg _ rfl rfl rfl, hRA])
    (by rw [gg _ rfl rfl rfl]) (by rw [gg _ rfl rfl rfl, hAL]) (by omega) (by omega) (by omega)
    (by omega)
  have eall : Exec P W regionBody c c4 (k1 + (k2 + (k3 + k4))) := e1.seq (e2.seq (e3.seq e4))
  have hlenL := hlen ri ht
  refine ⟨c4, _, eall, ⟨e4.wb_right, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by omega, v10, by omega⟩
  · unfold regFree at hr
    rw [g4 r (by omega) (by omega) (by omega) (by omega) (by omega),
      gg r (by unfold preB; simp; omega) (by unfold scanB; simp; omega) (by unfold finB; simp; omega)]
    exact g r (by unfold regFree; exact hr)
  · unfold regFree at hr
    rw [rr4, f3.2.1 r (by unfold finB; simp; omega), f2.2.1 r (by unfold scanB; simp; omega),
      f1.2.1 r (by unfold preB; simp; omega)]
    exact hrr r (by unfold regFree; exact hr)
  · rw [rm4, f3.2.2.2.1, f2.2.2.2.1, f1.2.2.2.1, hrm]
  · rw [o4, f3.2.2.2.2, f2.2.2.2.2, f1.2.2.2.2, ho]
  · rw [v10]; omega
  · rw [v13, v10]; ring
  · rw [v16, v10]; ring
  · rw [v9999, v10]; ring
  · intro a ha
    rw [m4]
    simp only [Machine.upd_apply]
    rw [Setup.iteF (by omega), Setup.iteF (by omega), Setup.iteF (by omega), Setup.iteF (by omega),
      f3.2.2.1, f2.2.2.1, m1, hmem a ha]
  · intro s hs
    rw [v10] at hs
    have mem3 : c3.nmem = c.nmem := by rw [f3.2.2.1, f2.2.2.1, m1]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · obtain ⟨t1, t2, t3, t4⟩ := hrecs s hs
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [m4] <;> simp only [Machine.upd_apply] <;>
        rw [Setup.iteF (by omega), Setup.iteF (by omega), Setup.iteF (by omega), Setup.iteF (by omega), mem3] <;>
        assumption
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [m4]
      · simp [v124, trapOf]
      · simp [v125, trapOf]
      · simp [v122, trapOf]
      · simp [v123, trapOf]

end region3

section region4

variable {P : Polygon} {W : ℕ}

/-- **Spec of the region loop.** -/
theorem regionLoop_spec {c0 c : Config} {b : Bool} {n B T0 rb lb cb : ℕ} {N : NF} {m0 : ℕ → ℕ}
    (hC : RegConsts c0 b n N.nRegions cb lb T0) (hRd : NFReads m0 T0 B N) (hrb : m0 (B + 5) = rb)
    (hlb : m0 (B + 7) = lb) (hcb : m0 (B + 3) = cb)
    (hlen : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ 4)
    (hent : ∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
      (N.region r).chords.getD t 0 < N.nChords)
    (hrec : ∀ k, k < N.nChords → (N.chord k).h < n ∧ (N.chord k).lp < n ∧ (N.chord k).rp < n)
    (hn : 1 ≤ n) (hnW : n + 1 ≤ W) (hTW : T0 + 4 * N.nRegions + 8 ≤ W)
    (hI : RegInv W b n N T0 rb m0 c0 c) (h0 : c.nreg 220010 = 0) :
    ∃ c' k, Exec P W regionLoop c c' k ∧ RegInv W b n N T0 rb m0 c0 c' ∧
      c'.nreg 220010 = N.nRegions ∧ k ≤ 332 * N.nRegions + 2 ∧ c'.nreg 9999 ≤ c.nreg 9999 + k := by
  have hnR : ∀ c', RegInv W b n N T0 rb m0 c0 c' → c'.nreg 220005 = N.nRegions := fun c' h => by
    rw [h.2.1 _ (by unfold regFree; omega), hC.2.1]
  obtain ⟨c', k, he, hI', hex, hk, hΨ⟩ := Setup.whileLtN_acc (P := P) (a := 220010) (b := 220005)
    (body := regionBody) (RegInv W b n N T0 rb m0 c0) (fun c => N.nRegions - c.nreg 220010) 330
    (fun c => c.nreg 9999) (fun c h => h.1) (fun c h htest => by
      rw [hnR c h] at htest
      obtain ⟨c'', k'', e'', hI'', hk'', h10, hA⟩ := regionBody_spec (P := P) hC hRd hrb hlb hcb hlen
        hent hrec hn hnW hTW h htest
      exact ⟨c'', k'', e'', hI'', hk'', by omega, hA⟩) hI
  rw [hnR c' hI'] at hex
  have hle := hI'.2.2.2.2.2.1
  refine ⟨c', k, he, hI', by omega, by rw [h0] at hk; omega, hΨ⟩

end region4

end

end Output

end Chazelle.Core
