module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoS0CandBsSpec

/-!
# The sweep RAM (WP-D), answers: the binary search in the event log, the program

`lsearch`: a lifting search over the powers of two (table `TBR`, `TLR` entries).  Registers
(`sw 4000 + i`): `0` the answer `i`, `1` the exponent `k`, `2` the table pointer, `3` the power
`p = 2^k`, `4` the candidate `i + p`, `5` its record index `i + p - 1`, `6 … 9` multiples,
`11` the record address, `12`, `13` the record key, `14`, `15` the bits of `offCmp`, `16` the
room `E - i`.  One step: `k := k - 1`; if `p ≤ E - i`, compare the key of record `i + p - 1`
with the target (`callOff`) and, if it is smaller, `i := i + p`.

Straight-line pieces: `lsInit_exec`, `lsB1_exec`, `lsB2_exec`, `lsB3_exec`.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim

@[expose] public section

/-- `i := 0`, `k := TLR`. -/
def lsInit : Stmt := block [.constN 244000 0, .copyN 244001 240601]

/-- `k := k - 1`, `p := 2^k`, `E - i`. -/
def lsB1 : Stmt := block [.subN 244001 244001 240611, .addN 244002 240600 244001,
  .loadN 244003 244002, .subN 244016 240301 244000]

/-- The candidate and the key of its record. -/
def lsB2 : Stmt := block [.addN 244004 244000 244003, .subN 244005 244004 240611,
  .addN 244006 244005 244005, .addN 244007 244006 244006, .addN 244008 244007 244006,
  .addN 244009 244008 244005, .addN 244011 240300 244009, .loadN 244012 244011,
  .addN 244011 244011 240611, .loadN 244013 244011]

/-- Accept the candidate. -/
def lsB3 : Stmt := block [.copyN 244000 244004]

/-- The test of a candidate. -/
def lsTest : Stmt :=
  .seq lsB2 (.seq (callOff 240002 244012 244013 244020 244021 240040 244014)
    (.ifLtN 240610 244014 lsB3 .skip))

/-- One step of the search. -/
def lsBody : Stmt := .seq lsB1 (.ifLtN 244016 244003 .skip lsTest)

/-- **The binary search in the log.** -/
def lsearchS : Stmt := .seq lsInit (.whileLtN 240610 244001 lsBody)

/-- The registers of the search. -/
def LB (r : ℕ) : Bool := decide (244000 ≤ r ∧ r ≤ 244019)

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
theorem lsInit_exec (d : Config) (hw : WordsBounded W d) :
    ∃ d' k, Exec P W lsInit d d' k ∧ k = 2 ∧ d'.nreg 244000 = 0 ∧
      d'.nreg 244001 = d.nreg 240601 ∧ (∀ r, LB r = false → d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨d', k, ex, hk, q1, q2⟩ : ∃ d' k, Exec P W lsInit d d' k ∧ k = 2 ∧
      d'.nreg 244000 = 0 ∧ d'.nreg 244001 = d.nreg 240601 := by
    unfold lsInit
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, ?_⟩ <;> config_simp
  have hf := SignK.exec_frameB ex (B := LB) (⌖)
  exact ⟨d', k, ex, hk, q1, q2, hf.1, funext fun r => WalkKey.exec_rframe ex
    (B := fun _ => false) (⌖) r rfl, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

set_option maxHeartbeats 1000000 in
theorem lsB1_exec (d : Config) (hw : WordsBounded W d) {I KK TB E : ℕ}
    (h00 : d.nreg 244000 = I) (h01 : d.nreg 244001 = KK) (hTB : d.nreg 240600 = TB)
    (hE : d.nreg 240301 = E) (hK1 : d.nreg 240611 = 1) (hW : TB + KK ≤ W) :
    ∃ d' k, Exec P W lsB1 d d' k ∧ k = 4 ∧ d'.nreg 244001 = KK - 1 ∧
      d'.nreg 244003 = d.nmem (TB + (KK - 1)) ∧ d'.nreg 244016 = E - I ∧ d'.nreg 244000 = I ∧
      (∀ r, LB r = false → d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨d', k, ex, hk, q1, q2, q3, q4⟩ : ∃ d' k, Exec P W lsB1 d d' k ∧ k = 4 ∧
      d'.nreg 244001 = KK - 1 ∧ d'.nreg 244003 = d.nmem (TB + (KK - 1)) ∧
      d'.nreg 244016 = E - I ∧ d'.nreg 244000 = I := by
    unfold lsB1
    exec_block
    all_goals try (config_simp; (try simp only [h00, h01, hTB, hE, hK1]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> simp only [h00, h01, hTB, hE, hK1]
  have hf := SignK.exec_frameB ex (B := LB) (⌖)
  exact ⟨d', k, ex, hk, q1, q2, q3, q4, hf.1, funext fun r => WalkKey.exec_rframe ex
    (B := fun _ => false) (⌖) r rfl, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

set_option maxHeartbeats 2000000 in
theorem lsB2_exec (d : Config) (hw : WordsBounded W d) {I Pv E AL : ℕ}
    (h00 : d.nreg 244000 = I) (h03 : d.nreg 244003 = Pv) (hAL : d.nreg 240300 = AL)
    (hK1 : d.nreg 240611 = 1) (hle : I + Pv ≤ E) (hpos : 1 ≤ I + Pv) (hW : AL + 7 * E ≤ W) :
    ∃ d' k, Exec P W lsB2 d d' k ∧ k = 10 ∧ d'.nreg 244004 = I + Pv ∧
      d'.nreg 244012 = d.nmem (AL + 7 * (I + Pv - 1)) ∧
      d'.nreg 244013 = d.nmem (AL + 7 * (I + Pv - 1) + 1) ∧ d'.nreg 244000 = I ∧
      d'.nreg 244001 = d.nreg 244001 ∧ (∀ r, LB r = false → d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨d', k, ex, hk, q1, q2, q3, q4, q5⟩ : ∃ d' k, Exec P W lsB2 d d' k ∧ k = 10 ∧
      d'.nreg 244004 = I + Pv ∧ d'.nreg 244012 = d.nmem (AL + 7 * (I + Pv - 1)) ∧
      d'.nreg 244013 = d.nmem (AL + 7 * (I + Pv - 1) + 1) ∧ d'.nreg 244000 = I ∧
      d'.nreg 244001 = d.nreg 244001 := by
    unfold lsB2
    exec_block
    all_goals try (config_simp; (try simp only [h00, h03, hAL, hK1]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h00, h03, hAL, hK1])
    · congr 1; omega
    · congr 1; omega
  have hf := SignK.exec_frameB ex (B := LB) (⌖)
  exact ⟨d', k, ex, hk, q1, q2, q3, q4, q5, hf.1, funext fun r => WalkKey.exec_rframe ex
    (B := fun _ => false) (⌖) r rfl, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

theorem lsB3_exec (d : Config) (hw : WordsBounded W d) :
    ∃ d' k, Exec P W lsB3 d d' k ∧ k = 1 ∧ d'.nreg 244000 = d.nreg 244004 ∧
      d'.nreg 244001 = d.nreg 244001 ∧ (∀ r, LB r = false → d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨d', k, ex, hk, q1, q2⟩ : ∃ d' k, Exec P W lsB3 d d' k ∧ k = 1 ∧
      d'.nreg 244000 = d.nreg 244004 ∧ d'.nreg 244001 = d.nreg 244001 := by
    unfold lsB3
    exec_block
    refine ⟨rfl, ?_, ?_⟩ <;> config_simp
  have hf := SignK.exec_frameB ex (B := LB) (⌖)
  exact ⟨d', k, ex, hk, q1, q2, hf.1, funext fun r => WalkKey.exec_rframe ex
    (B := fun _ => false) (⌖) r rfl, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

end exec

end

end S0C

end SweepIo

end Chazelle.Core
