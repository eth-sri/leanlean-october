module

public import Chazelle.Core.SweepIoS0CandInitMath2
public import Chazelle.Core.SweepEvOrg
public import Chazelle.Core.SweepEvPrep

/-!
# The sweep RAM (WP-D), answers: the slot table of the side-0 candidates (the program)

`initC ls` (for a binary search `ls` in the log, `LSearchSpec`):

1. `hdr`: the slot base `ipB := ALLOC`, the end `pT := ALLOC + 6 E` of the slot table, the
   counters, `K₂`, `2 m₂ + 5` and `6 + midT C₂` (from the descriptor of `C₂` at `sw 21`);
2. `SweepEv.zeroLoop`: zero the `6 E` words of the slot table (allocating them);
3. `stLoop ls`: for every stop record, its origin position by its kind (`stOrg`, `orgHead` for
   the ends of chords), the search of its key, and the write of the slot (`slotSt`);
4. `tbLoop ls`: for every chord `k < K₂` and `s = 0, 1` with table flag `1`, the end position
   (`orgHead`), the class test (`cls`), and for a regular entry the search of its position and
   the write of the slot;
5. `sw 620 := ipB`.

Registers `sw 4100 … 4129` (and the target `sw 4020`, `sw 4021` of the search, `pT`, and the
registers of `orgHead`).  Straight-line pieces: `hdrA_irs`, `midS_irs`, `stLd_irs`, `slotSt_irs`,
`tbLd_irs`, `cls_irs`.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv

@[expose] public section

/-! ## Registers -/

def ipB : ℕ := sw 4100
def ipM6 : ℕ := sw 4101
def ipM5 : ℕ := sw 4102
def ipX : ℕ := sw 4103
def ipA : ℕ := sw 4104
def ipK : ℕ := sw 4105
def ipKk : ℕ := sw 4106
def ipBb : ℕ := sw 4107
def ipS : ℕ := sw 4108
def ipE : ℕ := sw 4109
def ipH : ℕ := sw 4110
def ipT : ℕ := sw 4111
def ipJ : ℕ := sw 4112
def ipF : ℕ := sw 4113
def ipV : ℕ := sw 4114
def ipKc : ℕ := sw 4115
def ipTa : ℕ := sw 4120
def ipTm : ℕ := sw 4121
def ipTt : ℕ := sw 4122
def ipTb : ℕ := sw 4123
def ipT2 : ℕ := sw 4124
def ipTM : ℕ := sw 4125

/-! ## The program -/

/-- The head: slot base and end, counters, `K₂`, `2 m₂ + 5`, the fields `m`, `T`, `β` of the
descriptor of `C₂`. -/
def hdrA : List Instr :=
  [.copyN ipB ALLOC, .copyN pT ALLOC, .addN pT pT (sw 301), .addN pT pT (sw 301),
    .addN pT pT (sw 301), .addN pT pT (sw 301), .addN pT pT (sw 301), .addN pT pT (sw 301),
    .constN ipX 0, .constN ipJ 0, .loadN ipKc (sw 4), .subN ipM5 (sw 34) K2,
    .addN ipTa (sw 21) K2, .loadN ipTm ipTa, .addN ipTa (sw 21) K3, .loadN ipTt ipTa,
    .addN ipTa (sw 21) K4, .loadN ipTb ipTa]

/-- `midT` without the bit. -/
def ipMidF : Stmt := .ifLtN ipTt ipTm (.instr (.addN ipTM ipTt ipTt)) (.instr (.constN ipTM 0))

/-- `midT` with the bit. -/
def ipMidB : List Instr := [.addN ipT2 ipTm ipTm, .subN ipTM ipT2 ipTt, .subN ipTM ipTM ipTt]

/-- `midT C₂` into `ipTM`. -/
def ipMidS : Stmt := .ifLtN ipTb K1 ipMidF (.ifLtN K1 ipTb ipMidF (block ipMidB))

/-- **The head.** -/
def hdr : Stmt := .seq (block hdrA) (.seq ipMidS (.instr (.addN ipM6 ipTM K6)))

/-- Read stop record `x`: its key into the target of the search, kind, chord, direction bit, and
the slot `1 - b`. -/
def stLd : List Instr :=
  [.addN ipA ipX ipX, .addN ipA ipA ipA, .addN ipA ipA ipX, .addN ipA ipA (sw 200),
    .loadN lsxE ipA, .addN ipA ipA K1, .loadN lsxH ipA, .addN ipA ipA K1, .loadN ipK ipA,
    .addN ipA ipA K1, .loadN ipKk ipA, .addN ipA ipA K1, .loadN ipBb ipA, .subN ipS K1 ipBb]

/-- The origin position of a stop record by its kind. -/
def stOrg : Stmt :=
  .ifLtN ipK K1 (block [.copyN ipE (sw 41), .constN ipH 0])
    (.ifLtN ipK K2
      (.seq (block [.copyN oK ipKk, .copyN oS ipS])
        (.seq orgHead (block [.copyN ipE oE, .copyN ipH oC])))
      (block [.copyN ipE K6, .constN ipH 0]))

/-- The slot address `B + 6 t + 3 s`. -/
def slotAd : List Instr :=
  [.addN ipT lsI lsI, .addN ipT ipT lsI, .addN ipT ipT ipT, .addN ipT ipT ipB,
    .addN ipT ipT ipS, .addN ipT ipT ipS, .addN ipT ipT ipS]

/-- **Write the slot** `(lsI, ipS)` with `(1, ipE, ipH)`. -/
def slotSt : Stmt :=
  .seq (block slotAd) (.seq (.instr (.storeN ipT K1)) (.seq (.instr (.addN ipT ipT K1))
    (.seq (.instr (.storeN ipT ipE)) (.seq (.instr (.addN ipT ipT K1))
      (.instr (.storeN ipT ipH))))))

/-- One stop record. -/
def stB (ls : Stmt) : Stmt :=
  .seq (block stLd) (.seq stOrg (.seq ls (.seq slotSt (.instr (.addN ipX ipX K1)))))

/-- **The stop loop.** -/
def stLoop (ls : Stmt) : Stmt := .whileLtN ipX (sw 201) (stB ls)

/-- Read the table flag of entry `j = 2 k + s` (`s` the value of the register `sr`). -/
def tbLd (sr : ℕ) : List Instr :=
  [.copyN ipS sr, .addN ipA ipJ ipJ, .addN ipA ipA ipS, .addN ipT ipA ipA, .addN ipA ipT ipA,
    .addN ipA ipA (sw 302), .loadN ipF ipA]

def setV (v : ℕ) : Stmt := .instr (.constN ipV v)

/-- `if a = b then t else e`. -/
def ipEqT (a b : ℕ) (t e : Stmt) : Stmt := .ifLtN a b e (.ifLtN b a e t)

/-- **The class test** of the normalised end position `(oE, oC)`: `ipV = 1` iff regular. -/
def cls : Stmt :=
  .ifLtN oE K6 (setV 0)
    (.ifLtN ipM5 oE (setV 0)
      (.ifLtN K0 oC (setV 1)
        (ipEqT oE K6 (setV 0) (ipEqT oE (sw 41) (setV 0) (ipEqT oE ipM6 (setV 0) (setV 1))))))

/-- Read the target of a table entry and copy the origin. -/
def tbTg : List Instr :=
  [.copyN ipE oE, .copyN ipH oC, .addN ipA ipA K1, .loadN lsxE ipA, .addN ipA ipA K1,
    .loadN lsxH ipA]

section
variable (ls : Stmt)
include ls
/-- A table entry with flag `1`. -/
def tbHit : Stmt :=
  .seq (block [.copyN oK ipJ, .copyN oS ipS]) (.seq orgHead (.seq cls
    (.ifLtN ipV K1 .skip (.seq (block tbTg) (.seq ls slotSt)))))

/-- The table entry `2 k + s`. -/
def tbOne (sr : ℕ) : Stmt := .seq (block (tbLd sr)) (.ifLtN ipF K1 .skip (tbHit ls))

/-- One chord. -/
def tbB : Stmt := .seq (tbOne ls K0) (.seq (tbOne ls K1) (.instr (.addN ipJ ipJ K1)))

/-- **The table loop.** -/
def tbLoop : Stmt := .whileLtN ipJ ipKc (tbB ls)

/-- **The initialisation.** -/
def initC : Stmt :=
  .seq (.seq hdr (.seq zeroLoop (.seq (stLoop ls) (tbLoop ls)))) (.instr (.copyN sB ipB))


end

end

end S0C

end SweepIo

end Chazelle.Core
