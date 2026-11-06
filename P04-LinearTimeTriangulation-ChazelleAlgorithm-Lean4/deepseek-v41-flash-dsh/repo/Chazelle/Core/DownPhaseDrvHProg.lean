module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvHItems
public import Chazelle.Core.DownPhaseDrvRLib
public import Chazelle.Core.NFBuildMain

/-!
# Down-phase driver, host RAM (D3a), part 3: the program

Registers (band `bDownDrv`, all in `215000 … 215999`):

* inputs `215000` (NF handle `B`), `215001` (region `r`), `215002` (bit `li`); outputs `215010`
  (host handle), `215011` (item count), `215012` (point count);
* static (written by `setupS` only): `215020 = 1`, `215021 = n`, `215022 = 0`, `215023 = 3`,
  `215024 = 2`, `215025` chord base `CB`, `215026` arc base `AB`, `215027` list base `LB`,
  `215028` offset of the region's arc list, `215029` offset of its chord list, `215030` its
  number of arcs `A`, `215031` its number of exit chords, `215032` the temporary buffer `T`
  (the allocator on entry); setup scratch `215033 … 215035`;
* dynamic: `215040` write pointer, `215041` arc counter `t`, `215042` `(t + 1) mod A`,
  `215043`/`215044` the arcs `jp`/`j`, `215045` scratch address, `215046`/`215047` the end of
  `jp`, `215048`/`215049` the start of `j`, `215050`/`215051` the end of `j`, `215052`/`215053`
  the partner, `215054` found bit, `215055` chord counter, `215056 … 215063` chord scratch,
  `215064`/`215065` the point to emit (edge, height code), `215066 … 215069` emit scratch,
  `215070 … 215076` run scratch (`215072` the end edge, `215073` the run count);
  copy `215080 … 215086`.

Phases: `setupS`; `arcLoop` writes `walkItems` into the buffer at `T` (three words per item);
`finS` puts the host handle after the buffer and writes the count; `cpyLoop` copies the items
(reversed when `li = 0`); `padLoopH` raises the allocator to the end of the host one by one.
-/

namespace Chazelle.Core

namespace DrvH

open Machine Machine.Stmt

@[expose] public section

/-- Setup: constants, NF bases and the region record. -/
def setupS : Stmt := block [
  .constN 215020 1, .inputSize 215021, .constN 215022 0, .constN 215023 3, .constN 215024 2,
  .constN 215033 3, .addN 215033 215000 215033, .loadN 215025 215033,
  .constN 215033 4, .addN 215033 215000 215033, .loadN 215026 215033,
  .constN 215033 5, .addN 215033 215000 215033, .loadN 215034 215033,
  .constN 215033 7, .addN 215033 215000 215033, .loadN 215027 215033,
  .addN 215033 215001 215001, .addN 215033 215033 215033, .addN 215033 215033 215001,
  .addN 215035 215034 215033, .loadN 215030 215035,
  .addN 215033 215035 215020, .loadN 215028 215033,
  .addN 215033 215033 215020, .loadN 215031 215033,
  .addN 215033 215033 215020, .loadN 215029 215033,
  .copyN 215032 9999, .copyN 215040 9999, .constN 215011 0, .constN 215012 0,
  .constN 215041 0]

/-! ## Emitting a point -/

/-- `215066 := qE li n e` for `e` in `215064`. -/
def qES : Stmt :=
  .ifLtN 215022 215002 (block [.copyN 215066 215064])
    (.seq (block [.addN 215069 215064 215020])
      (.ifLtN 215069 215021 (block [.subN 215066 215021 215064, .subN 215066 215066 215024])
        (block [.subN 215066 215021 215020])))

/-- Write the point item `(2, r215066, r215065 - 1)` at the write pointer. -/
def wrPt : Stmt := block [.subN 215068 215065 215020, .storeN 215040 215024,
  .addN 215069 215040 215020, .storeN 215069 215066, .addN 215069 215069 215020,
  .storeN 215069 215068, .addN 215040 215040 215023, .addN 215011 215011 215020,
  .addN 215012 215012 215020]

/-- **Emit the point** `ptE li n e h` (`e` in `215064`, `h` in `215065`). -/
def emitS : Stmt := .seq qES wrPt

/-! ## The run of an arc -/

/-- `215070 := ivB li n e.edge`. -/
def ivS : Stmt := .ifLtN 215022 215002 (block [.copyN 215070 215050])
  (block [.subN 215070 215021 215020, .subN 215070 215070 215050])

/-- `215071 := 0` if `atVtx` else `1`; `215072 :=` the edge of the end point. -/
def atS : Stmt := .seq (block [.subN 215076 215051 215020, .subN 215063 215076 215070,
    .subN 215076 215070 215076, .addN 215063 215063 215076])
  (.ifLtN 215063 215020
    (.seq (block [.constN 215071 0])
      (.ifLtN 215050 215020 (block [.subN 215072 215021 215020])
        (block [.subN 215072 215050 215020])))
    (block [.constN 215071 1, .copyN 215072 215050]))

/-- `215073 := runCnt`. -/
def rcS : Stmt := .seq (block [.addN 215073 215050 215071, .addN 215073 215073 215021,
    .subN 215073 215073 215020, .subN 215073 215073 215048])
  (.ifLtN 215073 215021 .skip (block [.subN 215073 215073 215021]))

/-- `215074 :=` the first vertex of the run. -/
def rsS : Stmt := .ifLtN 215022 215002
  (.seq (block [.addN 215074 215048 215020])
    (.ifLtN 215074 215021 .skip (block [.constN 215074 0])))
  (.seq (block [.addN 215074 215048 215073])
    (.seq (.ifLtN 215074 215021 .skip (block [.subN 215074 215074 215021]))
      (block [.subN 215076 215021 215020, .subN 215074 215076 215074])))

/-- Write the run item `(0, r215074, r215073 - 1)`. -/
def wrRun : Stmt := block [.subN 215075 215073 215020, .storeN 215040 215022,
  .addN 215069 215040 215020, .storeN 215069 215074, .addN 215069 215069 215020,
  .storeN 215069 215075, .addN 215040 215040 215023, .addN 215011 215011 215020,
  .addN 215012 215012 215073]

/-- **The run items** of the arc from `s` (`215048`) to `e` (`215050`, `215051`). -/
def runS : Stmt := .seq ivS (.seq atS (.seq rcS (.ifLtN 215073 215020 .skip (.seq rsS wrRun))))

/-! ## The partner of the end of the previous arc -/

/-- Test the chord at position `r215055` of the region's chord list. -/
def chTest : Stmt := .seq (block [
    .addN 215045 215029 215055, .addN 215045 215027 215045, .loadN 215056 215045,
    .addN 215045 215056 215056, .addN 215045 215045 215045, .addN 215045 215045 215056,
    .addN 215045 215025 215045,
    .loadN 215057 215045, .addN 215057 215057 215020,
    .addN 215045 215045 215020, .loadN 215058 215045, .addN 215045 215045 215020,
    .loadN 215059 215045,
    .subN 215060 215057 215047, .subN 215063 215047 215057, .addN 215060 215060 215063,
    .subN 215061 215058 215046, .subN 215063 215046 215058, .addN 215061 215061 215063,
    .addN 215061 215061 215060,
    .subN 215062 215059 215046, .subN 215063 215046 215059, .addN 215062 215062 215063,
    .addN 215062 215062 215060])
  (.ifLtN 215061 215020 (block [.copyN 215052 215059, .copyN 215053 215057, .constN 215054 1])
    (.ifLtN 215062 215020 (block [.copyN 215052 215058, .copyN 215053 215057, .constN 215054 1])
      .skip))

/-- One step of the partner search. -/
def chBody : Stmt := .seq (.ifLtN 215054 215020 chTest .skip) (block [.addN 215055 215055 215020])

/-- **The partner search**: `215052`, `215053` := `partner N r x` for `x` in `215046`, `215047`. -/
def partS : Stmt := .seq (block [.copyN 215052 215046, .copyN 215053 215047, .constN 215054 0,
  .constN 215055 0]) (.whileLtN 215055 215031 chBody)

/-! ## One arc -/

/-- Load the arcs `jp = arcs[t]`, `j = arcs[(t + 1) mod A]` and their ends. -/
def ldS : Stmt := .seq (block [.addN 215045 215028 215041, .addN 215045 215027 215045,
    .loadN 215043 215045, .addN 215042 215041 215020])
  (.seq (.ifLtN 215042 215030 .skip (block [.constN 215042 0]))
    (block [.addN 215045 215028 215042, .addN 215045 215027 215045, .loadN 215044 215045,
      .addN 215045 215043 215043, .addN 215045 215045 215045, .addN 215045 215045 215043,
      .addN 215045 215026 215045, .addN 215045 215045 215023, .loadN 215046 215045,
      .addN 215045 215045 215020, .loadN 215047 215045,
      .addN 215045 215044 215044, .addN 215045 215045 215045, .addN 215045 215045 215044,
      .addN 215045 215026 215045, .addN 215045 215045 215020, .loadN 215048 215045,
      .addN 215045 215045 215020, .loadN 215049 215045, .addN 215045 215045 215020,
      .loadN 215050 215045, .addN 215045 215045 215020, .loadN 215051 215045]))

/-- The junction point (if the partner is not the start of `j`). -/
def junS : Stmt := .seq (block [.subN 215060 215052 215048, .subN 215063 215048 215052,
    .addN 215060 215060 215063, .subN 215061 215053 215049, .subN 215063 215049 215053,
    .addN 215061 215061 215063, .addN 215060 215060 215061])
  (.ifLtN 215060 215020 .skip (.seq (block [.copyN 215064 215052, .copyN 215065 215053]) emitS))

/-- The start point of `j`. -/
def stS : Stmt := .seq (block [.copyN 215064 215048, .copyN 215065 215049]) emitS

/-- The end point of `j`. -/
def enS : Stmt := .seq (block [.copyN 215064 215072, .copyN 215065 215051]) emitS

/-- **One iteration of the arc loop.** -/
def arcBody : Stmt :=
  .seq ldS (.seq partS (.seq junS (.seq stS (.seq runS (.seq enS
    (block [.addN 215041 215041 215020]))))))

/-- **The arc loop.** -/
def arcLoop : Stmt := .whileLtN 215041 215030 arcBody

/-! ## The host -/

/-- The host handle after the buffer, the count word, the copy arguments. -/
def finS : Stmt := .seq (block [.copyN 215010 215040, .storeN 215010 215011,
    .addN 215082 215010 215020, .constN 215080 0])
  (.ifLtN 215022 215002 (block [.copyN 215081 215032, .copyN 215083 215023, .constN 215084 0])
    (block [.subN 215081 215040 215023, .constN 215083 0, .copyN 215084 215023]))

/-- Copy one item. -/
def cpyBody : Stmt := block [.loadN 215085 215081, .storeN 215082 215085,
  .addN 215086 215081 215020, .loadN 215085 215086, .addN 215086 215082 215020,
  .storeN 215086 215085,
  .addN 215086 215081 215024, .loadN 215085 215086, .addN 215086 215082 215024,
  .storeN 215086 215085,
  .addN 215082 215082 215023, .addN 215081 215081 215083, .subN 215081 215081 215084,
  .addN 215080 215080 215020]

/-- **The copy of the items** (reversed when `li = 0`). -/
def cpyLoop : Stmt := .whileLtN 215080 215011 cpyBody

/-- Raise the allocator to the end of the host. -/
def padLoopH : Stmt := .whileLtN 9999 215082 (block [.addN 9999 9999 215020])

/-- **The host RAM.** -/
def hostS : Stmt := .seq setupS (.seq arcLoop (.seq finS (.seq cpyLoop padLoopH)))

/-! ## Write sets -/

open BuildRam

/-- The registers of the host RAM (and the allocator). -/
def Ball (q : ℕ) : Bool := decide (215000 ≤ q ∧ q < 216000) || decide (q = 9999)

/-- The registers written after the setup by the arc loop. -/
def Bdyn (q : ℕ) : Bool := decide (q = 215011) || decide (q = 215012) ||
  decide (215040 ≤ q ∧ q < 216000)

/-- The registers `emitS` writes. -/
def Bem (q : ℕ) : Bool := decide (q = 215011) || decide (q = 215012) || decide (q = 215040) ||
  decide (215066 ≤ q ∧ q ≤ 215069)

/-- The registers `runS` writes. -/
def Brun (q : ℕ) : Bool := decide (q = 215011) || decide (q = 215012) || decide (q = 215040) ||
  decide (q = 215063) || decide (215069 ≤ q ∧ q ≤ 215076)

/-- The registers `partS` writes. -/
def Bpart (q : ℕ) : Bool := decide (q = 215045) || decide (215052 ≤ q ∧ q ≤ 215063)

/-- The registers `junS`, `stS`, `enS` write. -/
def Bjun (q : ℕ) : Bool := Bem q || decide (215060 ≤ q ∧ q ≤ 215065)

/-- The registers `ldS` writes. -/
def Bld (q : ℕ) : Bool := decide (215042 ≤ q ∧ q ≤ 215051)

theorem wrM_setupS : wrM Ball setupS = true := ⌖
theorem wrM_chBody : wrM Bpart chBody = true := ⌖
theorem wrM_ldS : wrM Bld ldS = true := ⌖
theorem wrM_hostS : wrM Ball hostS = true := ⌖
theorem wrM2_hostS : wrM2 Ball (fun _ => false) hostS = true := ⌖

end

end DrvH

end Chazelle.Core
