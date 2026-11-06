module

public import Chazelle.Core.NFLocateChain

/-!
# WP-G, part 9: the programs of the arc-cutter core

The **core** walks a subarc of the walk of a chain model `M = chainModel C` (`C` a chain of a
host polygon with at most `64` items) from its start `s` to its end `e` and hands every piece to
an `emit` statement (the arc-cutter's `emit` writes the piece record; the ray-shooter's `emit`
shoots at the piece).  All registers of the core are in band `bCut` (`150000 + i`):

* inputs: `0` model descriptor, `1, 2` start, `3, 4` end, `9` `γ`, `13` grade context, `20`
  mode (`0` cut, `1` shoot);
* the chain: `21` host handle, `22` start `C.s`, `23` `m`, `24` top index, `25` orientation bit,
  `26` number `N` of host points, `27` `n`, `28` tour start `S`, `29` `2m`, `31` `2m + 5`,
  `32` `2m + 6`;
* the grade table: `33` `Λ`, `34` row table, `35` halving table, `36` powers of two;
* the walk: `40` current walk vertex `c`, `41` final vertex `f`, `42` loop flag, `43` done flag;
* the piece handed to `emit`: `50, 51` start, `52, 53` end, `54` kind, `55` grade-table entry
  (kind `1`), `56` first edge of its chain of `Q`, `57` direction (`1` up), `58` `2^g`;
* a walk vertex: `44` the vertex, `60` tour position, `61` tour coordinate `J`, `62` chain index,
  `63` climbing bit, `64` host point, `65` item, `66` offset, `67 … 69` the item words;
  `45 … 47` its symbolic point (`vtxPt`);
* a stretch: `70` index `q` of `Q`, `71` length `L`, `72` limit;
* the dyadic sweeps: `80` `x`, `81` `y`, `82` `g`, `83` `x / 2^g` (or `y / 2^g`), `84` `2^g`,
  `85` walk vertex, `86` half, `87`, `88` loop test;
* constants: `90` `0`, `91` `1`, `92` `2`, `93` `3`, `96` `6`; scratch `75 … 79`.

`emit` must keep the registers `150000 … 150099`.
-/

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## Set-up -/

/-- The constants. -/
def cInit : Stmt := block [.constN 150090 0, .constN 150091 1, .constN 150092 2,
  .constN 150093 3, .constN 150096 6]

/-- The chain descriptor (`lr 0 + 1 …`): host handle, start, number of edges. -/
def cHead1 : Stmt := block [
  .addN 150075 150000 150091, .loadN 150021 150075,
  .addN 150075 150075 150091, .loadN 150022 150075,
  .addN 150075 150075 150091, .loadN 150023 150075]

/-- The top index, the orientation bit and the walk constants. -/
def cHead2 : Stmt := block [
  .addN 150075 150075 150091, .loadN 150024 150075,
  .addN 150075 150075 150091, .loadN 150025 150075,
  .addN 150029 150023 150023, .addN 150032 150029 150096, .subN 150031 150032 150091]

/-- `n` and the grade table. -/
def cHead3 : Stmt := block [
  .inputSize 150027, .loadN 150033 150013,
  .addN 150075 150013 150091, .loadN 150076 150075, .addN 150036 150076 150092,
  .addN 150075 150013 150092, .loadN 150034 150075,
  .addN 150075 150013 150093, .loadN 150035 150075]

/-- The tour start `S = T` (orientation bit set) or `2m - T`. -/
def cS : Stmt :=
  .ifLtN 150025 150091 (.instr (.subN 150028 150029 150024))
    (.ifLtN 150091 150025 (.instr (.subN 150028 150029 150024)) (.instr (.copyN 150028 150024)))

/-- The number of host points (`NFLoc.cntStmt`). -/
def cCount : Stmt :=
  .seq (.instr (.copyN 50060 150021)) (.seq NFLoc.cntStmt (.instr (.copyN 150026 50063)))

/-- The whole set-up. -/
def cPre : Stmt := .seq cInit (.seq cHead1 (.seq cHead2 (.seq cHead3 (.seq cS cCount))))

/-! ## The host item of a host point -/

def itInit : Stmt :=
  block [.constN 150065 0, .constN 150073 0, .addN 150074 150021 150091, .loadN 150077 150021]

def itFound : Stmt := block [.subN 150066 150064 150073, .copyN 150079 150065, .copyN 150065 150077]

def itNext : Stmt := block [.copyN 150073 150078, .addN 150065 150065 150091,
  .addN 150074 150074 150093]

def itBody : Stmt :=
  .seq (block [.loadN 150067 150074, .addN 150075 150074 150091, .loadN 150068 150075,
      .addN 150075 150075 150091, .loadN 150069 150075])
    (.seq (.ifLtN 150067 150091 (block [.addN 150078 150073 150069, .addN 150078 150078 150091])
        (.instr (.addN 150078 150073 150091)))
      (.ifLtN 150064 150078 itFound itNext))

/-- **The item of the host point `150064`**: item `65`, offset `66`, words `67 … 69`. -/
def itLook : Stmt :=
  .seq itInit (.seq (.whileLtN 150065 150077 itBody) (.instr (.copyN 150065 150079)))

/-! ## A walk vertex of the double boundary -/

/-- **The walk vertex `150044`** (`6 ≤ v ≤ 2m + 6`): tour position, tour coordinate, chain
index, climbing bit, host point and its item. -/
def locV : Stmt :=
  .seq (block [.subN 150060 150044 150096, .subN 150075 150029 150028])
    (.seq (.ifLtN 150060 150075 (.instr (.addN 150061 150028 150060))
        (.instr (.subN 150061 150060 150075)))
      (.seq (.ifLtN 150061 150023 (block [.constN 150063 1, .copyN 150062 150061])
          (block [.constN 150063 0, .subN 150062 150029 150061]))
        (.seq (.seq (.instr (.addN 150075 150022 150062))
            (.ifLtN 150075 150026 (.instr (.copyN 150064 150075))
              (.instr (.subN 150064 150075 150026))))
          itLook)))

/-- **The symbolic point of the walk vertex `150044`** into `150045 …`. -/
def vtxPt : Stmt :=
  .seq locV
    (.ifLtN 150067 150091
      (.seq (.instr (.addN 150075 150068 150066))
        (.seq (.ifLtN 150075 150027 (.instr (.copyN 150046 150075))
            (.instr (.subN 150046 150075 150027)))
          (.instr (.constN 150045 0))))
      (.ifLtN 150067 150092 (block [.constN 150045 0, .copyN 150046 150068])
        (block [.constN 150045 1, .copyN 150046 150068, .copyN 150047 150069])))

/-! ## Pieces -/

/-- The single-edge piece from the current vertex. -/
def pcSingle : Stmt := block [.copyN 150050 150040, .constN 150051 0, .addN 150052 150040 150091,
  .constN 150053 0, .constN 150054 0]

/-- Emit a single edge and advance. -/
def single (emit : Stmt) : Stmt :=
  .seq pcSingle (.seq emit (.instr (.addN 150040 150040 150091)))

/-- The block piece `[w, w + 2^g]` with its entry (`g > 0`: the entry `(g, 150077)` of the grade
table, kind `1`; `g = 0`: kind `0`); `150056` the first edge of its chain of `Q`, `150057` the
direction. -/
def pcBlock (x dir : ℕ) : Stmt :=
  .seq (block [.copyN 150050 150085, .constN 150051 0, .addN 150052 150085 150084,
      .constN 150053 0, .copyN 150056 x, .constN 150057 dir, .copyN 150058 150084])
    (.ifLtN 150090 150082
      (block [.constN 150054 1, .addN 150075 150034 150082, .loadN 150076 150075,
        .addN 150055 150076 150077, .addN 150055 150055 150077, .addN 150055 150055 150077])
      (.instr (.constN 150054 0)))

/-! ## The dyadic sweeps -/

section
variable (emit : Stmt)
include emit
/-- Upward, ascending sweep body. -/
def upABody : Stmt :=
  .seq (block [.addN 150075 150035 150083, .loadN 150086 150075, .addN 150075 150086 150086])
    (.seq (.ifLtN 150075 150083
        (.seq (.instr (.copyN 150077 150083))
          (.seq (pcBlock 150080 1)
            (.seq emit (block [.addN 150080 150080 150084, .addN 150085 150085 150084,
              .addN 150086 150086 150091]))))
        .skip)
      (block [.addN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
        .copyN 150083 150086, .addN 150087 150080 150084]))

/-- Upward, descending sweep body (the odd branch as in the ascending sweep, with the index
kept in `86`). -/
def upBBody : Stmt :=
  .seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
      .addN 150083 150083 150083, .copyN 150086 150083, .addN 150087 150080 150084])
    (.seq (.ifLtN 150087 150088
      (.seq (.instr (.copyN 150077 150083))
        (.seq (pcBlock 150080 1)
          (.seq emit (block [.addN 150080 150080 150084, .addN 150085 150085 150084,
            .addN 150086 150086 150091]))))
      .skip) (.instr (.copyN 150083 150086)))

/-- **The upward dyadic cover** of `[q, q + L)` (`q` in `70`, `L` in `71`) from the walk vertex
`c`; the new `c` is `c + L`. -/
def dyUp : Stmt :=
  .seq (block [.copyN 150080 150070, .addN 150081 150070 150071, .addN 150088 150081 150091,
      .constN 150082 0, .copyN 150083 150070, .constN 150084 1, .copyN 150085 150040,
      .addN 150087 150080 150084])
    (.seq (.whileLtN 150087 150088 (upABody emit))
      (.seq (.whileLtN 150090 150082 (upBBody emit)) (.instr (.copyN 150040 150085))))

/-- Downward sweeps: hand the block below `y` (index `x / 2^g - 1`), then lower `y`. -/
def dnOdd : Stmt :=
  .seq (block [.subN 150077 150083 150091, .subN 150078 150081 150084])
    (.seq (pcBlock 150078 0)
      (.seq emit (block [.subN 150081 150081 150084, .addN 150085 150085 150084])))

/-- Downward, ascending sweep body. -/
def dnABody : Stmt :=
  .seq (block [.addN 150075 150035 150083, .loadN 150086 150075, .addN 150075 150086 150086])
    (.seq (.ifLtN 150075 150083 (dnOdd emit) .skip)
      (block [.addN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
        .copyN 150083 150086, .addN 150087 150080 150084, .addN 150088 150081 150091]))

/-- Downward, descending sweep body. -/
def dnBBody : Stmt :=
  .seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
      .addN 150083 150083 150083, .addN 150087 150080 150084, .addN 150088 150081 150091])
    (.ifLtN 150087 150088 (.seq (dnOdd emit) (.instr (.subN 150083 150083 150091))) .skip)

/-- **The downward dyadic cover** of `[q - L, q)` from the top `q`. -/
def dyDn : Stmt :=
  .seq (block [.copyN 150081 150070, .subN 150080 150070 150071, .addN 150088 150081 150091,
      .constN 150082 0, .copyN 150083 150070, .constN 150084 1, .copyN 150085 150040,
      .addN 150087 150080 150084])
    (.seq (.whileLtN 150087 150088 (dnABody emit))
      (.seq (.whileLtN 150090 150082 (dnBBody emit)) (.instr (.copyN 150040 150085))))

/-! ## One step of the main loop -/


end

/-- `150071 := min 150071 r`. -/
def minTo (r : ℕ) : Stmt := .ifLtN r 150071 (.instr (.copyN 150071 r)) .skip

/-- The length of a climbing stretch (the item is a run, `t < ℓ`, `q + 1 < n`) into `150071`:
`L = min (m - J) (ℓ - t) (n - 1 - q) lim`. -/
def upLen : Stmt :=
  .seq (block [.subN 150071 150023 150061, .subN 150075 150069 150066])
    (.seq (minTo 150075) (.seq (block [.subN 150075 150027 150070, .subN 150075 150075 150091])
      (.seq (minTo 150075) (minTo 150072))))

/-- A climbing stretch: its length, the upward cover, and the constants set again (the sweeps
keep only `150090`, `150091` of them). -/
def upStretch (emit : Stmt) : Stmt := .seq upLen (.seq (dyUp emit) cInit)

/-- The length of a descending stretch (`0 < t`, `0 < q`): `L = min (2m - J) t q lim`. -/
def dnLen : Stmt :=
  .seq (.instr (.subN 150071 150029 150061))
    (.seq (minTo 150066) (.seq (minTo 150070) (minTo 150072)))

section
variable (emit : Stmt)
include emit
/-- A descending stretch. -/
def dnStretch : Stmt := .seq dnLen (.seq (dyDn emit) cInit)

/-- A run item: the index `q = (a + t) mod n`, then a stretch or a single edge. -/
def runStep : Stmt :=
  .seq (.seq (.instr (.addN 150075 150068 150066))
      (.ifLtN 150075 150027 (.instr (.copyN 150070 150075))
        (.instr (.subN 150070 150075 150027))))
      (.ifLtN 150063 150091
        (.ifLtN 150090 150066 (.ifLtN 150090 150070 (dnStretch emit) (single emit)) (single emit))
        (.ifLtN 150066 150069
          (.seq (.instr (.addN 150075 150070 150091))
            (.ifLtN 150075 150027 (upStretch emit) (single emit)))
          (single emit)))

/-- **A step on the double boundary** from the vertex `c < 2m + 6`. -/
def cStep : Stmt :=
  .seq (.instr (.copyN 150044 150040))
    (.seq locV
      (.seq (.ifLtN 150041 150040 (.instr (.subN 150072 150032 150040))
          (.instr (.subN 150072 150041 150040)))
        (.ifLtN 150067 150091 (runStep emit) (single emit))))

/-- The piece through the uncounted block, from `2m + 6` to `6`. -/
def uStep : Stmt :=
  .seq (block [.copyN 150050 150032, .constN 150051 0, .copyN 150052 150096, .constN 150053 0,
      .constN 150054 0])
    (.seq emit (.instr (.copyN 150040 150096)))


end

/-- The loop flag: `1` iff `c ≠ f`. -/
def setFlag : Stmt :=
  .ifLtN 150040 150041 (.instr (.constN 150042 1))
    (.ifLtN 150041 150040 (.instr (.constN 150042 1)) (.instr (.constN 150042 0)))

/-- **The main loop**: while `c ≠ f`, a step. -/
def mainLoop (emit : Stmt) : Stmt :=
  .whileLtN 150090 150042 (.seq (.ifLtN 150040 150032 (cStep emit) (uStep emit)) setFlag)

/-! ## Tests on walk positions -/

/-- The direction code of the walk edge `150049` into `150059` (`NFLoc.chainDir`). -/
def dirP : Stmt :=
  .seq (block [.copyN 50000 150000, .copyN 50002 150049])
    (.seq NFLoc.chainDir (.instr (.copyN 150059 10502)))

/-- Compare the height of the symbolic point `150045 …` with the height of the vertex `150076`
of `Q`: `150089 := dirOf` (`NFLoc.dirTail`). -/
def hcmp : Stmt :=
  .seq (block [.copyN 50040 150045, .copyN 50041 150046, .copyN 50042 150047,
      .constN 50043 0, .copyN 50044 150076])
    (.seq NFLoc.dirTail (.instr (.copyN 150089 10502)))

/-- **Is the parameter of the position `(150049, 150076 + 1)` positive?** (walk edge
`6 ≤ p ≤ 2m + 6`): the edge is not horizontal and the height differs from the one of its start
vertex; answer in `150089`. -/
def posP : Stmt :=
  .seq dirP
    (.ifLtN 150059 150091 (.instr (.constN 150089 0))
      (.seq (.instr (.copyN 150044 150049)) (.seq vtxPt (.seq hcmp
        (.ifLtN 150090 150089 (.instr (.constN 150089 1)) .skip)))))

/-- **Is the start before the end** (both on the edge `150049`, codes `≥ 1`)?  Answer in
`150089`: the direction code and the order of the two heights agree. -/
def keyLess : Stmt :=
  .seq dirP
    (.ifLtN 150059 150091 (.instr (.constN 150089 0))
      (.seq (block [.constN 50040 0, .subN 50041 150002 150091, .constN 50043 0,
          .subN 50044 150004 150091])
        (.seq NFLoc.dirTail
          (.ifLtN 10502 150059 (.instr (.constN 150089 0))
            (.ifLtN 150059 10502 (.instr (.constN 150089 0)) (.instr (.constN 150089 1)))))))

/-- The flag of the box block: `150038 := [e₁ ∈ U]`, `150039 := [e₂ ∈ U]`; their positions in
the block (`150037`, `150030`: `0` for `2m + 6`, else `p + 1`). -/
def uFlag (src dst idx : ℕ) : Stmt :=
  .ifLtN src 150096 (block [.constN dst 1, .addN idx src 150091])
    (.ifLtN src 150032 (block [.constN dst 0, .constN idx 0])
      (.ifLtN 150032 src (block [.constN dst 0, .constN idx 0])
        (block [.constN dst 1, .constN idx 0])))

/-- The box edges: `150048 := 1` on the edges `1, 3, 5` (not horizontal; the end is inside the
box). -/
def decBox : Stmt :=
  .ifLtN 150001 150091 .skip (.ifLtN 150001 150092 (.instr (.constN 150048 1))
    (.ifLtN 150001 150093 .skip (.seq (.instr (.subN 150075 150001 150093))
      (.ifLtN 150075 150091 (.instr (.constN 150048 1))
        (.ifLtN 150075 150092 .skip (.instr (.constN 150048 1)))))))

/-- The start at a vertex, the end inside the edge: is the parameter of the end positive? -/
def decVtx : Stmt :=
  .ifLtN 150001 150096 decBox
    (.seq (block [.copyN 150049 150001, .subN 150076 150004 150091])
      (.seq posP (.instr (.copyN 150048 150089))))

/-- Both ends on one edge, the end not at its start vertex. -/
def decSame : Stmt :=
  .ifLtN 150002 150091 decVtx
    (.seq (.instr (.copyN 150049 150001)) (.seq keyLess (.instr (.copyN 150048 150089))))

/-- **The decision `SAME`** (the subarc lies inside the edge of its start), into `150048`. -/
def decideS : Stmt :=
  .seq (.instr (.constN 150048 0))
    (.ifLtN 150001 150003 .skip (.ifLtN 150003 150001 .skip
      (.ifLtN 150090 150004 decSame .skip)))

/-! ## The whole core -/

/-- The piece `[s, e]` (kind `0`). -/
def pcSE : Stmt := block [.copyN 150050 150001, .copyN 150051 150002, .copyN 150052 150003,
  .copyN 150053 150004, .constN 150054 0]

/-- The piece from the start to the walk vertex `150075` (kind `0`). -/
def pcSV : Stmt := block [.copyN 150050 150001, .copyN 150051 150002, .copyN 150052 150075,
  .constN 150053 0, .constN 150054 0]

/-- The piece from the walk vertex `150075` to the end (kind `0`). -/
def pcVE : Stmt := block [.copyN 150050 150075, .constN 150051 0, .copyN 150052 150003,
  .copyN 150053 150004, .constN 150054 0]

section
variable (emit : Stmt)
include emit
/-- The first piece; sets `c` (`150040`) or the done flag (`150043`). -/
def first : Stmt :=
  .ifLtN 150090 150038
    -- the start is in the box block
    (.ifLtN 150090 150039
      (.ifLtN 150037 150030 (.seq pcSE (.seq emit (.instr (.constN 150043 1))))
        (.seq (.instr (.copyN 150075 150096)) (.seq pcSV (.seq emit
          (.instr (.copyN 150040 150096))))))
      (.seq (.instr (.copyN 150075 150096)) (.seq pcSV (.seq emit
        (.instr (.copyN 150040 150096))))))
    -- the start is on the double boundary
    (.seq (.instr (.addN 150075 150001 150091))
      (.ifLtN 150090 150039
        (.ifLtN 150075 150032
          (.seq pcSV (.seq emit (.instr (.addN 150040 150001 150091))))
          (.seq pcSE (.seq emit (.instr (.constN 150043 1)))))
        (.seq pcSV (.seq emit (.instr (.addN 150040 150001 150091))))))

/-- The last piece. -/
def final : Stmt :=
  .ifLtN 150090 150039
    (.seq (.instr (.copyN 150075 150031)) (.seq pcVE emit))
    (.ifLtN 150090 150004
      (.seq (block [.copyN 150049 150003, .subN 150076 150004 150091])
        (.seq posP (.ifLtN 150090 150089
          (.seq (.instr (.copyN 150075 150003)) (.seq pcVE emit)) .skip)))
      .skip)

/-- The general case: the first piece, the main loop, the last piece. -/
def general : Stmt :=
  .seq (.seq (uFlag 150001 150038 150037) (uFlag 150003 150039 150030))
    (.seq (.ifLtN 150090 150039 (.instr (.copyN 150041 150031)) (.instr (.copyN 150041 150003)))
      (.seq (.instr (.constN 150043 0))
        (.seq (first emit)
          (.ifLtN 150043 150091 (.seq setFlag (.seq (mainLoop emit) (final emit))) .skip))))

/-- **The core of the arc-cutter.** -/
def core : Stmt :=
  .seq cPre (.seq decideS (.ifLtN 150090 150048 (.seq pcSE emit) (general emit)))


end

end

end ShootCut

end Chazelle.Core
