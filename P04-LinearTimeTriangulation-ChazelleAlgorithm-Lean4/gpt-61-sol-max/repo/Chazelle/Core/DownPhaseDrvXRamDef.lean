module

public import Chazelle.Core.DownPhaseDrvXBkt2
public import Chazelle.Core.DownPhaseDrvRLib
public import Chazelle.Core.RestoreTRead

/-!
# Down phase, extraction (D6): the RAM program

Registers (band `bDownDrv`, `217000 … 217999`).

* Inputs: `217000` handle of `N`, `217001` region `r`, `217002` bit `li`, `217003` host handle,
  `217004` number of host points, `217005` model descriptor, `217006` handle of `N_R`.
* Outputs: `217010` triple list, `217011` its length, `217012` bucket list.
* Globals (`setupS`): `217020 n`, `217021 m`, `217022 2m`, `217023 T`, `217024` raw orientation
  bit, `217025 sS` (tour offset), `217026 li ∈ {0, 1}`, `217027 = 1`, `217028` number of chords
  of `N_R`, `217029` its chord base, `217030 A` (arcs of `N`), `217031` arc base, `217032` number of
  arcs of region `r`, `217033` start of its arc list, `217034` number of host items, `217035` first
  host item, `217036` triple base, `217037` bucket base, `217038` count of kept chords, `217039`
  chord counter, `217040` chord pointer, `217041 = 6`, `217042 = 2m + 6`, `217043` padding counter,
  `217044 = 2`, `217045` triple pointer, `217046` bucket pointer, `217047` padding bound.
* Chord: `217050 h`, `217051 lp`, `217052 rp`, `217053 h + 1`; left end `217054 … 217057`
  (regular-inner bit, symbolic point), right end `217080 … 217083`, `217084`/`217085` interior
  edges, `217086`/`217087` buckets.
* `clsS` (an end): `217060 p` → `217061 u`, `217062 kc`, `217063` side bit, `217064` regular-inner
  bit, `217065 t0`, `217066` height vertex, `217067` scratch.
* `lookS` (host point `k`): `217090 k` → `217070` kind (`1` vertex, `2` edge point), `217071`,
  `217072` arguments; scratch `217091 … 217097`.
* `peS` (interior edge): `217070 … 217072` → `217100`; scratch `217101 … 217104`.
* `bktS` (bucket): `217110` edge, `217111` height code → `217112`; scratch `217113 … 217128`.
* `posLtS` (key order): `217150 … 217153` → `217154`; scratch `217155`, `217156`.
* `hltS` (height order): `217160`, `217161` → `217162`; real scratch `217160`, `217161`.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## Height order -/

/-- `217162 := [ylexLT (P.vtx u) (P.vtx v)]` for `u = 217160`, `v = 217161`. -/
def hltS : Stmt :=
  .seq (block [.readY 217160 217160, .readY 217161 217161])
    (.ifLtR 217160 217161 (block [.constN 217162 1])
      (.ifLtR 217161 217160 (block [.constN 217162 0])
        (.seq (block [.readX 217160 217160, .readX 217161 217161])
          (.ifLtR 217160 217161 (block [.constN 217162 1]) (block [.constN 217162 0])))))

/-! ## Walk vertex and walk edge indices -/

section
variable (src dst : ℕ)
include src dst
/-- `dst := ivB li n src`. -/
def ivBS : Stmt :=
  .ifLtN 217026 217027 (block [.subN dst 217020 217027, .subN dst dst src])
    (block [.copyN dst src])

/-- `dst := qE li n src` (scratch `217104`). -/
def qES : Stmt :=
  .ifLtN 217026 217027
    (.seq (block [.addN 217104 src 217027])
      (.ifLtN 217104 217020 (block [.subN dst 217020 217027, .subN dst dst 217027, .subN dst dst src])
        (block [.subN dst 217020 217027])))
    (block [.copyN dst src])

/-- `dst := (src + 1) mod n` for `src < n`. -/
def succS : Stmt :=
  .seq (block [.addN dst src 217027]) (.ifLtN dst 217020 .skip (block [.constN dst 0]))

/-! ## Key order of interior positions -/


end

/-- The core of `posLtS` (equal edges, different heights). -/
def posLtCore : Stmt :=
  .seq (ivBS 217150 217160)
    (.seq (succS 217150 217155)
      (.seq (ivBS 217155 217161)
        (.seq hltS
          (.seq (block [.copyN 217156 217162, .subN 217160 217151 217027,
              .subN 217161 217153 217027])
            (.seq hltS
              (.ifLtN 217156 217162 (block [.constN 217154 0])
                (.ifLtN 217162 217156 (block [.constN 217154 0]) (block [.constN 217154 1]))))))))

/-- `217154 := [PosLt ⟨217150, 217151⟩ ⟨217152, 217153⟩]`. -/
def posLtS : Stmt :=
  .ifLtN 217150 217152 (block [.constN 217154 1])
    (.ifLtN 217152 217150 (block [.constN 217154 0])
      (.ifLtN 217151 217153 posLtCore
        (.ifLtN 217153 217151 posLtCore (block [.constN 217154 0]))))

/-! ## Host points -/

/-- One host item of `lookS`. -/
def lookBody : Stmt :=
  .seq (block [.loadN 217094 217092, .addN 217097 217092 217027, .loadN 217095 217097,
      .addN 217097 217097 217027, .loadN 217096 217097])
    (.seq
      (.ifLtN 217094 217027
        -- a run `a = x1`, `ℓ = x2`
        (.seq
          (.ifLtN 217090 217093 .skip
            (.seq (block [.subN 217097 217090 217093])
              (.ifLtN 217096 217097 .skip
                (.seq (block [.constN 217070 1, .addN 217071 217095 217097])
                  (.ifLtN 217071 217020 .skip (block [.subN 217071 217071 217020]))))))
          (block [.addN 217093 217093 217096, .addN 217093 217093 217027]))
        -- a point
        (.seq
          (.ifLtN 217090 217093 .skip
            (.ifLtN 217093 217090 .skip
              (block [.copyN 217070 217094, .copyN 217071 217095, .copyN 217072 217096])))
          (block [.addN 217093 217093 217027])))
      (block [.addN 217092 217092 217027, .addN 217092 217092 217027, .addN 217092 217092 217027,
        .addN 217091 217091 217027]))

/-- **Host point `k = 217090`** (`217070` kind, `217071`, `217072` arguments). -/
def lookS : Stmt :=
  .seq (block [.constN 217091 0, .copyN 217092 217035, .constN 217093 0])
    (.whileLtN 217091 217034 lookBody)

/-! ## The ends of a chord -/

/-- A list of statements in sequence. -/
def seqs : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: l => .seq s (seqs l)

theorem seqs_cons₂ (s t : Stmt) (l : List Stmt) : seqs (s :: t :: l) = .seq s (seqs (t :: l)) := rfl

/-- **Classify the end at walk edge `p = 217060`** (height vertex `h = 217050`). -/
def clsS : Stmt := seqs [
  block [.subN 217061 217060 217041, .addN 217061 217025 217061],
  .ifLtN 217061 217022 .skip (block [.subN 217061 217061 217022]),
  .ifLtN 217061 217022 .skip (block [.subN 217061 217061 217022]),
  .ifLtN 217061 217021 (block [.constN 217063 1]) (block [.constN 217063 0]),
  .ifLtN 217021 217061 (block [.subN 217062 217022 217061]) (block [.copyN 217062 217061]),
  block [.copyN 217090 217062],
  lookS,
  .ifLtN 217070 217044 (block [.copyN 217066 217071]) (block [.copyN 217066 217072]),
  .ifLtN 217050 217066 (block [.constN 217065 0])
    (.ifLtN 217066 217050 (block [.constN 217065 0]) (block [.constN 217065 1])),
  block [.constN 217064 1],
  .ifLtN 217060 217041 (block [.constN 217064 0]) .skip,
  .ifLtN 217042 217060 (block [.constN 217064 0]) .skip,
  .ifLtN 217060 217042 .skip
    (.ifLtN 217042 217060 .skip (.ifLtN 217065 217027 (block [.constN 217064 0]) .skip)),
  .ifLtN 217065 217027 .skip
    (.ifLtN 217062 217027 (block [.constN 217064 0])
      (.ifLtN 217062 217021 .skip (.ifLtN 217021 217062 .skip (block [.constN 217064 0])))),
  .ifLtN 217063 217026 (block [.constN 217064 0])
    (.ifLtN 217026 217063 (block [.constN 217064 0]) .skip)]

/-- **The interior walk edge of the host point** `217070 … 217072` into `217100`. -/
def peS : Stmt :=
  .ifLtN 217070 217044 (ivBS 217071 217100)
    (.seq (qES 217071 217101)
      (.seq (succS 217101 217102)
        (.seq (ivBS 217102 217103)
          (.ifLtN 217072 217103 (block [.copyN 217100 217101])
            (.ifLtN 217103 217072 (block [.copyN 217100 217101])
              (block [.copyN 217100 217102]))))))

/-! ## Buckets -/

/-- `dst := [a = b ∧ c = d]`. -/
def eq2S (a b c d dst : ℕ) : Stmt :=
  .seq (block [.constN dst 0])
    (.ifLtN a b .skip (.ifLtN b a .skip (.ifLtN c d .skip (.ifLtN d c .skip (block [.constN dst 1])))))

/-- `posLtS` on four registers, result into `dst`. -/
def posLtOn (a b c d dst : ℕ) : Stmt :=
  .seq (block [.copyN 217150 a, .copyN 217151 b, .copyN 217152 c, .copyN 217153 d])
    (.seq posLtS (block [.copyN dst 217154]))

/-- The bucket formula `bktF A j eqS eqE gtS` into `217112`. -/
def bktFS : Stmt :=
  .ifLtN 217122 217027
    (.ifLtN 217123 217027
      (.ifLtN 217125 217027 (block [.constN 217112 0])
        (block [.addN 217112 217116 217116, .addN 217112 217112 217044]))
      (.seq (block [.addN 217128 217116 217027])
        (.ifLtN 217128 217030 (block [.addN 217112 217128 217128, .addN 217112 217112 217027])
          (block [.constN 217112 1]))))
    (block [.addN 217112 217116 217116, .addN 217112 217112 217027])

/-- The arc test `eqS ∨ eqE ∨ (ltSE ? ltSX ∧ ltXE : ltSX ∨ ltXE)` into `217127`. -/
def onS : Stmt :=
  .seq (block [.constN 217127 0])
    (.ifLtN 217122 217027
      (.ifLtN 217123 217027
        (.ifLtN 217124 217027
          (.ifLtN 217125 217027 (.ifLtN 217126 217027 .skip (block [.constN 217127 1]))
            (block [.constN 217127 1]))
          (.ifLtN 217125 217027 .skip (.ifLtN 217126 217027 .skip (block [.constN 217127 1]))))
        (block [.constN 217127 1]))
      (block [.constN 217127 1]))

/-- Read arc `j = mem 217114` of `N`: `217116 j`, `217118 … 217121` its ends. -/
def arcRdS : Stmt :=
  block [.loadN 217116 217114, .addN 217117 217116 217116, .addN 217117 217117 217117,
    .addN 217117 217117 217116, .addN 217117 217117 217031,
    .addN 217128 217117 217027, .loadN 217118 217128, .addN 217128 217128 217027,
    .loadN 217119 217128, .addN 217128 217128 217027, .loadN 217120 217128,
    .addN 217128 217128 217027, .loadN 217121 217128]

/-- One arc of the region in `bktS`. -/
def bktBody : Stmt := seqs [
  arcRdS,
  eq2S 217110 217118 217111 217119 217122,
  eq2S 217110 217120 217111 217121 217123,
  posLtOn 217118 217119 217120 217121 217124,
  posLtOn 217118 217119 217110 217111 217125,
  posLtOn 217110 217111 217120 217121 217126,
  onS,
  .ifLtN 217115 217027 (.ifLtN 217127 217027 .skip (.seq bktFS (block [.constN 217115 1]))) .skip,
  block [.addN 217114 217114 217027, .addN 217113 217113 217027]]

/-- **The bucket of the interior position `⟨217110, 217111⟩`** into `217112`. -/
def bktS : Stmt :=
  .seq (block [.constN 217113 0, .copyN 217114 217033, .constN 217115 0, .constN 217112 0])
    (.whileLtN 217113 217032 bktBody)

end

end DrvX

end Chazelle.Core
