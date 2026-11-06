module

public import Chazelle.Core.DownPhaseDrvRSplH

/-!
# Down-phase level tail (D12), part 2: the program

`tailS sB sRd`, run after the region loop of a level (`DrvR.lvLoop`):

1. `gatherS`: constants (`ltInit`); the reservation of `5 K₂` words at the allocator `A₀`
   (`K₂ = r211012`, the total kept length; `ltRes`); the bases `A₀` (triples of `L₂`) and
   `A₀ + 3 K₂` (buckets) and the region loop set-up (`ltMid`); for every region `r < K + 1`
   (`r211011`) the copy of its kept triples and buckets from the table entry `T + 3 r`
   (`T = r211009`) to the write pointers (`ltLoop`, two `DrvR.cpS`); the arguments of the splice
   (`ltArgs`: `210020 … 210024` = `L₂` base, `K₂`, bucket base, `4 K + 3`, `4 M`,
   `M = r211013`);
2. the splice `DrvR.splS sB`;
3. the arguments of the rounds (`ltRd`: `216000 = regCap + 4 = 134`,
   `216001 = r211007 = 2^(⌈βμ⌉+12)`) and the rounds `sRd`.

Registers of `bDownDrv`: `211100` (`1`), `211101` (`3`), `211110` (`A₀`), `211111`
(reservation counter), `211112` (bucket base), `211113`, `211114` (write pointers), `211130`
(region), `211131` (`T + 3 r`), `211140 … 211145` (entry: triples, scratch, length, buckets,
`3 ℓ`, `2 ℓ`), `211147`, `211150`, `211151` (scratch); the copy uses `210034`, `210060 … 210065`.
-/

namespace Chazelle.Core

namespace DrvLT

open Machine Machine.Stmt Programs

@[expose] public section

/-- Constants, the allocator, the reservation counter. -/
def ltInit : Stmt := block [.constN 211100 1, .constN 211101 3, .constN 210034 1,
  .copyN 211110 9999, .constN 211111 0]

/-- Reserve five words. -/
def ltResBody : Stmt := block [.addN 9999 9999 211100, .addN 9999 9999 211100,
  .addN 9999 9999 211100, .addN 9999 9999 211100, .addN 9999 9999 211100,
  .addN 211111 211111 211100]

/-- The reservation loop (`5 K₂` words). -/
def ltRes : Stmt := .whileLtN 211111 211012 ltResBody

/-- The bucket base, the write pointers, the region loop set-up. -/
def ltMid : Stmt := block [.addN 211147 211012 211012, .addN 211147 211147 211012,
  .addN 211112 211110 211147, .copyN 211113 211110, .copyN 211114 211112, .constN 211130 0,
  .copyN 211131 211009]

/-- Read the table entry; the arguments of the triple copy. -/
def ltB1 : Stmt := block [.loadN 211140 211131, .addN 211141 211131 211100,
  .loadN 211142 211141, .addN 211141 211141 211100, .loadN 211143 211141,
  .addN 211144 211142 211142, .addN 211144 211144 211142, .addN 211145 211142 211142,
  .copyN 210061 211144, .copyN 210062 211140, .copyN 210063 211113]

/-- Advance the triple pointer; the arguments of the bucket copy. -/
def ltB2 : Stmt := block [.addN 211113 211113 211144, .copyN 210061 211145,
  .copyN 210062 211143, .copyN 210063 211114]

/-- Advance the bucket pointer, the table pointer and the region. -/
def ltB3 : Stmt := block [.addN 211114 211114 211145, .addN 211131 211131 211101,
  .addN 211130 211130 211100]

/-- One region of the gather. -/
def ltBody : Stmt := .seq ltB1 (.seq DrvR.cpS (.seq ltB2 (.seq DrvR.cpS ltB3)))

/-- The gather loop over the regions. -/
def ltLoop : Stmt := .whileLtN 211130 211011 ltBody

/-- The arguments of the splice. -/
def ltArgs : Stmt := block [.copyN 210020 211110, .copyN 210021 211012, .copyN 210022 211112,
  .addN 211150 210003 210003, .addN 211150 211150 211150, .addN 211150 211150 211101,
  .copyN 210023 211150, .addN 211151 211013 211013, .addN 211151 211151 211151,
  .copyN 210024 211151]

/-- The arguments of the rounds. -/
def ltRd : Stmt := block [.constN 216000 134, .copyN 216001 211007]

/-- **The gather.** -/
def gatherS : Stmt := .seq ltInit (.seq ltRes (.seq ltMid (.seq ltLoop ltArgs)))

/-- **The tail of a level** with the sorted build `sB` and the rounds `sRd`. -/
def tailS (sB sRd : Stmt) : Stmt := .seq gatherS (.seq (DrvR.splS sB) (.seq ltRd sRd))

/-- The registers the gather writes (besides the allocator). -/
def BL (r : ℕ) : Bool :=
  decide (211100 ≤ r ∧ r < 211200) || decide (210020 ≤ r ∧ r ≤ 210024) || decide (r = 210034) ||
    decide (210060 ≤ r ∧ r ≤ 210065)

end

end DrvLT

end Chazelle.Core
