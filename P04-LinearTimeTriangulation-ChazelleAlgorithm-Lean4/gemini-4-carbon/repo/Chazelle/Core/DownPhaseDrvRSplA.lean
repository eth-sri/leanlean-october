module

public import Chazelle.Core.DownPhaseDrvRBLoop
public import Chazelle.Core.DownPhaseDrvRMerge
public import Chazelle.Core.DownPhaseDrvRCopy
public import Chazelle.Core.DownPhaseNFSorted

/-!
# Down-phase driver (RAM side): the splice, blocks

The blocks of **the splice** `splS sB` (assembled in `DownPhaseDrvRSplH`), which adds the new
chords `L₂` (with a bucket per new event code) to the current chord list `L` with its sorted
event list `E`, and rebuilds the normal form with the sorted build `sB` (`BuildNFSortedSpec`):

1. `L' = L ++ L₂` at a fresh `B'` (two copies, `cpS`);
2. the event records of `L'` (`DownNF.phaseAS`);
3. the bucket distribution of the new codes `2K … 2K' - 1` (`bktS`);
4. every bucket sorted (`bsLoop`);
5. `E` and the sorted new codes copied side by side and merged (`mergeE`);
6. padding (`padS`, so that the step count covers the allocation);
7. the sorted build of `L'` with the merged list.

Registers of `bDownDrv`: inputs `210001` (model descriptor), `210002` (`B`), `210003` (`K`),
`210004` (`E`), `210020` (`B₂`), `210021` (`K₂`), `210022` (buckets), `210023` (`A`); outputs
`210002` (`B'`), `210003` (`K'`), `210004` (`E'`), `210005` (normal form).  Scratch `210025`
(`K'`), `210026` (`B'`), `210027` (`2K`), `210028` (`2K₂`), `210029` (`2K'`), `210030` (merge
source), `210066`, `210067` (`3K`), `210068`, `210069` (padding).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK

@[expose] public section

/-- Constants, sizes, the allocation of `L'`, the arguments of the first copy. -/
def spl0 : Stmt :=
  block [.constN 210034 1, .addN 210025 210003 210021, .copyN 210026 9999,
    .addN 210029 210025 210025, .addN 210027 210003 210003, .addN 210028 210021 210021,
    .addN 210066 210025 210025, .addN 210066 210066 210025, .addN 9999 9999 210066,
    .addN 210067 210003 210003, .addN 210067 210067 210003,
    .copyN 210061 210067, .copyN 210062 210002, .copyN 210063 210026]

/-- The arguments of the second copy. -/
def spl1 : Stmt :=
  block [.addN 210061 210021 210021, .addN 210061 210061 210021, .copyN 210062 210020,
    .addN 210063 210026 210067]

/-- The arguments of the records. -/
def spl2 : Stmt := block [.copyN 40000 210001, .copyN 40001 210026, .copyN 40002 210025]

/-- The arguments of the bucket distribution. -/
def spl3 : Stmt := block [.copyN 210031 210028, .copyN 210032 210023, .copyN 210033 210027]

/-- The merge arrays and the arguments of the copy of `E`. -/
def spl5 : Stmt :=
  block [.copyN 210030 9999, .addN 210071 210030 210029, .addN 9999 210071 210029,
    .copyN 210070 210030, .copyN 210072 210027, .copyN 210073 210029,
    .copyN 210061 210027, .copyN 210062 210004, .copyN 210063 210030]

/-- The arguments of the copy of the sorted new codes. -/
def spl6 : Stmt := block [.copyN 210061 210028, .copyN 210062 210048, .addN 210063 210030 210027]

/-- The arguments of the sorted build. -/
def spl7 : Stmt :=
  block [.copyN 40000 210001, .copyN 40001 210026, .copyN 40002 210025, .copyN 40004 210071]

/-- The outputs. -/
def spl8 : Stmt :=
  block [.copyN 210002 210026, .copyN 210003 210025, .copyN 210004 210071, .copyN 210005 40003]

end

end DrvR

end Chazelle.Core
