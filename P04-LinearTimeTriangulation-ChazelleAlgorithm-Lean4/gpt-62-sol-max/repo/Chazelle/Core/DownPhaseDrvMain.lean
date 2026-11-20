module

public import Chazelle.Core.DownPhaseDrvRMain
public import Chazelle.Core.DownPhaseDrvTMain
public import Chazelle.Core.DownPhaseDrvLSOf
public import Chazelle.Core.DownPhaseDrvHMain
public import Chazelle.Core.DownPhaseDrvGMain
public import Chazelle.Core.DownPhaseDrvPOf
public import Chazelle.Core.DownPhaseDrvLMMain
public import Chazelle.Core.DownPhaseDrvLCMain
public import Chazelle.Core.DownPhaseMathHR1
public import Chazelle.Core.ShootCutMain
public import Chazelle.Core.GradeCtx

/-!
# The down phase (RAM driver): the final assembly

`downPhaseH_of_parts` (D1, `DownPhaseDrvRMain`) runs the transition, the levels and the base case
from their contracts.  Here the contracts are discharged by the components:

* transition (D2): `DrvT.transSpec` (count `lvCnt = DownMath.cnt (2^(regCap+4)) (1120 (regCap+2))`,
  bounded by `cntMax`);
* one level: `DrvLS.levelSpec_of` from the host RAM (`DrvH.hostRamSpec`), the region procedure
  (`DrvG.regionSpec` with the pieces `DrvP.pieceSpec_of'` and the oracles `ShootCut.shootCutSpec`),
  the extraction (`ExtractRamSpec`, D6), H-R1/H-R2 (`DownMath.hostR1Spec`), the level math
  (`DrvLM.levelMathSpec`), the tail (`LvTailSpec`, D12) and the cost (`DrvLC.lvCostSpec`);
* base case (D9): `BaseSpec`.

**`downPhaseH_of`**: `MergeSpec`, valid oracles and the open components (extraction, tail, base)
give `DownPhaseSpecH (gradeCtx O)`.
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

/-- The count bound of the levels is bounded. -/
theorem lvCnt_le (l : ℕ) : lvCnt l ≤ DownMath.cntMax (2 ^ (regCap + 4)) (1120 * (regCap + 2)) :=
  DownMath.cnt_le_cntMax Nat.one_le_two_pow _ l

/-- **The down phase from a level and a base case** with the count `lvCnt` (the transition is
`DrvT.transSpec`). -/
theorem downPhaseH_of_level {X : MemCtx} (hX : X.CapLocal) {n₀ : ℕ}
    (hL : LevelSpec X lvCnt n₀) (hB : BaseSpec X lvCnt n₀) : DownPhaseSpecH X :=
  downPhaseH_of_parts hX lvCnt_le (DrvT.transSpec Nat.one_le_two_pow _) hL hB

/-- **The down phase** (`DownPhaseSpecH (gradeCtx O)`) from `MergeSpec`, valid oracles, and the
open components: the extraction (D6), the tail of a level (D12) and the base case (D9). -/
theorem downPhaseH_of (hM : MergeSpec) {O : OracleIface} (hV : O.Valid)
    (hX : ExtractRamSpec) (hT : LvTailSpec O) (hB : ∀ n₀, BaseSpec (gradeCtx O) lvCnt n₀) :
    DownPhaseSpecH (gradeCtx O) := by
  obtain ⟨n₀, hL⟩ := DrvLS.levelSpec_of DrvH.hostRamSpec
    (DrvG.regionSpec hM (ShootCut.shootCutSpec O hV) (DrvP.pieceSpec_of' hM hV)) hX hT
    DownMath.hostR1Spec DrvLM.levelMathSpec DrvLC.lvCostSpec
  exact downPhaseH_of_level (gradeCtx_capLocal O) hL (hB n₀)

end

end DrvR

end Chazelle.Core
