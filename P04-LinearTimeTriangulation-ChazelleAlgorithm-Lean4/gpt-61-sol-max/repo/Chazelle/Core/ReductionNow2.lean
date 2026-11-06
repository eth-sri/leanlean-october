module

public import Chazelle.Core.ReductionNow
public import Chazelle.Core.DownPhaseDrvMain
public import Chazelle.Core.DownPhaseDrvLTMain
public import Chazelle.Core.DownPhaseDrvBTopMain

/-!
# The reduction of the target after the down-phase driver

With the down-phase driver (`DrvR.downPhaseH_of`) the target follows from the sweep
(`SweepSpecH`) and three components of the down phase still being proved: the extraction RAM
(`DrvR.ExtractRamSpec`, D6), the tail of a level (`DrvR.LvTailSpec`, D12) and the base case
(`DrvR.BaseSpec`, D9).  This records exactly what remains.
-/

namespace Chazelle.Core

public section

section
variable (hS : SweepSpecH) (hX : DrvR.ExtractRamSpec)
include hS hX
/-- **Reduction of the main theorem** to the sweep and three down-phase components. -/
theorem linear_of_sweep_parts
    (hT : ∀ O : OracleIface, O.Valid → DrvR.LvTailSpec O)
    (hB : ∀ O : OracleIface, O.Valid → ∀ n₀, DrvR.BaseSpec (gradeCtx O) DrvR.lvCnt n₀) :
    LinearTimeTriangulation :=
  linear_of_sweep_down hS fun O hV =>
    DrvR.downPhaseH_of (mergeSpec_of_sweep hS) hV hX (hT O hV) (hB O hV)

/-- **Reduction of the main theorem** to the sweep, the extraction RAM (D6) and the base case
(D9): the tail of a level (D12) is proved (`DrvLT.lvTailSpec` from the interior oracles). -/
theorem linear_of_sweep_xb
    (hB : ∀ O : OracleIface, O.Valid → ∀ n₀, DrvR.BaseSpec (gradeCtx O) DrvR.lvCnt n₀) :
    LinearTimeTriangulation :=
  linear_of_sweep_parts hS hX
    (fun O hV => DrvLT.lvTailSpec (IOrc.interiorOracles_of (ShootCut.shootCutSpec O hV))) hB

/-- **Reduction of the main theorem** to the sweep, the extraction RAM (D6) and the region loop
of the base case (`DrvB.RegLoopSpec`): the top level of the base case is proved
(`DrvB.baseSpec_of_regLoop`). -/
theorem linear_of_sweep_xr
    (hRL : DrvB.RegLoopSpec) : LinearTimeTriangulation :=
  linear_of_sweep_xb hS hX fun _ _ _ => DrvB.baseSpec_of_regLoop hRL


end

end

end Chazelle.Core
