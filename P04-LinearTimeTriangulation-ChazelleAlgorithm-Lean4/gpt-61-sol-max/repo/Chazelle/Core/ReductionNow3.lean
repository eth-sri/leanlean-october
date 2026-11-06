module

public import Chazelle.Core.ReductionNow2
public import Chazelle.Core.DownPhaseDrvXFinal
public import Chazelle.Core.DownPhaseDrvBLoopMain
public import Chazelle.Core.DownPhaseDrvBRegC
public import Chazelle.Core.DownPhaseDrvBExpD

/-!
# The reduction of the target after the extraction RAM (D6)

With `DrvX.extractRamSpec` proved, the target follows from the sweep `SweepSpecH` and the region
loop of the base case `DrvB.RegLoopSpec` alone (`linear_of_sweep_reg`).
-/

namespace Chazelle.Core

public section

section
variable (hS : SweepSpecH)
include hS
/-- **Reduction of the main theorem** to the sweep (WP-D) and the region loop of the base case. -/
theorem linear_of_sweep_reg (hRL : DrvB.RegLoopSpec) :
    LinearTimeTriangulation :=
  linear_of_sweep_xr hS DrvX.extractRamSpec hRL

/-- **Reduction of the main theorem** to the sweep and one step of the region loop
(`DrvB.RegStepSpec`), via the region loop `DrvB.regLoopSpec_of`. -/
theorem linear_of_sweep_regStep {s : Machine.Stmt} {κR : ℕ}
    (hR : DrvB.RegStepSpec s κR) : LinearTimeTriangulation :=
  linear_of_sweep_reg hS (DrvB.regLoopSpec_of hR)

/-- **Reduction of the main theorem** to the sweep and the host expansion `DrvB.ExpSpec` of the
base case (the region step from `DrvB.regStepSpec_of` with the host RAM `DrvH.hostRamSpec`). -/
theorem linear_of_sweep_exp (hE : DrvB.ExpSpec) : LinearTimeTriangulation := by
  obtain ⟨s, κ, hR⟩ := DrvB.regStepSpec_of DrvH.hostRamSpec hE
  exact linear_of_sweep_regStep hS hR

/-- **Reduction of the main theorem to the sweep alone**: the down phase is fully proved
(`DrvB.expSpec`). -/
theorem linear_of_sweep : LinearTimeTriangulation :=
  linear_of_sweep_exp hS DrvB.expSpec


end

end

end Chazelle.Core
