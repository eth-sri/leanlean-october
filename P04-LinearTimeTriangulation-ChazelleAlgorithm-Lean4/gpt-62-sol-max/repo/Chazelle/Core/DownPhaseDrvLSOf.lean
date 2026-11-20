module

public import Chazelle.Core.DownPhaseDrvLSMain
public import Chazelle.Core.DownPhaseDrvRLvE

/-!
# Down-phase driver: one level from its parts (`LevelSpec`), the instance

**`levelSpec_of`**: the host RAM, the region procedure, the extraction (programs from
`hostMeets_of`, `regMeets_of`, `extMeets_of`), the region loop of the driver
(`DrvR.lvLoop_exec`), the tail (`LvTailSpec`) and the level cost (`LvCostSpec`) give
`LevelSpec (gradeCtx O) lvCnt n₀` (`DrvLS.levelSpec_of_loop`).
-/

namespace Chazelle.Core

namespace DrvLS

open DrvR

@[expose] public section

/-- **One level of the down phase from its parts.** -/
theorem levelSpec_of {O : OracleIface} (hH : HostRamSpec) (hReg : RegionSpec O)
    (hX : ExtractRamSpec) (hT : LvTailSpec O) (hR1 : HostR1Spec) (hLM : LevelMathSpec)
    (hC : LvCostSpec) : ∃ n₀, LevelSpec (gradeCtx O) lvCnt n₀ := by
  obtain ⟨sH, κH, hHm⟩ := hostMeets_of hH
  obtain ⟨sR, κR, hRm⟩ := regMeets_of hReg
  obtain ⟨sX, κX, hXm⟩ := extMeets_of hX
  exact levelSpec_of_loop (sH := sH) (sR := sR) (sX := sX) (κH := κH) (κR := κR) (κX := κX)
    (fun P W c₁ c L E reg lam Kb ctx hKb hroom hinv0 =>
      lvLoop_exec hHm hRm hXm hR1 hLM ctx hKb hroom hinv0) hT hC

end

end DrvLS

end Chazelle.Core
