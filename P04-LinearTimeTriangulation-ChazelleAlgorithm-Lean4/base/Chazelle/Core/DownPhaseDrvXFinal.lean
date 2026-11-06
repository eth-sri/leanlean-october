module

public import Chazelle.Core.DownPhaseDrvXMain
public import Chazelle.Core.DownPhaseDrvXGlueA
public import Chazelle.Core.DownPhaseDrvXGlueB

/-!
# Down phase, extraction (D6): `DrvX.extractRamSpec : DrvR.ExtractRamSpec`

The assembly `extractRamSpec_of` (`DownPhaseDrvXMain`) with the two pieces of glue
`xeGlue` (`DownPhaseDrvXGlueA`) and `postMath` (`DownPhaseDrvXGlueB`).
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

/-- **D6: the extraction RAM meets its contract.** -/
theorem extractRamSpec : DrvR.ExtractRamSpec := extractRamSpec_of xeGlue postMath

end

end DrvX

end Chazelle.Core
