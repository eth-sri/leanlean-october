module

public import Chazelle.Core.SweepIoS0CandInitFull
public import Chazelle.Core.SweepIoS0CandQ5

/-!
# The sweep RAM (WP-D), answers: the side-0 candidate preparation (`S0CandSpec`)

`S0CandSpec` from the per-query step `S0C.s0CandSpec_of` and the initialisation
`S0C.initPartSpec`.
-/

namespace Chazelle.Core

namespace SweepIo

@[expose] public section

/-- **`S0CandSpec`**. -/
theorem s0CandSpec : S0CandSpec := S0C.s0CandSpec_of S0C.initPartSpec

end

end SweepIo

end Chazelle.Core
