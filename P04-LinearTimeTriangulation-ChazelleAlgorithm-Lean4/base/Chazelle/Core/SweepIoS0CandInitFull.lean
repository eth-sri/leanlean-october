module

public import Chazelle.Core.SweepIoS0CandInitMain
public import Chazelle.Core.SweepIoS0CandBsMain

/-!
# The sweep RAM (WP-D), answers: the initialisation of the side-0 candidates, unconditionally

`initPartSpec : InitPartSpec` from `initPart` and the binary search `lsearchSpec`.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

@[expose] public section

/-- **The initialisation contract of the side-0 stop and table candidates.** -/
theorem initPartSpec : InitPartSpec := initPart lsearchSpec

end

end S0C

end SweepIo

end Chazelle.Core
