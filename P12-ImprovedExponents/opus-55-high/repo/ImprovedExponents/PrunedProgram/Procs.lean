
import ThreeSumApsp.Slots
import Mathlib.Data.Nat.Notation


/-!
# The numbers of the procedures of the pruned solver

The pruned thin-product solver is `programRS G r s` (`ImprovedExponents.Pipeline.RegimeRS`, whose
last procedure has the number 76) followed by copies of upstream's procedures in which one callee
is exchanged: the encoder gets a budget of symbols `P₀`, and the chain from the shared stage to
the solver of all instances calls the new procedures.  The bodies of the tile preprocessing, the
queries, the band arrays and the slices are upstream's and keep their numbers.
-/

namespace ImprovedExponents.Proc

/- The pruned encoder (`encodePBody`). -/
slots 77 encodeP
/- The encodings of all bands with the pruned encoder (`encodeBandsPBody`). -/
slots 78 encodeBandsP
/- The shared stage with the pruned encoder (`sharedPBody`). -/
slots 79 sharedP
/- The preprocessing of Theorem 30 with the pruned shared stage (`preCorePBody`). -/
slots 80 preCoreP
/- The preprocessing with rational parameters calling `preCoreP` (`pre31PBody`). -/
slots 81 pre31P
/- The offline routine calling `pre31P` (`offline32PBody`). -/
slots 82 offline32P
/- The solver of all instances with the test `D^r ≤ N^s` and the routine `offline32P`
(`allBody Proc.testRS Proc.offline32P`). -/
slots 83 allP
