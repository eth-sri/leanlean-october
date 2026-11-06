module
import Mathlib
public import Mathlib.NumberTheory.ZetaValues
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.EulerMaclaurin

@[expose] public section

open Complex
open scoped BigOperators

namespace GuthMaynard.NativeMoment


/-!
# The periodic Euler--Maclaurin functions in DFI equation (12)

DFI write their periodic function as a paired Fourier series.  The canonical
real representative is the periodized Bernoulli polynomial `B_j({x}) / j!`.
For `j = 1` its value at an integer is immaterial to every Lebesgue integral;
we use the right-continuous representative, which is exactly the `B1` used by
the pinned Euler--Maclaurin theorem.
-/






