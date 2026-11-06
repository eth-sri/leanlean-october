module
public import GuthMaynard.NativeSource.GuthMaynard.TypeIReflection

@[expose] public section

open Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace GuthMaynard.NativeMoment

/-!
# Shared logarithmic Fourier deweighting

The main theorem is deliberately independent of the Type-I cutoff.  Any
Schwartz weight in logarithmic coordinates is removed by the same exact
Fourier-inversion identity, so the theorem applies both before reflection and
to the smooth weight on the reflected `T/N` block.
-/

end GuthMaynard.NativeMoment
