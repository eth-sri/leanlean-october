/- Literal metric, cubic, basis table and flat coordinates for the dictionary.
  * The metric in summation and matrix forms.
  * The cubic in complex form det H - tr(H M^dagger M) + det M + conj(det M),
    whose imaginary part vanishes identically.
  * The 27-entry basis table, derived index by index as extDecode of coordinate
    unit vectors.
  * Flat base vectors x, y(theta), z(theta) as decodes of explicit coordinate
    vectors, with s standing for theta^-1 (no inverse is cast to C).
No flatness, frame admission, Phi value or rank statement is made here. -/
module

public import Glennie.Compact.NativeDictionary
public import Glennie.Theorems.CubicNorm

@[expose] public section

namespace Glennie.Compact.NativeDictionary

noncomputable section

def extUnit (n : Fin 27) : Fin 27 → ℝ := fun i => if i = n then 1 else 0

/-! ## The flat base, as explicit coordinates (s stands for theta^-1) -/

end
end Glennie.Compact.NativeDictionary
