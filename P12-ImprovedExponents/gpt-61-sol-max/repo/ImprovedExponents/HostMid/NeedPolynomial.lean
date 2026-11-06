module

public import Mathlib.Tactic
public import ImprovedExponents.HostMid.Program

@[expose] public section

/-!
# The need of the variant host stays polynomial

The need of the variant host is upstream's need over a solver whose parameters `[n, D, w]` are
rewritten to `[n, midSize D g, w]` (`hostNeed'_eq`), and rewriting keeps a need polynomially
bounded because `midSize D g ≤ D` (`polyNeedN_midArgs`).  So upstream's `hostNeed_poly` applies.
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3

/-- **The need of the variant host stays polynomial**, if the parameters, the numbers that the
parameter procedures form, and the need of the solver are polynomially bounded. -/
def hostNeed_poly' {Dfun Gfun wD wG : ℕ → ℕ} {need}
     hD (hG : PolyBounded fun n _ => Gfun (Dfun n))
    (hwD : PolyBounded fun n _ => wD n) (hwG : PolyBounded fun n _ => wG (Dfun n))
    (h : PolyNeedN need) :=
  hostNeed_poly hD hG hwD hwG (polyNeedN_midArgs Gfun h)

end ImprovedExponents.HostMid
