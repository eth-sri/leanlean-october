module

public import RequestProject.NeumannBoundaryPole
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Energy comparison for the genuine Neumann boundary maps

The inverse difference identity is applied to the actual weak Helmholtz
form `B_E = I - (E + 1) J†J`. Compactness of `J†J` then proves compactness
of the differences of the actual H¹ solution maps and L² NtD maps.
At energy `-1` the form is the identity, so this reference energy requires
no nonnegative-energy or nonresonance assumption.

These are identities for the genuine ordinary-`dθ` boundary maps. They do
not assert a fractional trace estimate or a conformal principal symbol.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace






end PolyaNeumann

end
