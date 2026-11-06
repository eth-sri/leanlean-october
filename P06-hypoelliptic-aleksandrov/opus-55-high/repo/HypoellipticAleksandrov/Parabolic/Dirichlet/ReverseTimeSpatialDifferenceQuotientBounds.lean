module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import PDEFoundation.Sobolev.Cutoff.Basic

/-!
# Compact reverse-time coefficient difference-quotient bounds

This module derives simultaneous signed spatial difference-quotient bounds for
the smooth reverse-time coefficient fields on a compact time--velocity carrier.
It is pointwise infrastructure for a later commutator calculation.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators Matrix.Norms.Elementwise

variable {d : ℕ} {S : Set (TimeVelocity d)}

end HypoellipticAleksandrov.Parabolic.Dirichlet
