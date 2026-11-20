module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalTests
public import RequestProject.LocalConformalTrace
public import RequestProject.LocalConformalMassForcing
public import RequestProject.DiskWeakModes
public import RequestProject.NeumannNormalizedBoundary
public import RequestProject.DiskHardyExtension
public import RequestProject.PlanarNotation

/-!
# Harmonic-mode identities for the genuine Neumann weak equation

The test vectors are obtained from a smooth local inverse. Both their
gradient pairing and their mass pairing come from the actual physical H¹
space. The boundary load is the constructed conformal half trace.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

theorem h1Value_diskHolomorphicH1Test (m : ℕ) :
    h1Value unitDisk (diskHolomorphicH1Test m) = diskHolomorphicArea m :=
  (by measurability)

section

end

end PolyaNeumann

end
