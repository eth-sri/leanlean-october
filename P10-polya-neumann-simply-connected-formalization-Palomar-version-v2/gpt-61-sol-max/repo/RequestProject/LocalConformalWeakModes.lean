module

public import RequestProject.DiskHardyExtension


public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalTests
public import RequestProject.LocalConformalTrace
public import RequestProject.LocalConformalMassForcing
public import RequestProject.DiskWeakModes
public import RequestProject.NeumannNormalizedBoundary

/-!
# Harmonic-mode identities for the genuine Neumann weak equation

The test vectors are obtained from a smooth local inverse. Both their
gradient pairing and their mass pairing come from the actual physical H¹
space. The boundary load is the constructed conformal half trace.
-/

public section




namespace PolyaNeumann

open MeasureTheory Set Metric Real

theorem h1Value_diskHolomorphicH1Test m :
    h1Value unitDisk (diskHolomorphicH1Test m) = diskHolomorphicArea m :=
  h1Value_smoothTraceH1 unitDisk
    ⟨diskHarmonicCutoff (diskHolomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)⟩

end PolyaNeumann
