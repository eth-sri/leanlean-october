module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
public import Mathlib.MeasureTheory.Measure.Prod
public import HypoellipticAleksandrov.Ambient.TypeAbbrev

/-! # Negation invariance of the native spatial product volume -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- The native spatial volume is invariant under simultaneous coordinate negation. -/
instance nativeSpatialVolume_isNegInvariant (d : ℕ) :
    Measure.IsNegInvariant (volume : Measure (PDE.Vec d × PDE.Vec d)) := by
  constructor
  change Measure.map (fun q : PDE.Vec d × PDE.Vec d => (-q.1, -q.2))
    ((HypoellipticAleksandrov.VecVolume d).prod volume) = volume.prod volume
  exact ((HypoellipticAleksandrov.VecVolume d).measurePreserving_neg.prod
    (HypoellipticAleksandrov.VecVolume d).measurePreserving_neg).map_eq

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
