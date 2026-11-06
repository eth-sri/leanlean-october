module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Negation invariance of the native spatial product volume -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- The native spatial volume is invariant under simultaneous coordinate negation. -/
instance nativeSpatialVolume_isNegInvariant (d : ℕ) :
    Measure.IsNegInvariant (volume : Measure (PDE.Vec d × PDE.Vec d)) := ({
  neg_eq_self :=
    id (MeasurePreserving.prod (Measure.measurePreserving_neg volume) (Measure.measurePreserving_neg volume)).map_eq })

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
