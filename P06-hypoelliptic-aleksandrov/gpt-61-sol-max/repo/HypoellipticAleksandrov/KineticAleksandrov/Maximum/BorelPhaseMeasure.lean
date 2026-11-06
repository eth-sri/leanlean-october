module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
import Mathlib.MeasureTheory.Measure.Prod

/-! # Lifting time--velocity null sets to phase space -/

 public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- Tonelli lifts every a.e. time--velocity assertion, with no position dependence. -/
theorem borel_timeVelocity_ae_lift {d : ℕ} {p : (ℝ × PDE.Vec d) → Prop}
    (hp : ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)), p z) :
    ∀ᵐ P ∂(volume : Measure (KineticPoint d)), p (P.time,P.velocity) := (Measure.QuasiMeasurePreserving.ae
  (MeasurePreserving.quasiMeasurePreserving (KineticPoint.measurePreserving_equivProd d))
  (Measure.QuasiMeasurePreserving.ae
    (Measure.QuasiMeasurePreserving.comp Measure.quasiMeasurePreserving_fst
      (MeasurePreserving.quasiMeasurePreserving
        (MeasurePreserving.comp (MeasurePreserving.symm MeasurableEquiv.prodAssoc volume_preserving_prodAssoc)
          (MeasurePreserving.prod (MeasurePreserving.id volume) Measure.measurePreserving_swap))))
    hp))

end HypoellipticAleksandrov.KineticAleksandrov
