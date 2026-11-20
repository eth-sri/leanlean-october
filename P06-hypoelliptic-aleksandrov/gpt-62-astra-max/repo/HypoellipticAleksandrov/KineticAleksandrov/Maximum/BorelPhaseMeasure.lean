module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
import Mathlib.MeasureTheory.Measure.Prod

/-! # Lifting time--velocity null sets to phase space -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- Tonelli lifts every a.e. time--velocity assertion, with no position dependence. -/
theorem borel_timeVelocity_ae_lift {d : ℕ} {p : (ℝ × PDE.Vec d) → Prop}
    (hp : ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)), p z) :
    ∀ᵐ P ∂(volume : Measure (KineticPoint d)), p (P.time,P.velocity) := by
  have hproj : Measure.QuasiMeasurePreserving
      (Prod.fst : (ℝ × PDE.Vec d) × PDE.Vec d → ℝ × PDE.Vec d) volume volume :=
    Measure.quasiMeasurePreserving_fst
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℝ × PDE.Vec d) × PDE.Vec d ≃ᵐ
        ℝ × (PDE.Vec d × PDE.Vec d)) volume volume := volume_preserving_prodAssoc
  have hp' := (hproj.comp ((MeasurePreserving.symm MeasurableEquiv.prodAssoc hassoc).comp ((MeasurePreserving.id volume).prod Measure.measurePreserving_swap)).quasiMeasurePreserving).ae hp
  exact (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving.ae hp'

end HypoellipticAleksandrov.KineticAleksandrov
