module

public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! # Measurable fixed-time convergence and positive-part norm convergence -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory
open scoped Topology ENNReal

/- Measurable convergence at almost every spatial point at each time yields convergence
in the literal kinetic product-volume carrier. -/
theorem construction_fixed_time_tendsto_ae_spacetime {d }
    (F : ℕ → ℝ × XV d → ℝ) (g : ℝ × XV d → ℝ)
    (hF : ∀ n, Measurable (F n)) (hg : Measurable g)
    (ht : ∀ t : ℝ, ∀ᵐ q ∂volume,
      Tendsto (fun n => F n (t, q)) atTop (𝓝 (g (t, q)))) :
    ∀ᵐ P : KineticPoint d ∂volume,
      Tendsto (fun n => F n (KineticPoint.equivProd d P)) atTop
        (𝓝 (g (KineticPoint.equivProd d P))) := by
  have hp := measurableSet_tendsto_fun (l := atTop) hF hg
  have he : ∀ᵐ z : ℝ × XV d ∂volume,
      Tendsto (fun n => F n z) atTop (𝓝 (g z)) :=
    (Measure.ae_prod_iff_ae_ae hp).mpr (Eventually.of_forall ht)
  exact (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving.ae he

/- Uniformly bounded measurable convergence controls the positive-part source error in
any finite exponent on a finite-measure cylinder. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
