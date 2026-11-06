module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMeasurableConstruction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamily
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionDiagonal
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionHeight
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionInterface
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionNormRecovery
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceNormDecay
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # The unconditional Appendix C counterexample -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Filter MeasureTheory Counterexample
open scoped MatrixOrder
open Set HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open scoped Topology ENNReal

/- Autonomous counterexamples for every finite exponent below `4d`, with fixed shared
ellipticity bounds and cylinder, constructed internally in both coefficient classes. -/
theorem kinetic_aleksandrov_autonomous_counterexample_aux
    (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ lam Lam : ℝ, ∃ P₀ : KineticPoint d, ∃ R : ℝ,
      0 < lam ∧ lam ≤ Lam ∧ 0 < R ∧
      ((∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ i k, Measurable (fun z => A z i k)) ∧
          (∀ z, lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)) ∧
       (∃ A : ℕ → (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ j i k, ContDiff ℝ (⊤ : ℕ∞) (fun z => A j z i k)) ∧
          (∀ j z, lam • (1 : PDE.Mat d) ≤ A j z ∧
            A j z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A j (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0))) := by
  apply construction_of_families ?_ d hd p hp hpd
  intro d hd p hp hpd
  have hm : MeasurableFamilyStatement d p (counterParameters d p).1 (counterParameters d p).2.1
      (counterParameters d p).2.2.1 (counterParameters d p).2.2.2 := by
    classical
    let h := counterProfileFor d hd p hp hpd
    have ha := counterAlpha_spec d hd p hp hpd
    let geom := construction_fixed_geometry_of_profile hd ha.1 h
    let R := geom.choose
    let mu := geom.choose_spec.choose
    let S := geom.choose_spec.choose_spec.choose
    have hg := geom.choose_spec.choose_spec.choose_spec
    simpa only [counterParameters, dite_eq_left (And.intro hd (And.intro hp hpd))] using! (construction_measurableFamily_of_geometry hd ha.1 ha.2.1 h p R mu S hp ha.2.2 hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1)
  exact ⟨hm, smoothFamily_of_measurable hp
    (counterParameters_pos d hd p hp hpd).2.2 hm⟩

end HypoellipticAleksandrov.KineticAleksandrov
