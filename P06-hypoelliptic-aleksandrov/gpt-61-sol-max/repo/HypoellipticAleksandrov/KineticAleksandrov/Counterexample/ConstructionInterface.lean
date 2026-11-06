module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import PDEFoundation.Calculus.RegularityOrder


/-! # Sequence-constructor interface for the Appendix C construction

The family propositions are the two conjuncts of the construction's conclusion. Parameters
are selected from the internally proved profile and fixed-cylinder geometry.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter MeasureTheory
open scoped MatrixOrder

variable (d : ℕ)

/-- The subcritical exponent is fixed before all profile and sequence choices. -/
noncomputable def counterAlpha  (p : ℝ) : ℝ := (if h : 1 ≤ d ∧ 1 ≤ p ∧ p < 4 * ↑d then (exists_subcritical_alpha d h.left p h.right.left h.right.right).choose
else 1 / 2)

section
variable (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ))

include hd hp hpd
/-- The selected exponent satisfies the full source range and positive norm exponent. -/
theorem counterAlpha_spec   :
    0 < counterAlpha d p ∧ counterAlpha d p < 1 ∧
      0 < counterAlpha d p - 2 + 4 * (d : ℝ) / p := by
  classical
  simp only [counterAlpha, dite_eq_left (And.intro hd (And.intro hp hpd))]
  exact (exists_subcritical_alpha d hd p hp hpd).choose_spec

/-- The internally proved profile at the one fixed selected exponent. -/
theorem counterProfileFor   :
    CounterProfileStatement d (counterAlpha d p) :=
  counterProfile_holds d hd _
    (counterAlpha_spec d hd p hp hpd).1 (counterAlpha_spec d hd p hp hpd).2.1
end


/-- Joint ellipticity bounds and cylinder parameters, independent of the sequence index. -/
noncomputable def counterParameters  (p : ℝ) : ℝ × ℝ × KineticPoint d × ℝ := by
  classical
  exact if hvalid : 1 ≤ d ∧ 1 ≤ p ∧ p < 4 * (d : ℝ) then
    let h := counterProfileFor d hvalid.1 p hvalid.2.1 hvalid.2.2
    let geom := construction_fixed_geometry_of_profile hvalid.1
      (counterAlpha_spec d hvalid.1 p hvalid.2.1 hvalid.2.2).1 h
    let mu := geom.choose_spec.choose
    let S := geom.choose_spec.choose_spec.choose
    (profileLowerEllipticity h, profileUpperEllipticity h, ⟨barrierTime mu, 0, 0⟩, S)
  else (1, 1, ⟨0, 0, 0⟩, 1)

/-- The selected joint parameters have the required positive bounds and cylinder radius. -/
theorem counterParameters_pos  (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    0 < (counterParameters d p).1 ∧
      (counterParameters d p).1 ≤ (counterParameters d p).2.1 ∧
      0 < (counterParameters d p).2.2.2 := by
  classical
  let h := counterProfileFor d hd p hp hpd




  simpa only [counterParameters, dite_eq_left (And.intro hd (And.intro hp hpd))] using
    And.intro ((selectedProfile_spec h).1) (And.intro ((selectedProfile_spec h).2.1) (construction_fixed_geometry_of_profile hd (counterAlpha_spec d hd p hp hpd).1 h).choose_spec.choose_spec.choose_spec.2.2.1)

variable (p lam Lam : ℝ) (P₀ : KineticPoint d) (R : ℝ)

/-- The measurable-coefficient family statement. -/
def MeasurableFamilyStatement   : Prop :=
  ∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → HypoellipticAleksandrov.KineticScalarField d,
          (∀ i k, Measurable (fun z => A z i k)) ∧
          (∀ z, lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ PDE.smoothOrder
            (fun q  =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)

/-- The smooth-coefficient family statement. -/
def SmoothFamilyStatement   : Prop :=
  ∃ A : ℕ → (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → HypoellipticAleksandrov.KineticScalarField d,
          (∀ j i k, ContDiff ℝ PDE.smoothOrder (fun z => A j z i k)) ∧
          (∀ j z, lam • (1 : PDE.Mat d) ≤ A j z ∧
            A j z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ PDE.smoothOrder
            (fun q  =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A j (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

namespace HypoellipticAleksandrov.KineticAleksandrov

open Counterexample Filter MeasureTheory
open scoped MatrixOrder

/-- The two family statements at the one selected tuple give the construction. -/
theorem construction_of_families
    (hfamilies : ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 1 ≤ p → p < 4 * (d : ℝ) →
      let params := counterParameters d p
      MeasurableFamilyStatement d p params.1 params.2.1 params.2.2.1 params.2.2.2 ∧
      SmoothFamilyStatement d p params.1 params.2.1 params.2.2.1 params.2.2.2)
    (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ lam Lam : ℝ, ∃ P₀ : KineticPoint d, ∃ R : ℝ,
      0 < lam ∧ lam ≤ Lam ∧ 0 < R ∧
      ((∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → HypoellipticAleksandrov.KineticScalarField d,
          (∀ i k, Measurable (fun z => A z i k)) ∧
          (∀ z, lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ PDE.smoothOrder
            (fun q  =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)) ∧
       (∃ A : ℕ → (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → HypoellipticAleksandrov.KineticScalarField d,
          (∀ j i k, ContDiff ℝ PDE.smoothOrder (fun z => A j z i k)) ∧
          (∀ j z, lam • (1 : PDE.Mat d) ≤ A j z ∧
            A j z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ PDE.smoothOrder
            (fun q  =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A j (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0))) := by
  have hpos := counterParameters_pos d hd p hp hpd
  have hf := hfamilies d hd p hp hpd
  exact ⟨_, _,
    _, _,
    hpos.1, hpos.2.1, hpos.2.2, hf.1, hf.2⟩

end HypoellipticAleksandrov.KineticAleksandrov
