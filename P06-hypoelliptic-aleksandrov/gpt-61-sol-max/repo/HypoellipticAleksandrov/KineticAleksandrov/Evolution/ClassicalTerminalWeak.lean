module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
import Aesop
public import PDEFoundation.Calculus.RegularityOrder




/-! # Weak equations supplied by classical viscous terminal solutions -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Evolution

variable {n : ℕ}

/-- The exact product-coordinate interior is the image of the kinetic interior. -/
theorem evolutionPastInteriorRaw_eq_image  (Ω : PDE.VelocityRegion n)
    (γ : ℝ → PDE.Vec n) (τ : ℝ) :
    evolutionPastInteriorRaw Ω γ τ =
      KineticPoint.equivProd n '' evolutionPastOpenCylinder Ω γ τ := by
  aesop

variable {Ω : PDE.VelocityRegion n} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)

include hΩ hγ
/-- The past kinetic interior is open for an open domain and a continuous curve. -/
theorem isOpen_evolutionPastOpenCylinder   (τ : ℝ) :
    IsOpen (evolutionPastOpenCylinder Ω γ τ) := (isOpen_evolutionPastInteriorRaw hΩ hγ τ).preimage
    (KineticPoint.homeomorphProd n).continuous

/-- A classical viscous terminal solution satisfies the literal weak adjoint equation. -/
theorem classical_viscous_terminalSolution_isWeak
    {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) {b : PDE.VectorField n}
    (hb : IsSmoothDrift b) {ε τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    {u : HypoellipticAleksandrov.KineticScalarField n}
    (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u) :
    IsKineticWeakRegularizedSolution B b ε (evolutionPastOpenCylinder Ω γ τ) u
      (fun _ => 0) := by
  let U := evolutionPastOpenCylinder Ω γ τ

  have hP := (evolutionHomeomorph n).continuous.isOpen_preimage U (isOpen_evolutionPastOpenCylinder hΩ hγ τ)
  have hs : ContDiffOn ℝ PDE.smoothOrder (u ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' U) := by
    apply contDiffOn_comp_evolutionHomeomorph_iff.mpr
    change ContDiffOn ℝ PDE.smoothOrder _
      (KineticPoint.equivProd n '' evolutionPastOpenCylinder Ω γ τ)
    rw [← evolutionPastInteriorRaw_eq_image]
    exact hu.2.2.1
  apply (isWeakRegularizedSolution_comp_iff B b ε U u (fun _ => 0)).mp
  refine ⟨hs.continuousOn.locallyIntegrableOn hP.measurableSet, ?_⟩
  intro ψ hψ hc hsupport
  rw [integral_regularizedAdjoint_contDiffOn hP hB hBs hb ε hs ψ hψ hc hsupport]
  have heq : (∫ x in evolutionHomeomorph n ⁻¹' U,
      regularizedOperator B b ε (u ∘ evolutionHomeomorph n) x * ψ x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [regularizedOperator_comp ε ((hs.contDiffAt (hP.mem_nhds hx)).of_le (by simp))]
    change viscousTransportedOperator B b ε u (evolutionHomeomorph n x) * ψ x = 0
    rw [hu.2.2.2.1 _ hx, zero_mul]
  rw [heq]
  simp only [Function.comp_apply, zero_mul, integral_zero]

end HypoellipticAleksandrov.KineticAleksandrov
