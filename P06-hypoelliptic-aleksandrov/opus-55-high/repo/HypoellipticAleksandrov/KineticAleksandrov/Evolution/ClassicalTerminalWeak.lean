module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator

/-! # Weak equations supplied by classical viscous terminal solutions -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Set MeasureTheory Evolution

variable {n : ℕ} {Ω : Set (PDE.Vec n)}

/-- The exact product-coordinate interior is the image of the kinetic interior. -/
theorem evolutionPastInteriorRaw_eq_image  (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) :
    evolutionPastInteriorRaw Ω γ τ =
      KineticPoint.equivProd n '' evolutionPastOpenCylinder Ω γ τ := by
  aesop

/-- The past kinetic interior is open for an open domain and a continuous curve. -/
theorem isOpen_evolutionPastOpenCylinder  (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) (τ : ℝ) :
    IsOpen (evolutionPastOpenCylinder Ω γ τ) := (isOpen_evolutionPastInteriorRaw hΩ hγ τ).preimage
    (KineticPoint.homeomorphProd n).continuous

/-- A classical viscous terminal solution satisfies the literal weak adjoint equation. -/
theorem classical_viscous_terminalSolution_isWeak 
    (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) {b : PDE.Vec n → PDE.Vec n}
    (hb : IsSmoothDrift b) {ε τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u) :
    IsKineticWeakRegularizedSolution B b ε (evolutionPastOpenCylinder Ω γ τ) u
      (fun _ => 0) := by
  let U := evolutionPastOpenCylinder Ω γ τ
  have hU := isOpen_evolutionPastOpenCylinder hΩ hγ τ
  have hP := (evolutionHomeomorph n).continuous.isOpen_preimage U hU
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' U) := by
    apply contDiffOn_comp_evolutionHomeomorph_iff.mpr
    rw [← evolutionPastInteriorRaw_eq_image]
    exact hu.2.2.1
  apply (isWeakRegularizedSolution_comp_iff B b ε U u _).mp
  refine ⟨hs.continuousOn.locallyIntegrableOn hP.measurableSet, ?_⟩
  intro ψ hψ hc hsupport
  rw [integral_regularizedAdjoint_contDiffOn hP hB hBs hb ε hs ψ hψ hc hsupport]
  have heq : (∫ x in evolutionHomeomorph n ⁻¹' U,
      regularizedOperator B b ε (u ∘ evolutionHomeomorph n) x * ψ x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [regularizedOperator_comp ε ((hs.contDiffAt (hP.mem_nhds hx)).of_le (by simp))]
    change viscousTransportedOperator B b ε u _ * ψ x = 0
    rw [hu.2.2.2.1 _ hx, zero_mul]
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov
