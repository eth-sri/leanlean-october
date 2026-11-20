module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual smoothness and pointwise viscous equation for the exhaustion candidate -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/-- The actual continuous zero extension is smooth and solves the viscous equation
pointwise on every strict bounded inner cylinder, relative to the explicit Hörmander input. -/
theorem classical_innerBallDirichletLimit_on_innerCylinder
    {n : ℕ} (E : InnerBallExhaustion n)
    {δ0 S0 : ℝ} (hδ0 : 0 < δ0) (hδr : δ0 < E.r0) (hεpos : 0 < E.ε) :
    ContDiffOn ℝ (⊤ : ℕ∞) (E.limit ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' (E.innerOpen δ0 S0)) ∧
    ∀ p ∈ E.innerOpen δ0 S0,
      viscousTransportedOperator E.B E.b E.ε (E.limit) p = 0 := by
  let U := (E.innerOpen δ0 S0)
  have hU : IsOpen U := isOpen_boundedInnerOpenCylinder _ E.hΓ _ _ _
  have hclosed := boundedInnerOpenCylinder_subset_closed (E.r0 - δ0) E.Γ E.α E.τ S0
  have hcont := (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S0) E hδ0 hδr).1.mono hclosed
  have hw := weakRegularized_innerBall_dirichlet_limit (S0 := S0) E hδ0 hδr
  obtain ⟨hsm, he⟩ := classical_kinetic_of_continuous_weak E.hlam E.hB E.hBs E.hBsym E.hbs hεpos hU hcont hw
  have hEq : EqOn (E.limit)
      (fun p => E.pointLimit p) U :=
    fun _ hp => E.limit_eq
      (innerClosedCylinder_subset_movingBall hδ0 hδr (hclosed hp))
  refine ⟨hsm.congr (fun _ hx => hEq hx), fun p hp => ?_⟩
  have hn : ∀ᶠ q in 𝓝 p, q ∈ U := hU.mem_nhds hp
  rw [viscousTransportedOperator_congr_germ E.B E.b E.ε (hn.mono fun _ hq => hEq hq)]
  exact he p hp

end HypoellipticAleksandrov.KineticAleksandrov
