module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Comparison for the viscous terminal problem

Statements for the comparison clauses of Proposition 2.1 and
Proposition 2.1 in the carriers of `EvolutionProblem`.  The viscous
terminal-solution predicate is the one of `IsClassicalTerminalSolution` with `L_ε`
in place of `L`; at `ε = 0` they coincide.

The comparison is carried out in absolute coordinates `(σ, y, z)` on the moving
cylinder `{y ∈ γ(σ) + Ω}`.  This is equivalent to the straightened formulation of the
source (`Y = y - γ(σ)` adds the drift `-γ'(σ) · ∇_Y`) but needs neither piecewise
regularity of `γ` nor any derivative of it: only continuity of `γ` enters.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set Matrix
open scoped MatrixOrder

variable {n : ℕ}

/-- Subtraction for the viscous operator at a slice-regular point. -/
theorem viscousTransportedOperator_sub  {B : FullKineticCoefficient n}
    {b : PDE.VectorField n} {ε : ℝ} {u v : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) (hv : IsSliceRegularAt v p) :
    viscousTransportedOperator B b ε (fun q => u q - v q) p =
      viscousTransportedOperator B b ε u p - viscousTransportedOperator B b ε v p := by
  have h : (fun q  => u q - v q) = fun q => u q + (-1) * v q := by
    funext q
    ring
  rw [h, viscousTransportedOperator_add hu (hv.const_mul (-1)),
    viscousTransportedOperator_const_mul (-1) hv]
  ring

/-- A matrix coefficient with a positive lower Loewner bound is positive semidefinite. -/
theorem posSemidef_of_hasEverywhereLoewnerBounds  {lam Lam : ℝ} (hlam : 0 ≤ lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    (σ : ℝ) (y z : PDE.Vec n) : (B σ y z).PosSemidef := (nonneg_iff_posSemidef.mp
  (LE.le.trans
    (Eq.mpr (id (congrArg (fun _a => _a) (propext nonneg_iff_posSemidef))) (PosSemidef.smul PosSemidef.one hlam))
    (hB σ y z).left))

variable (Ω : PDE.VelocityRegion n) (γ : ℝ → PDE.Vec n) (B : FullKineticCoefficient n) (b : PDE.VectorField n)

/-- The viscous classical terminal-solution predicate: `IsClassicalTerminalSolution` with
`L_ε = L + ε Δ_z` in the equation. -/
def IsClassicalViscousTerminalSolution
     (ε : ℝ)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (u : HypoellipticAleksandrov.KineticScalarField n) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, abs (u p) ≤ C) ∧
    ContinuousOn u (evolutionPastClosedCylinder Ω γ τ) ∧
    ContDiffOn ℝ PDE.smoothOrder
      (fun q => u ⟨q.1, q.2.1, q.2.2⟩)
      (evolutionPastInteriorRaw Ω γ τ) ∧
    (∀ p ∈ evolutionPastOpenCylinder Ω γ τ,
      viscousTransportedOperator B b ε u p = 0) ∧
    (∀ p ∈ evolutionTerminalClosure Ω γ τ,
      u p = F (p.position, p.velocity)) ∧
    (∀ p ∈ evolutionLateralFrontier Ω γ τ, u p = 0)

/-- At `ε = 0` the viscous predicate is `IsClassicalTerminalSolution`. -/
theorem isClassicalViscousTerminalSolution_zero_iff

    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) (u : HypoellipticAleksandrov.KineticScalarField n) :
    IsClassicalViscousTerminalSolution Ω γ B b 0 τ F u ↔
      IsClassicalTerminalSolution Ω γ B b τ F u := by
  simp_all [IsClassicalViscousTerminalSolution, IsClassicalTerminalSolution]

variable {Ω : PDE.VelocityRegion n} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)

include hΩ hγ
/-- The raw interior of the past moving cylinder is open. -/
theorem isOpen_evolutionPastInteriorRaw   (τ : ℝ) :
    IsOpen (evolutionPastInteriorRaw Ω γ τ) := by
  have h1 : IsOpen {q : ℝ × (PDE.Vec n × PDE.Vec n) | q.1 < τ} :=
    isOpen_lt continuous_fst continuous_const
  have hc : Continuous (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => q.2.1 - γ q.1) :=
    (continuous_fst.comp continuous_snd).sub (hγ.comp continuous_fst)
  have h2 := hΩ.preimage hc
  have := h1.inter h2
  convert this using 1
  ext q
  simp only [evolutionPastInteriorRaw, mem_inter_iff, Set.mem_ofPred_eq, mem_preimage,
    mem_movingDomain_iff]

/-- A viscous classical solution is slice regular at every point of the open cylinder. -/
theorem IsClassicalViscousTerminalSolution.isSliceRegularAt
    {B : FullKineticCoefficient n} {b : PDE.VectorField n} {ε τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : HypoellipticAleksandrov.KineticScalarField n}
    (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u)
    {p : KineticPoint n} (hp : p ∈ evolutionPastOpenCylinder Ω γ τ) :
    IsSliceRegularAt u p := (IsSliceRegularAt.of_contDiffAt
  (ContDiffAt.of_le
    (ContDiffOn.contDiffAt hu.right.right.left (IsOpen.mem_nhds (isOpen_evolutionPastInteriorRaw hΩ hγ τ) hp))
    (WithTop.coe_le_coe.mpr le_top)))

end HypoellipticAleksandrov.KineticAleksandrov
