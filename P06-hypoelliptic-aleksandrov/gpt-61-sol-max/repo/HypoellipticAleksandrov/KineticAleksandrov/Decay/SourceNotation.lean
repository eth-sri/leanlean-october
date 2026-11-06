module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Literal notation for the Section 3 source proofs

These definitions specify curves, query lifts, polynomial barriers, phases, and
block constants. They assert no PDE existence or analytic estimate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open Set MeasureTheory
open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped MatrixOrder

/-- Literal Section 3 notation: `TV`. -/
abbrev TV {d : ℕ} (ν : ComplexMeasure (PDE.Vec d)) : ℝ :=
  (ν.variation univ).toReal

variable {d : ℕ}

/-- Literal Section 3 notation: `stationary`. -/
def stationary  : ℝ → PDE.Vec d := fun _ => 0

/-- Literal Section 3 notation: `SourceCase`. -/
def SourceCase  (D : PDE.VelocityRegion d) (b : PDE.VectorField d)
    (m Lb : ℝ) : Prop :=
  (D = univ ∧ b = id ∧ m = 1 ∧ Lb = 1) ∨
  (∃ hd : d = 1, ∃ a c : ℝ, a < c ∧ hd ▸ D = PDE.oneDimensionalAxisBox a c)

/-- Literal Section 3 notation: `SourceSetting`. -/
def SourceSetting  (lam Lam m Lb : ℝ) (D : PDE.VelocityRegion d)
    (B : CoefficientField d) (b : PDE.VectorField d) : Prop :=
  IsSectionTwoCoefficient lam Lam B ∧ IsSmoothDrift b ∧
  0 < m ∧ m ≤ Lb ∧ HasTransportBounds m Lb b ∧ SourceCase D b m Lb

section
variable {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d} (σ τ : ℝ) (hστ : σ ≤ τ)

/-- Literal Section 3 notation: `movingQuery`. -/
def movingQuery   (v z : PDE.Vec d)
    (hv : v ∈ movingDomain Ω γ σ) : EvolutionQuery Ω γ :=
  ⟨(σ, τ, v, z), hστ, hv, mem_univ z⟩

/-- Literal Section 3 notation: `scalarQuery`. -/
def scalarQuery   (v : PDE.Vec d)
    (hv : v ∈ movingDomain Ω γ σ) : ParabolicEvolutionQuery Ω γ :=
  ⟨(σ, τ, v), hστ, hv⟩
end


/-- Literal Section 3 notation: `P`. -/
abbrev P {d : ℕ} {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (q : ParabolicEvolutionQuery Ω γ) : Measure (PDE.Vec d) :=
  parabolicMarginalAmbientMeasure K hΩ q

variable {d : ℕ}

/-- Literal Section 3 notation: `phaseCoordinate`. -/
def phaseCoordinate  (ξ z0 : PDE.Vec d)
    (x : EvolutionAmbientState d) : ℝ := PDE.vecDot ξ (x.2 - z0)

/-- Literal Section 3 notation: `barrier`. -/
def barrier  (N : ℕ) (s : ℝ) (Y : PDE.Vec d) : ℝ :=
  (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ N

/-- Literal Section 3 notation: `Hess`. -/
abbrev Hess {d : ℕ} (f : PDE.ScalarField d) (Y : PDE.Vec d) : PDE.Mat d :=
  scalarSpatialHessian (fun z  => f z.2) (0, Y)

variable (d N : ℕ)

/-- Literal Section 3 notation: `barrierC`. -/
def barrierC  (lam Lam : ℝ) : ℝ :=
  4 * N * (N - 1 : ℕ) * lam - 2 * N * d * Lam

/-- Literal Section 3 notation: `barrierRate`. -/
def barrierRate  (lam Lam s H : ℝ) : ℝ :=
  2 * N * d * Lam / s ^ 2 + (N : ℝ) ^ 2 * H ^ 2 / barrierC d N lam Lam

variable {d : ℕ}

/-- `HasCurveSpeedOn H γ σ τ`: at every differentiable interior time the Euclidean speed of `γ`
is at most `H`.  (Corners are excluded.) -/
def HasCurveSpeedOn  (H : ℝ) (γ : ℝ → PDE.Vec d) (σ τ : ℝ) : Prop :=
  ∀ r ∈ Ioo σ τ, DifferentiableAt ℝ γ r → PDE.vecEuclideanNorm (deriv γ r) ≤ H

/-- The source phase center `∫_σ^τ ξ · b(γ(r)) dr`. -/
def phaseCenter  (ξ : PDE.Vec d) (b : PDE.VectorField d)
    (γ : ℝ → PDE.Vec d) (σ τ : ℝ) : ℝ :=
  ∫ r in σ..τ, PDE.vecDot ξ (b (γ r))

/-- The source tent profile `𝖿(t) = min {t, 1, L₀ - t}`. -/
def tent (L0 t : ℝ) : ℝ := min t (min 1 (L0 - t))

/-- The source duration `L₀ = 2 + 2π / m` of the two opposite tubes. -/
def blockL0 (m : ℝ) : ℝ := 2 + 2 * Real.pi / m

/-- The source radius `ρ = min {1, (128 L_b)^(-1/3)}`. -/
def blockRho (Lb : ℝ) : ℝ := min 1 ((128 * Lb) ^ (-(1 / 3 : ℝ)))

variable (m Lb : ℝ)

/-- The source tube radius `η = min {ρ / 4, 1 / (8 L_b L₀)}`. -/
def blockEta  : ℝ :=
  min (blockRho Lb / 4) (1 / (8 * Lb * blockL0 m))

/-- The source block length `L = L₀ + 4ρ²`. -/
def blockTime  : ℝ := blockL0 m + 4 * blockRho Lb ^ 2

/-- The source fitting radius `R_* = 1 + 4ρ`. -/
def blockOuter (Lb : ℝ) : ℝ := 1 + 4 * blockRho Lb

/-- The source retained mass `m₀ = exp (-C_* (η⁻² + 1/4) L₀)`. -/
def blockMass (Cstar m Lb : ℝ) : ℝ :=
  Real.exp (-Cstar * ((blockEta m Lb)⁻¹ ^ 2 + 1 / 4) * blockL0 m)

variable {d : ℕ}

/-- The signed source phase comparison barrier. -/
def phaseBarrier  (sgn : ℝ) (ξ z0 : PDE.Vec d)
    (b : PDE.VectorField d) (γ : ℝ → PDE.Vec d)
    (σ Lb ρ : ℝ) (p : KineticPoint d) : ℝ :=
  sgn * (PDE.vecDot ξ (p.velocity - z0) - phaseCenter ξ b γ σ p.time) -
    Lb * ρ * (p.time - σ)

/-- The source quadratic barrier controlling the transported infinity. -/
def infinityBarrier  (η M τ : ℝ) (z0 : PDE.Vec d)
    (p : KineticPoint d) : ℝ :=
  η * (1 + PDE.vecNormSq (p.velocity - z0)) * Real.exp ((M + 1) * (τ - p.time))

/-- Interchange diffused and transported coordinates, preserving time. -/
def swapDiffusedTransported  (p : KineticPoint d) : KineticPoint d :=
  ⟨p.time, p.velocity, p.position⟩

section
variable {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d} (σ τ : ℝ) (hστ : σ ≤ τ)

/-- The query lift preserves the two times and both source coordinates. -/
@[simp]
theorem movingQuery_val   (v z : PDE.Vec d)
    (hv : v ∈ movingDomain Ω γ σ) :
    (movingQuery σ τ hστ v z hv).val = (σ, τ, v, z) := rfl

/-- The scalar query lift preserves the two times and source position. -/
@[simp]
theorem scalarQuery_val   (v : PDE.Vec d)
    (hv : v ∈ movingDomain Ω γ σ) :
    (scalarQuery σ τ hστ v hv).val = (σ, τ, v) := rfl
end


/-- The coordinate interchange is an involution. -/
@[simp]
theorem swapDiffusedTransported_swap  (p : KineticPoint d) :
    swapDiffusedTransported (swapDiffusedTransported p) = p := rfl

end HypoellipticAleksandrov.KineticAleksandrov.Decay
