module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import HypoellipticAleksandrov.Parabolic.Geometry

/-!
# Section 5 geometry and reflection API

Literal source definitions and complete formula characterizations.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory
open scoped MatrixOrder Matrix.Norms.Elementwise
open HypoellipticAleksandrov.Parabolic

/-- The forward cylinder in physical `(s,X,v)` coordinates, with positive radius. -/
def forwardCylinder {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    Set (KineticPoint d) :=
  {P | Z₀.time < P.time ∧ P.time < Z₀.time + R ^ 2 ∧
    P.velocity ∈ PDE.euclideanBall Z₀.velocity R ∧
    relativePosition Z₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d) (R ^ 3)}

/-- Complete literal membership characterization of the forward cylinder. -/
theorem mem_forwardCylinder_iff {d : ℕ} (Z₀ P : KineticPoint d)
    (R : ℝ) (hR : 0 < R) :
    P ∈ forwardCylinder Z₀ R hR ↔
      Z₀.time < P.time ∧ P.time < Z₀.time + R ^ 2 ∧
        P.velocity ∈ PDE.euclideanBall Z₀.velocity R ∧
        relativePosition Z₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d) (R ^ 3) := Iff.rfl

/-- Terminal, velocity, and outgoing or grazing position faces of the forward cylinder. -/
def exitBoundary {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    Set (KineticPoint d) :=
  closure (forwardCylinder Z₀ R hR) ∩
    ({P | P.time = Z₀.time + R ^ 2} ∪
      {P | P.velocity ∈ PDE.euclideanSphere Z₀.velocity R} ∪
      {P | relativePosition Z₀ P ∈
          PDE.euclideanSphere (0 : PDE.Vec d) (R ^ 3) ∧
        0 ≤ PDE.vecDot (relativeVelocity Z₀ P) (relativePosition Z₀ P)})

/-- Complete face-by-face characterization of the exit boundary. -/
theorem mem_exitBoundary_iff {d : ℕ} (Z₀ P : KineticPoint d)
    (R : ℝ) (hR : 0 < R) :
    P ∈ exitBoundary Z₀ R hR ↔
      P ∈ closure (forwardCylinder Z₀ R hR) ∧
        (P.time = Z₀.time + R ^ 2 ∨
          P.velocity ∈ PDE.euclideanSphere Z₀.velocity R ∨
          (relativePosition Z₀ P ∈ PDE.euclideanSphere (0 : PDE.Vec d) (R ^ 3) ∧
            0 ≤ PDE.vecDot (relativeVelocity Z₀ P) (relativePosition Z₀ P))) := by
  simp only [exitBoundary, mem_inter_iff, mem_union, mem_ofPred_eq, or_assoc]

/-- Source reflection of time and position, leaving velocity fixed. -/
def kineticReflection {d : ℕ} (P : KineticPoint d) : KineticPoint d :=
  ⟨-P.time, -P.position, P.velocity⟩

/-- Reflection is an involution on the same kinetic carrier. -/
theorem kineticReflection_involutive {d : ℕ} :
    Function.Involutive (kineticReflection (d := d)) := by
  intro P
  ext <;> simp [kineticReflection]

/-- Pull back a time-velocity coefficient by the source time reflection about zero. -/
def kineticReflectedCoefficient {d : ℕ} (A : CoefficientField d) : CoefficientField d :=
  fun s v => A (-s) v

/-- The general forward kinetic operator in literal `(s,X,v)` field order. -/
def forwardKineticOperator {d : ℕ} (A : FullKineticCoefficient d)
    (U : KineticPoint d → ℝ) (P : KineticPoint d) : ℝ :=
  kineticTimeDerivative U P + PDE.vecDot P.velocity (kineticPositionGradient U P) +
    matrixContraction (fullKineticCoefficientAt A P) (kineticVelocityHessian U P)

/-- Complete literal characterization of the general forward kinetic operator. -/
theorem forwardKineticOperator_apply {d : ℕ} (A : FullKineticCoefficient d)
    (U : KineticPoint d → ℝ) (P : KineticPoint d) :
    forwardKineticOperator A U P =
      kineticTimeDerivative U P + PDE.vecDot P.velocity (kineticPositionGradient U P) +
        matrixContraction (A P.time P.position P.velocity) (kineticVelocityHessian U P) :=
  rfl

/-- Literal inner scaling factor, restricted to the source parameter carrier. -/
def innerRatio (R : ℝ) (hR : 0 < R) (δ : ℝ)
    (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) : ℝ :=
  Real.sqrt (1 - 2 * δ / R ^ 2)

/-- The explicit inner cylinder in the original centre's relative coordinates. -/
def innerCylinder {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) : Set (KineticPoint d) :=
  let ρ := innerRatio R hR δ hδ0 hδlt
  {P | Z₀.time + δ < P.time ∧ P.time < Z₀.time + R ^ 2 - δ ∧
    relativeVelocity Z₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d) (ρ * R) ∧
    relativePosition Z₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d) (ρ ^ 3 * R ^ 3)}

/-- Complete membership characterization of the literal inner cylinder. -/
theorem mem_innerCylinder_iff {d : ℕ} (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    P ∈ innerCylinder Z₀ R hR δ hδ0 hδlt ↔
      Z₀.time + δ < P.time ∧ P.time < Z₀.time + R ^ 2 - δ ∧
        relativeVelocity Z₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d)
          (innerRatio R hR δ hδ0 hδlt * R) ∧
        relativePosition Z₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d)
          ((innerRatio R hR δ hδ0 hδlt) ^ 3 * R ^ 3) := Iff.rfl

/-- The inner cylinder's centre as a genuine forward kinetic cylinder. -/
def innerCentre {d : ℕ} (Z₀ : KineticPoint d) (δ : ℝ) : KineticPoint d :=
  ⟨Z₀.time + δ, Z₀.position + δ • Z₀.velocity, Z₀.velocity⟩
section
variable {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2)

/-- Literal affine retraction converted from relative to physical coordinates. -/
def innerRetraction 
    (P : KineticPoint d) : KineticPoint d :=
  let ρ := innerRatio R hR δ hδ0 hδlt
  let s := Z₀.time + δ + ρ ^ 2 * (P.time - Z₀.time)
  ⟨s, Z₀.position + (s - Z₀.time) • Z₀.velocity + ρ ^ 3 • relativePosition Z₀ P,
    Z₀.velocity + ρ • relativeVelocity Z₀ P⟩

/-- The inner exit boundary is the exit boundary of the identified inner cylinder. -/
def innerExitBoundary  : Set (KineticPoint d) :=
  let ρ := innerRatio R hR δ hδ0 hδlt
  closure (innerCylinder Z₀ R hR δ hδ0 hδlt) ∩
    ({P | P.time = Z₀.time + R ^ 2 - δ} ∪
      {P | relativeVelocity Z₀ P ∈ PDE.euclideanSphere (0 : PDE.Vec d) (ρ * R)} ∪
      {P | relativePosition Z₀ P ∈ PDE.euclideanSphere (0 : PDE.Vec d) (ρ ^ 3 * R ^ 3) ∧
        0 ≤ PDE.vecDot (relativeVelocity Z₀ P) (relativePosition Z₀ P)})
end

/-- Complete literal membership characterization of the inner exit boundary. -/
theorem mem_innerExitBoundary_iff {d : ℕ}
    (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    P ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt ↔
      let ρ := innerRatio R hR δ hδ0 hδlt
      P ∈ closure (innerCylinder Z₀ R hR δ hδ0 hδlt) ∧
        (P.time = Z₀.time + R ^ 2 - δ ∨
          relativeVelocity Z₀ P ∈ PDE.euclideanSphere (0 : PDE.Vec d) (ρ * R) ∨
          (relativePosition Z₀ P ∈ PDE.euclideanSphere (0 : PDE.Vec d)
            (ρ ^ 3 * R ^ 3) ∧
            0 ≤ PDE.vecDot (relativeVelocity Z₀ P) (relativePosition Z₀ P))) := by
  dsimp only [innerExitBoundary]
  simp only [mem_inter_iff, mem_union, mem_ofPred_eq, or_assoc]

/-- Literal conjugate reflection of the source affine inner retraction. -/
def reflectedInnerRetraction {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2)
    (P : KineticPoint d) : KineticPoint d :=
  kineticReflection (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt
    (kineticReflection P))

end HypoellipticAleksandrov.KineticAleksandrov
