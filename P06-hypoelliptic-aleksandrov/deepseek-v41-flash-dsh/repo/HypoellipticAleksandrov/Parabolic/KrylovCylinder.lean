module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.Parabolic.TypeAbbrev

/-!
# Krylov cylinders and anisotropic regularity up to their boundary

Geometry and classical regularity for the companion paper, Theorem 4.1.
-/

@[expose] public section

noncomputable section
namespace HypoellipticAleksandrov.Parabolic
section
variable {N : ℕ}

/-- The round unit cylinder ending at `t₀`, with time first. -/
def krylovCylinder  (t₀ h : ℝ) (v₀ : PDE.Vec N) : HypoellipticAleksandrov.Parabolic.TVSet N :=
  Set.Ioo (t₀ - h) t₀ ×ˢ PDE.euclideanBall v₀ 1

/-- The closed round unit cylinder ending at `t₀`. -/
def krylovClosedCylinder  (t₀ h : ℝ) (v₀ : PDE.Vec N) : HypoellipticAleksandrov.Parabolic.TVSet N :=
  Set.Icc (t₀ - h) t₀ ×ˢ PDE.euclideanClosedBall v₀ 1

/-- The bottom and lateral faces; the top open-ball face is excluded. -/
def krylovParabolicBoundary  (t₀ h : ℝ) (v₀ : PDE.Vec N) :
    HypoellipticAleksandrov.Parabolic.TVSet N :=
  ({t₀ - h} : Set ℝ) ×ˢ PDE.euclideanClosedBall v₀ 1 ∪
    Set.Icc (t₀ - h) t₀ ×ˢ PDE.euclideanSphere v₀ 1

/-- Interior anisotropic classical regularity with continuous boundary traces
of the value, time derivative, spatial gradient and spatial Hessian. -/
def IsScalarC12UpTo  (u : TimeVelocity N → ℝ)
    (Q K : HypoellipticAleksandrov.Parabolic.TVSet N) : Prop :=
  IsScalarC12On u Q ∧ ContinuousOn u K ∧
    ∃ (dt : TimeVelocity N → ℝ) (dv : TimeVelocity N → PDE.Vec N)
      (dvv : TimeVelocity N → PDE.Mat N),
      ContinuousOn dt K ∧ ContinuousOn dv K ∧ ContinuousOn dvv K ∧
      Set.EqOn dt (scalarTimeDerivative u) Q ∧
      Set.EqOn dv (scalarSpatialGradient u) Q ∧
      Set.EqOn dvv (scalarSpatialHessian u) Q

/-- The Krylov cylinder is open in the ambient time–velocity space. -/
theorem isOpen_krylovCylinder  (t₀ h : ℝ) (v₀ : PDE.Vec N) :
    IsOpen (krylovCylinder t₀ h v₀) :=
  isOpen_Ioo.prod (PDE.isOpen_euclideanBall v₀ 1)

/-- Membership uses the literal time interval and round unit ball. -/
@[simp] theorem mem_krylovCylinder_iff {N : ℕ} (t₀ h : ℝ) (v₀ : PDE.Vec N)
    (z : TimeVelocity N) :
    z ∈ krylovCylinder t₀ h v₀ ↔
      t₀ - h < z.1 ∧ z.1 < t₀ ∧ z.2 ∈ PDE.euclideanBall v₀ 1 := by
  simp only [krylovCylinder, Set.mem_prod, Set.mem_Ioo, and_assoc]

/-- Up-to-boundary regularity includes precisely the interior classical predicate. -/
theorem IsScalarC12UpTo.isScalarC12On  {u : TimeVelocity N → ℝ}
    {Q K : HypoellipticAleksandrov.Parabolic.TVSet N} (hu : IsScalarC12UpTo u Q K) :
    IsScalarC12On u Q :=
  hu.1

/-- Up-to-boundary regularity includes continuity of the value on the closed set. -/
theorem IsScalarC12UpTo.continuousOn  {u : TimeVelocity N → ℝ}
    {Q K : HypoellipticAleksandrov.Parabolic.TVSet N} (hu : IsScalarC12UpTo u Q K) :
    ContinuousOn u K :=
  hu.2.1
end

end HypoellipticAleksandrov.Parabolic
