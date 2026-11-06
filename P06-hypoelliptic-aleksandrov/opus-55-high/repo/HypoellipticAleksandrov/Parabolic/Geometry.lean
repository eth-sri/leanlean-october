module

public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Parabolic time--velocity geometry

This module fixes the explicit Euclidean time--velocity cylinders and their
forward parabolic boundary. The terminal open-ball face is deliberately not a
boundary component.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- Time--velocity points in dimension `d`. -/
abbrev TimeVelocity (d : ℕ) := ℝ × PDE.Vec d

/-- The analytic interior `(0, T) × B₁(y₀)` of a parabolic cylinder. -/
def parabolicInterior {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) : Set (TimeVelocity d) :=
  Set.Ioo 0 T ×ˢ PDE.euclideanBall y₀ 1

/-- The forward-reachable cylinder `(0, T] × B₁(y₀)`. -/
def parabolicReachable {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) : Set (TimeVelocity d) :=
  Set.Ioc 0 T ×ˢ PDE.euclideanBall y₀ 1

/-- The compact closure `[0, T] × \overline{B₁(y₀)}` of a parabolic cylinder. -/
def closedParabolicCylinder {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Set.Icc 0 T ×ˢ PDE.euclideanClosedBall y₀ 1

/-- The initial boundary face `{0} × \overline{B₁(y₀)}`. -/
def initialParabolicBoundary {d : ℕ} (y₀ : PDE.Vec d) : Set (TimeVelocity d) :=
  ({0} : Set ℝ) ×ˢ PDE.euclideanClosedBall y₀ 1

/-- The lateral boundary face `[0, T] × ∂B₁(y₀)`. -/
def lateralParabolicBoundary {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Set.Icc 0 T ×ˢ PDE.euclideanSphere y₀ 1

/-- The forward parabolic boundary: precisely its initial and lateral faces. -/
def forwardParabolicBoundary {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  initialParabolicBoundary y₀ ∪ lateralParabolicBoundary T y₀

variable {d : ℕ} {T t : ℝ} {y₀ v : PDE.Vec d}

/-- Membership in the analytic parabolic interior. -/
@[simp] theorem mem_parabolicInterior_iff  :
    (t, v) ∈ parabolicInterior T y₀ ↔
      0 < t ∧ t < T ∧ v ∈ PDE.euclideanBall y₀ 1 := by
  constructor
  · rintro ⟨⟨hzero, hT⟩, hv⟩
    simp_all
  · rintro ⟨hzero, hT, hv⟩
    exact ⟨⟨hzero, hT⟩, hv⟩

/-- Membership in the forward-reachable parabolic cylinder. -/
@[simp] theorem mem_parabolicReachable_iff  :
    (t, v) ∈ parabolicReachable T y₀ ↔
      0 < t ∧ t ≤ T ∧ v ∈ PDE.euclideanBall y₀ 1 := by
  constructor
  · rintro ⟨⟨hzero, hT⟩, hv⟩
    simp_all
  · rintro ⟨hzero, hT, hv⟩
    exact ⟨⟨hzero, hT⟩, hv⟩

/-- Membership in the closed parabolic cylinder. -/
@[simp] theorem mem_closedParabolicCylinder_iff  :
    (t, v) ∈ closedParabolicCylinder T y₀ ↔
      0 ≤ t ∧ t ≤ T ∧ v ∈ PDE.euclideanClosedBall y₀ 1 := by
  constructor
  · rintro ⟨⟨hzero, hT⟩, hv⟩
    simp_all
  · rintro ⟨hzero, hT, hv⟩
    exact ⟨⟨hzero, hT⟩, hv⟩

/-- Membership in the initial parabolic boundary face. -/
@[simp] theorem mem_initialParabolicBoundary_iff  {t : ℝ} {y₀ v : PDE.Vec d} :
    (t, v) ∈ initialParabolicBoundary y₀ ↔
      t = 0 ∧ v ∈ PDE.euclideanClosedBall y₀ 1 := by
  aesop

/-- Membership in the lateral parabolic boundary face. -/
@[simp] theorem mem_lateralParabolicBoundary_iff  :
    (t, v) ∈ lateralParabolicBoundary T y₀ ↔
      0 ≤ t ∧ t ≤ T ∧ v ∈ PDE.euclideanSphere y₀ 1 := by
  constructor
  · rintro ⟨⟨hzero, hT⟩, hv⟩
    simp_all
  · rintro ⟨hzero, hT, hv⟩
    exact ⟨⟨hzero, hT⟩, hv⟩

/-- Membership in the forward parabolic boundary. -/
@[simp] theorem mem_forwardParabolicBoundary_iff  :
    (t, v) ∈ forwardParabolicBoundary T y₀ ↔
      (t = 0 ∧ v ∈ PDE.euclideanClosedBall y₀ 1) ∨
        (0 ≤ t ∧ t ≤ T ∧ v ∈ PDE.euclideanSphere y₀ 1) := by
  simp [forwardParabolicBoundary]

/-- The analytic parabolic interior is measurable. -/
theorem measurableSet_parabolicInterior  (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (parabolicInterior T y₀) :=
  measurableSet_Ioo.prod (PDE.measurableSet_euclideanBall y₀ 1)

/-- The closed parabolic cylinder is compact. -/
theorem isCompact_closedParabolicCylinder  (T : ℝ) (y₀ : PDE.Vec d) :
    IsCompact (closedParabolicCylinder T y₀) :=
  isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall y₀ (by norm_num))

/-- The analytic interior is contained in the closed parabolic cylinder. -/
theorem parabolicInterior_subset_closedParabolicCylinder  (T : ℝ)
    (y₀ : PDE.Vec d) :
    parabolicInterior T y₀ ⊆ closedParabolicCylinder T y₀ := by
  intro p hp
  rcases mem_parabolicInterior_iff.mp hp with ⟨hzero, hT, hv⟩
  exact mem_closedParabolicCylinder_iff.mpr
    ⟨hzero.le, hT.le, PDE.euclideanBall_subset_euclideanClosedBall y₀ 1 hv⟩

end HypoellipticAleksandrov.Parabolic
