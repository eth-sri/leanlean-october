import GS.MatrixGeometry.Base

import GS.MatrixGeometry.SmoothLift





/-!
# A point-only shared Cayley update with a canonical generator lift

The update uses the unique minimum-physical-norm generators. It is defined
for every real step length and every ambient input vector, preserves the
original shared orbit, and has initial velocity equal to the exact projected
input. Joint smoothness is asserted on a fixed orbit, not across rank changes.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {right left : Pattern 𝕜 n}

variable (X Z P : KMat 𝕜 n)

variable (v : PairGenerator right left)

variable (t a : ℝ)

/-- The normalized Cayley transform preserves all physical block ties. -/
theorem unitCayley_shared (s : Pattern 𝕜 n) (C : Generator s) :
    SharedUnitaryFactor s.size s.label (unitCayley C.val) :=
  cayley_shared s.positive s.divides
    ((sharedSkewSpace s.size s.label).smul_mem (-1 / 2 : ℝ) C.property)

/-- Auxiliary globally smooth map before the generators are chosen. -/
def generatorCayleyValue (right left : Pattern 𝕜 n)
    (p : KMat 𝕜 n × (PairGenerator right left × ℝ)) := unitCayley (p.2.2 • p.2.1.1.val) * p.1 * unitCayley (p.2.2 • p.2.1.2.val)

@[fun_prop] theorem generatorCayleyValue_smooth (right left : Pattern 𝕜 n) :
    ContDiff ℝ ⊤ (generatorCayleyValue right left) := by
  fun_prop (disch := intro p; first
    | exact skewAdjoint.smul_mem _ p.2.1.1.property.2.1
    | exact skewAdjoint.smul_mem _ p.2.1.2.property.2.1) [generatorCayleyValue]


/-- The actual shared group element acting by this update. -/
def generatorCayleyAction   : Factors right left :=
  (Factor.ofMatrix (unitCayley (t • v.1.val)) (unitCayley_shared left (t • v.1)),
   Factor.ofMatrix ((unitCayley (t • v.2.val))ᴴ)
     (shared_factor_conjTranspose (unitCayley_shared right (t • v.2))))

theorem generatorCayleyAction_value    :
    generatorCayleyAction v t • X = generatorCayleyValue right left (X, (v, t)) := by
  change unitCayley (t • v.1.val) * X * ((unitCayley (t • v.2.val))ᴴ)ᴴ = _
  rw [Matrix.conjTranspose_conjTranspose]
  rfl

/-- The value depends on X,Z,t alone, not on a factor representative. -/
def sharedCayleyValue (right left : Pattern 𝕜 n) (X Z : KMat 𝕜 n) (t : ℝ) : KMat 𝕜 n :=
  generatorCayleyValue right left (X, (minimumNormLift right left X Z, t))

/-- Removing an ambient normal component does not change the exact update. -/
@[simp] theorem sharedCayleyValue_projected   :
    sharedCayleyValue right left X (pointProjection right left X Z) t =
      sharedCayleyValue right left X Z t := by simp_all [sharedCayleyValue,minimumNormLift_projected]



@[simp] theorem sharedCayleyValue_zero_vector   :
    sharedCayleyValue right left X 0 t = X := by simp [sharedCayleyValue, generatorCayleyValue]

theorem sharedCayleyValue_smul  (t : ℝ) :
    sharedCayleyValue right left X (a • Z) t = sharedCayleyValue right left X Z (t * a) := by
  unfold sharedCayleyValue
  rw [map_smul]
  change unitCayley (t • (a • (minimumNormLift right left X Z).1.val)) * X *
      unitCayley (t • (a • (minimumNormLift right left X Z).2.val)) =
    unitCayley ((t * a) • (minimumNormLift right left X Z).1.val) * X *
      unitCayley ((t * a) • (minimumNormLift right left X Z).2.val)
  simp only [smul_smul]

/-- Feasibility holds for all times, not only for a sufficiently small step. -/
theorem sharedCayleyValue_mem_orbit  (X : MatrixOrbit right left P)
    (Z : KMat 𝕜 n) (t : ℝ) :
    sharedCayleyValue right left X.val Z t ∈ MulAction.orbit (Factors right left) P := by
  obtain ⟨g, hg⟩ := X.property
  refine ⟨generatorCayleyAction (minimumNormLift right left X.val Z) t * g, ?_⟩
  change g • P = X.val at hg
  change (generatorCayleyAction (minimumNormLift right left X.val Z) t * g) • P = _
  rw [mul_smul, hg, generatorCayleyAction_value]
  rfl

/-- Initial matrix velocity equals the canonical full shared tangent projection. -/
theorem sharedCayleyValue_derivative  :
    HasDerivAt (sharedCayleyValue right left X Z) (pointProjection right left X Z) 0 := by
  let v := minimumNormLift right left X Z
  have hL := unitCayley_line_derivative v.1.val v.1.property.2.1
  have hR := unitCayley_line_derivative v.2.val v.2.property.2.1
  have hd := GS.MatrixBase.hasDerivAt_matrix_mul
    (GS.MatrixBase.hasDerivAt_matrix_mul hL (hasDerivAt_const (0 : ℝ) X)) hR
  have hv : v.1.val * X + X * v.2.val = pointProjection right left X Z :=
    minimumNormLift_synthesis X Z
  unfold sharedCayleyValue generatorCayleyValue
  simpa only [zero_smul, unitCayley_zero, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, add_zero, hv] using hd

/-- At a fixed matrix point, dependence on the ambient velocity and time is smooth. -/
theorem sharedCayleyValue_fixed_smooth  :
    ContDiff ℝ ⊤ (fun p : KMat 𝕜 n × ℝ => sharedCayleyValue right left X p.1 p.2) := by
  fun_prop [sharedCayleyValue]

end GS.MatrixGeometry
