module

public import GS.Shared.SmoothLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A point-only shared Cayley update with a canonical generator lift

The update uses the unique minimum-physical-norm generators. It is defined
for every real step length and every ambient input vector, preserves the
original shared orbit, and has initial velocity equal to the exact projected
input. Joint smoothness is asserted on a fixed orbit, not across rank changes.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
open scoped Topology Manifold
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Pattern 𝕜 n}

/-- The normalized Cayley transform preserves all physical block ties. -/
theorem unitCayley_shared (s : Pattern 𝕜 n) (C : Generator s) :
    SharedFactor s.size s.label (unitCayley C.val) :=
  cayley_shared s.positive s.divides
    (by aesop)

section
variable (right left : Pattern 𝕜 n)
/-- Auxiliary globally smooth map before the generators are chosen. -/
def generatorCayleyValue (p : 𝕄 × (PairGenerator right left × ℝ)) : 𝕄 :=
  unitCayley (p.2.2 • p.2.1.1.val) * p.1 * unitCayley (p.2.2 • p.2.1.2.val)

theorem generatorCayleyValue_smooth :
    ContDiff ℝ ⊤ (generatorCayleyValue right left) := by
  let E := 𝕄 × (PairGenerator right left × ℝ)
  have hL : ContDiff ℝ ⊤ (fun p : E => p.2.2 • p.2.1.1.val) :=
    contDiff_snd.snd.smul
      ((contDiff_val _).comp contDiff_snd.fst.fst)
  have hR : ContDiff ℝ ⊤ (fun p : E => p.2.2 • p.2.1.2.val) :=
    contDiff_snd.snd.smul
      ((contDiff_val _).comp contDiff_snd.fst.snd)
  have hcL := unitCayley_smooth_comp _ hL (fun p => skew_smul p.2.2 p.2.1.1.property.2.1)
  have hcR := unitCayley_smooth_comp _ hR (fun p => skew_smul p.2.2 p.2.1.2.property.2.1)
  exact smooth_matrix_product (smooth_matrix_product hcL contDiff_fst) hcR

end

/-- The actual shared group element acting by this update. -/
def generatorCayleyAction (v : PairGenerator right left) (t : ℝ) : Factors right left :=
  (Factor.ofMatrix (unitCayley (t • v.1.val)) (unitCayley_shared left (t • v.1)),
   Factor.ofMatrix ((unitCayley (t • v.2.val))ᴴ)
     (shared_factor_conjTranspose (unitCayley_shared right (t • v.2))))

theorem generatorCayleyAction_value (X : 𝕄) (v : PairGenerator right left) (t : ℝ) :
    generatorCayleyAction v t • X = generatorCayleyValue right left (X, (v, t)) := by
  change unitCayley (t • v.1.val) * X * ((unitCayley (t • v.2.val))ᴴ)ᴴ = _
  aesop

/-- The value depends on X,Z,t alone, not on a factor representative. -/
def sharedCayleyValue (right left : Pattern 𝕜 n) (X Z : 𝕄) (t : ℝ) : 𝕄 :=
  generatorCayleyValue right left (X, (minimumNormLift right left X Z, t))

section
variable (X Z : 𝕄)
/-- Removing an ambient normal component does not change the exact update. -/
@[simp] theorem sharedCayleyValue_projected (t : ℝ) :
    sharedCayleyValue right left X (pointProjection right left X Z) t =
      sharedCayleyValue right left X Z t := by
  simp only [sharedCayleyValue, minimumNormLift_projected]

@[simp] theorem sharedCayleyValue_zero_time :
    sharedCayleyValue right left X Z 0 = X := by simp [sharedCayleyValue, generatorCayleyValue]

end

@[simp] theorem sharedCayleyValue_zero_vector (X : 𝕄) (t : ℝ) :
    sharedCayleyValue right left X 0 t = X := by simp [sharedCayleyValue, generatorCayleyValue]

theorem sharedCayleyValue_smul (X Z : 𝕄) (a t : ℝ) :
    sharedCayleyValue right left X (a • Z) t = sharedCayleyValue right left X Z (t * a) := by
  unfold sharedCayleyValue
  simp
  change unitCayley (t • (a • (minimumNormLift right left X Z).1.val)) * X *
      unitCayley (t • (a • (minimumNormLift right left X Z).2.val)) =
    unitCayley ((t * a) • (minimumNormLift right left X Z).1.val) * X *
      unitCayley ((t * a) • (minimumNormLift right left X Z).2.val)
  simp only [smul_smul]

/-- Feasibility holds for all times, not only for a sufficiently small step. -/
theorem sharedCayleyValue_mem_orbit (P : 𝕄) (X : MatrixOrbit right left P)
    (Z : 𝕄) (t : ℝ) :
    sharedCayleyValue right left X.val Z t ∈ MulAction.orbit (Factors right left) P := by
  obtain ⟨g, hg⟩ := X.property
  refine ⟨generatorCayleyAction (minimumNormLift right left X.val Z) t * g, ?_⟩
  change g • P = X.val at hg
  field_simp
  rw [mul_smul, hg, generatorCayleyAction_value]
  rfl

/-- Initial matrix velocity equals the canonical full shared tangent projection. -/
theorem sharedCayleyValue_derivative (X Z : 𝕄) :
    HasDerivAt (sharedCayleyValue right left X Z) (pointProjection right left X Z) 0 := by
  let v := minimumNormLift right left X Z
  have hL := unitCayley_line_derivative v.1.val v.1.property.2.1
  have hR := unitCayley_line_derivative v.2.val v.2.property.2.1
  have hd := hasDerivAt_matrix_mul
    (hasDerivAt_matrix_mul hL (hasDerivAt_const (0 : ℝ) X)) hR
  have hv : v.1.val * X + X * v.2.val = pointProjection right left X Z :=
    minimumNormLift_synthesis X Z
  aesop

/-- At a fixed matrix point, dependence on the ambient velocity and time is smooth. -/
theorem sharedCayleyValue_fixed_smooth (X : 𝕄) :
    ContDiff ℝ ⊤ (fun p : 𝕄 × ℝ => sharedCayleyValue right left X p.1 p.2) :=
  (generatorCayleyValue_smooth right left).comp
    (contDiff_const.prodMk (((minimumNormLift right left X).contDiff.comp contDiff_fst).prodMk contDiff_snd))

section OrbitSmoothness
variable (right left : Pattern 𝕜 n) (P : 𝕄)
local instance cayleyStepChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P

/-- Joint smoothness including the base point, on the whole fixed orbit. -/
theorem sharedCayleyValue_contMDiff :
    ContMDiff (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, 𝕄)) ⊤ (fun p : (MatrixOrbit right left P × 𝕄) × ℝ =>
        sharedCayleyValue right left p.1.1.val p.1.2 p.2) := by
  have hb : ContMDiff
      (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, 𝕄)) ⊤
      (fun p : (MatrixOrbit right left P × 𝕄) × ℝ => p.1.1.val) :=
    (sharedOrbit_val_contMDiff right left P).comp (contMDiff_fst.comp contMDiff_fst)
  have hl : ContMDiff
      (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, PairGenerator right left)) ⊤
      (fun p : (MatrixOrbit right left P × 𝕄) × ℝ =>
        minimumNormLift right left p.1.1.val p.1.2) :=
    (minimumNormLift_contMDiff right left P).comp contMDiff_fst
  exact (generatorCayleyValue_smooth right left).comp_contMDiff
    (hb.prodMk_space (hl.prodMk_space contMDiff_snd))

end OrbitSmoothness
end GS.Shared
