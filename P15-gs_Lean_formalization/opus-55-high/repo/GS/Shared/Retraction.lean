module

public import GS.Shared.CayleyStep
public import GS.Shared.Gradient
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A canonical Cayley retraction on each actual shared tangent fibre

The map uses only the base matrix and the matrix image of the actual tangent
vector. It is feasible for all real times. The initial matrix derivative is
identified with the manifold derivative using injectivity of the inclusion,
and the fibre differential of the time-one map is the identity.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open scoped Topology Manifold
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (right left : Pattern 𝕜 n) (P : 𝕄)
local instance retractionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance retractionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P

attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

section
variable (X : MatrixOrbit right left P) (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X)
/-- Orbit membership is proof data; the value does not inspect a factorization. -/
def cayleyTangentStep (t : ℝ) :
    MatrixOrbit right left P :=
  ⟨sharedCayleyValue right left X.val (inclusionDifferential right left P X v) t,
    sharedCayleyValue_mem_orbit P X (inclusionDifferential right left P X v) t⟩

@[simp] theorem cayleyTangentStep_val (t : ℝ) :
    (cayleyTangentStep right left P X v t).val =
      sharedCayleyValue right left X.val (inclusionDifferential right left P X v) t := rfl

@[simp] theorem cayleyTangentStep_at_zero :
    cayleyTangentStep right left P X v 0 = X := by
  apply Subtype.ext
  simp

end

section
variable (X : MatrixOrbit right left P)
@[simp] theorem cayleyTangentStep_zero_vector (t : ℝ) :
    cayleyTangentStep right left P X 0 t = X := by
  apply Subtype.ext
  simp

/-- The genuine matrix derivative, for every actual tangent vector. -/
theorem cayleyTangentStep_derivative (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    HasDerivAt (fun t => (cayleyTangentStep right left P X v t).val)
      (inclusionDifferential right left P X v) 0 := by
  have hd := sharedCayleyValue_derivative (right := right) (left := left)
    X.val (inclusionDifferential right left P X v)
  have hfix : pointProjection right left X.val (inclusionDifferential right left P X v) =
      inclusionDifferential right left P X v :=
    (pointProjection_fixed_iff_tangent_image right left P X _).mpr (by aesop)
  simp_all

/-- Fixed-base smoothness jointly in the true tangent coordinate and time. -/
theorem cayleyTangentStep_joint_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P × ℝ))
      (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (fun p : HorizontalModel right left P × ℝ => cayleyTangentStep right left P X p.1 p.2) := by
  apply (sharedOrbit_contMDiff_iff_contDiff right left P
    (fun p : HorizontalModel right left P × ℝ =>
      cayleyTangentStep right left P X p.1 p.2)).mpr
  let D : HorizontalModel right left P →L[ℝ] 𝕄 :=
    inclusionDifferential right left P X
  exact (sharedCayleyValue_fixed_smooth (right := right) (left := left) X.val).comp
    (f := fun p : HorizontalModel right left P × ℝ => (D p.1, p.2))
    (by fun_prop)

/-- Scaling the tangent vector is equivalent to scaling time. -/
theorem cayleyTangentStep_smul
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) (a t : ℝ) :
    cayleyTangentStep right left P X (a • v) t = cayleyTangentStep right left P X v (t * a) := by
  apply Subtype.ext
  simp
  exact sharedCayleyValue_smul X.val (inclusionDifferential right left P X v) a t

/-- The time-one Cayley retraction on the actual tangent fibre. -/
def cayleyFibreRetraction (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    MatrixOrbit right left P :=
  cayleyTangentStep right left P X v 1


@[simp] theorem cayleyFibreRetraction_zero :
    cayleyFibreRetraction right left P X 0 = X :=
  cayleyTangentStep_zero_vector right left P X 1

theorem cayleyFibreRetraction_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (fun v : HorizontalModel right left P => cayleyFibreRetraction right left P X v) := by
  have hi : ContMDiff (𝓘(ℝ, HorizontalModel right left P))
      (𝓘(ℝ, HorizontalModel right left P × ℝ)) ⊤ (fun v : HorizontalModel right left P => (v, (1 : ℝ))) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact ContMDiff.comp
    (g := fun p : HorizontalModel right left P × ℝ => cayleyTangentStep right left P X p.1 p.2)
    (f := fun v : HorizontalModel right left P => (v, (1 : ℝ)))
    (cayleyTangentStep_joint_contMDiff right left P X) hi

/-- Smoothness of the feasible curve in the actual orbit atlas. -/
theorem cayleyTangentStep_contMDiff
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (cayleyTangentStep right left P X v) := by
  have hi : ContMDiff (𝓘(ℝ, ℝ))
      (𝓘(ℝ, HorizontalModel right left P × ℝ)) ⊤ (fun t : ℝ => (Prod.mk (α := HorizontalModel right left P) (β := ℝ) v t)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  exact ContMDiff.comp
    (g := fun p : HorizontalModel right left P × ℝ => cayleyTangentStep right left P X p.1 p.2)
    (f := fun t : ℝ => (Prod.mk (α := HorizontalModel right left P) (β := ℝ) v t))
    (cayleyTangentStep_joint_contMDiff right left P X) hi

/-- The derivative is in mathlib's original tangent space, not only its matrix image. -/
theorem cayleyTangentStep_mfderiv_one
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P))
      (cayleyTangentStep right left P X v) 0 (1 : ℝ) = v := by
  apply inclusionDifferential_injective right left P X
  have hc := (cayleyTangentStep_contMDiff right left P X v).mdifferentiable (by simp)
  have hi := (sharedOrbit_val_contMDiff right left P).mdifferentiable (by simp)
  have hchain := mfderiv_comp_apply_of_eq (0 : ℝ) (hi X) (hc 0)
    (by simp) (1 : ℝ)
  have hmatrix : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, 𝕄))
      (fun t => (cayleyTangentStep right left P X v t).val) 0 (1 : ℝ) =
        inclusionDifferential right left P X v := by
    rw [mfderiv_eq_fderiv]
    exact (cayleyTangentStep_derivative right left P X v).deriv
  exact hchain.symm.trans hmatrix

/-- Directional form of the retraction derivative at the zero vector. -/
theorem cayleyFibreRetraction_mfderiv_zero_apply
    (v : HorizontalModel right left P) :
    @Eq (HorizontalModel right left P)
      (mfderiv (M := HorizontalModel right left P) (M' := MatrixOrbit right left P)
        (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
        (fun w : HorizontalModel right left P => cayleyFibreRetraction right left P X w)
        (0 : HorizontalModel right left P) v) v := by
  have hd : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hf := (cayleyFibreRetraction_contMDiff right left P X).mdifferentiable (by simp)
  have hline : (fun t : ℝ => cayleyFibreRetraction right left P X (t • v)) =
      cayleyTangentStep right left P X v := by
    funext t
    exact (cayleyTangentStep_smul right left P X v t 1).trans (by simp)
  have hlineD : @Eq (HorizontalModel right left P)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P))
        (fun t : ℝ => t • v) 0 (1 : ℝ)) v := by
    rw [mfderiv_eq_fderiv]
    exact hd.deriv
  let R : HorizontalModel right left P → MatrixOrbit right left P :=
    fun w => cayleyFibreRetraction right left P X w
  let DR : HorizontalModel right left P →L[ℝ] HorizontalModel right left P :=
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P)) R (0 : HorizontalModel right left P)
  let velocity : (ℝ → MatrixOrbit right left P) → HorizontalModel right left P :=
    fun c => mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P)) c 0 (1 : ℝ)
  have hchain : @Eq (HorizontalModel right left P)
      (velocity (fun t : ℝ => R (t • v)))
      (DR (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, HorizontalModel right left P))
        (fun t : ℝ => t • v) 0 (1 : ℝ))) :=
    mfderiv_comp_apply_of_eq (0 : ℝ) (hf 0)
      hd.differentiableAt.mdifferentiableAt (by simp) (1 : ℝ)
  have hvelocity : @Eq (HorizontalModel right left P)
      (velocity (cayleyTangentStep right left P X v)) v :=
    cayleyTangentStep_mfderiv_one right left P X v
  aesop


/-- The derivative of the time-one retraction at the zero vector is the identity. -/
theorem cayleyFibreRetraction_mfderiv_zero
    :
    mfderiv (M := HorizontalModel right left P) (M' := MatrixOrbit right left P)
      (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
      (fun v : HorizontalModel right left P => cayleyFibreRetraction right left P X v) (0 : HorizontalModel right left P) =
        ContinuousLinearMap.id ℝ (HorizontalModel right left P) := by
  ext v
  exact cayleyFibreRetraction_mfderiv_zero_apply right left P X v

end

end GS.Shared
