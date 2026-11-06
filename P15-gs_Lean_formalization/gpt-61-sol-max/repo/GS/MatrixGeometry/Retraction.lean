import GS.MatrixGeometry.Base

import GS.MatrixGeometry.CayleyStep
import GS.MatrixGeometry.Gradient
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv


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
open GS.MatrixBase
open scoped Manifold
attribute [local fun_prop] GS.MatrixGeometry.sharedCayleyValue_fixed_smooth
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  (right left : Pattern 𝕜 n) (P : KMat 𝕜 n)
local instance retractionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance retractionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P


attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

variable (X : MatrixOrbit right left P)

theorem sharedCayleyValue_hasFDerivAt_zero (X : KMat 𝕜 n) :
    HasFDerivAt (fun Z => sharedCayleyValue right left X Z 1)
      (pointProjection right left X) 0 := by
  let f := fun Z => sharedCayleyValue right left X Z 1
  have hs : DifferentiableAt ℝ f 0 :=
    ((sharedCayleyValue_fixed_smooth X).comp
      (contDiff_id.prodMk contDiff_const)).differentiable (by simp) 0
  have he : fderiv ℝ f 0 = pointProjection right left X := by
    apply ContinuousLinearMap.ext
    intro Z
    have hd := hs.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).smul_const Z) (by simp)
    simp only [f, Function.comp_def, id_eq, one_smul,
      sharedCayleyValue_smul, one_mul] at hd
    exact hd.unique (sharedCayleyValue_derivative X Z)
  rw [← he]
  exact hs.hasFDerivAt


/-- The globally feasible time-one Cayley map on the actual tangent fibre. -/
def cayleyFibreRetraction 
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    MatrixOrbit right left P :=
  ⟨sharedCayleyValue right left X.val (inclusionDifferential right left P X v) 1,
    sharedCayleyValue_mem_orbit P X (inclusionDifferential right left P X v) 1⟩

@[simp] theorem cayleyFibreRetraction_zero  :
    cayleyFibreRetraction right left P X 0 = X := by
  apply Subtype.ext
  simp [cayleyFibreRetraction]

theorem cayleyFibreRetraction_contMDiff  :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P)) ⊤
      (fun v : HorizontalModel right left P => cayleyFibreRetraction right left P X v) := by
  apply (sharedOrbit_contMDiff_iff_ambient right left P (𝓘(ℝ, HorizontalModel right left P)) _).mpr
  apply contMDiff_iff_contDiff.mpr
  let D : HorizontalModel right left P →L[ℝ] KMat 𝕜 n := inclusionDifferential right left P X
  change ContDiff ℝ ⊤ (fun v => sharedCayleyValue right left X.val (D v) 1)
  fun_prop

/-- The derivative of the time-one retraction at the zero vector is the identity. -/
theorem cayleyFibreRetraction_mfderiv_zero
     :
    mfderiv (M := HorizontalModel right left P) (M' := MatrixOrbit right left P)
      (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
      (fun v : HorizontalModel right left P => cayleyFibreRetraction right left P X v) (0 : HorizontalModel right left P) =
        ContinuousLinearMap.id ℝ (HorizontalModel right left P) := by
  ext v
  apply inclusionDifferential_injective right left P X
  have hf := (cayleyFibreRetraction_contMDiff right left P X).mdifferentiable (by simp)
  have hi := (sharedOrbit_val_contMDiff right left P).mdifferentiable (by simp)
  have hchain := mfderiv_comp_apply_of_eq (0 : HorizontalModel right left P)
    (hi X) (hf 0) (cayleyFibreRetraction_zero right left P X) v
  let D : HorizontalModel right left P →L[ℝ] KMat 𝕜 n := inclusionDifferential right left P X
  have hd := sharedCayleyValue_hasFDerivAt_zero right left X.val
  rw [← map_zero D] at hd
  have hd := hd.comp 0 D.hasFDerivAt
  have hmatrix : mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, KMat 𝕜 n))
      (fun w : HorizontalModel right left P => (cayleyFibreRetraction right left P X w).val)
      0 v = D v := by
    rw [mfderiv_eq_fderiv]
    exact (congrArg (fun L : HorizontalModel right left P →L[ℝ] KMat 𝕜 n => L v)
      hd.fderiv).trans ((pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v,rfl⟩)
  exact hchain.symm.trans hmatrix


end GS.MatrixGeometry
