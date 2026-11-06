module

public import GS.Shared.ProjectedSlice

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The full differential image after removing the shared stabilizer

The complement has the same differential image as the complete factor model
at every translated centre.  It therefore represents every matrix direction,
including when shared blocks and cross-layer overlap occur simultaneously.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Pattern 𝕜 n}
local instance horizontalDifferentialNormedSpace (P : 𝕄) :
    NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _

theorem orbitParam_fderiv_zero_of_kernel (g : Factors right left) (P : 𝕄)
    (v : PairGenerator right left)
    (hv : fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0) :
    fderiv ℝ (orbitParam g P) 0 v = 0 := by
  have hi := (orbitParam_kernel_iff_intertwine P v).mp hv
  rw [orbitParam_fderiv_zero]
  simp only [tangentParam, Matrix.smul_mul, Matrix.mul_smul]
  have he : (Factor.matrix g.1) * v.1.val * P * (Factor.matrix g.2)ᴴ =
      (Factor.matrix g.1) * P * v.2.val * (Factor.matrix g.2)ᴴ := by
    grind
  simp_all

section
variable (P : 𝕄) (g : Factors right left)
theorem horizontalOrbit_hasFDerivAt_zero :
    HasFDerivAt (fun h : HorizontalModel right left P => orbitParam g P h.val)
      ((fderiv ℝ (orbitParam g P) 0).comp
        (HorizontalModel right left P).subtypeL) 0 := by
  have hh := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  simpa only [map_zero, Function.comp_def] using
    HasFDerivAt.comp (f := fun h : HorizontalModel right left P => h.val)
      (g := orbitParam g P) 0 hh
      (HorizontalModel right left P).subtypeL.hasFDerivAt

theorem horizontalOrbit_fderiv_zero (h : HorizontalModel right left P) :
    fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h =
      fderiv ℝ (orbitParam g P) 0 h.val := by
  rw [(horizontalOrbit_hasFDerivAt_zero P g).fderiv]
  rfl

theorem horizontalOrbit_fderiv_zero_range (Z : 𝕄) :
    (∃ h : HorizontalModel right left P,
      fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h = Z) ↔
      Z ∈ pointDirections right left (g • P) := by
  rw [← orbitParam_fderiv_zero_range g P Z]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h.val, (horizontalOrbit_fderiv_zero P g h).symm.trans hh⟩
  · rintro ⟨v, hv⟩
    let z := (horizontalKernelEquiv right left P).symm v
    have hz : (z.1.val : PairGenerator right left) + z.2.val = v :=
      (horizontalKernelEquiv right left P).apply_symm_apply v
    have hk : fderiv ℝ (orbitParam g P) 0 z.2.val = 0 :=
      orbitParam_fderiv_zero_of_kernel g P z.2.val z.2.property
    refine ⟨z.1, ?_⟩
    rw [horizontalOrbit_fderiv_zero, ← hv, ← hz, map_add, hk, add_zero]

end

end GS.Shared
