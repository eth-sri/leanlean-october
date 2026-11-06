module

public import GS.Shared.HorizontalModel
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Ambient coordinates on a horizontal slice

The inverse function theorem supplies an ambient smooth left inverse to the
horizontal orbit parametrization near zero. Openness of the slice image in the
whole orbit is established separately by local factor decomposition.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Set Filter
open GS.OverlapGeometry (horizontalComplement horizontalRestriction
  horizontalLeftInverse_comp)
open scoped Topology
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (right left : Pattern 𝕜 n) (P : 𝕄)
local instance projectedSliceNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _

section
variable (h : HorizontalModel right left P)
def horizontalValue : 𝕄 :=
  orbitParam (1 : Factors right left) P h.val

def horizontalPoint :
    MatrixOrbit right left P :=
  orbitInverse P (1 : Factors right left) h.val

@[simp] theorem horizontalPoint_val :
    (horizontalPoint right left P h).val = horizontalValue right left P h :=
  by rfl

end

theorem horizontalValue_smooth : ContDiff ℝ ⊤ (horizontalValue right left P) :=
  (orbitParam_smooth 1 P).comp
    (horizontalComplement (orbitDerivative right left P)).subtypeL.contDiff

@[simp] theorem horizontalValue_zero :
    horizontalValue right left P 0 = P := by
  simp [horizontalValue, orbitParam_zero, one_smul]

def horizontalProjected (h : HorizontalModel right left P) : HorizontalModel right left P :=
  orbitHorizontalInverse right left P (horizontalValue right left P h - P)

theorem horizontalProjected_smooth : ContDiff ℝ ⊤ (horizontalProjected right left P) :=
  (orbitHorizontalInverse right left P).contDiff.comp
    ((horizontalValue_smooth right left P).sub contDiff_const)

@[simp] theorem horizontalProjected_zero : horizontalProjected right left P 0 = 0 := by
  simp [horizontalProjected]

theorem horizontalValue_hasFDerivAt_zero :
    HasFDerivAt (horizontalValue right left P)
      (horizontalRestriction (orbitDerivative right left P)) 0 := by
  have hh := ((orbitParam_smooth (1 : Factors right left) P).differentiable
    (by simp) 0).hasFDerivAt
  unfold horizontalValue
  simpa only [Function.comp_def, horizontalValue, horizontalRestriction, orbitDerivative, map_zero] using
    HasFDerivAt.comp (f := fun h : HorizontalModel right left P => h.val)
      (g := orbitParam (1 : Factors right left) P) 0 hh
      (horizontalComplement (orbitDerivative right left P)).subtypeL.hasFDerivAt

theorem horizontalProjected_hasFDerivAt_zero :
    HasFDerivAt (horizontalProjected right left P)
      (ContinuousLinearMap.id ℝ (HorizontalModel right left P)) 0 := by
  have hh := (orbitHorizontalInverse right left P).hasFDerivAt.comp 0
    ((horizontalValue_hasFDerivAt_zero right left P).sub_const P)
  unfold horizontalProjected
  simpa only [Function.comp_def, horizontalProjected, orbitHorizontalInverse, horizontalLeftInverse_comp] using hh

/-- Concrete IFT data, without any assertion that its image is open in the orbit. -/
structure ProjectedSliceData where
  domain : Set (HorizontalModel right left P)
  coordinates : 𝕄 → HorizontalModel right left P
  open_domain : IsOpen domain
  zero_mem : 0 ∈ domain
  left_inverse : ∀ h ∈ domain, coordinates (horizontalValue right left P h) = h
  coordinates_smooth : ∀ h ∈ domain,
    ContDiffAt ℝ ⊤ coordinates (horizontalValue right left P h)

def projectedSliceData : ProjectedSliceData right left P :=
  Classical.choice <| by
    have hd := (horizontalProjected_smooth right left P).contDiffAt (x := 0)
    have hf := horizontalProjected_hasFDerivAt_zero right left P
    let e := hd.toOpenPartialHomeomorph _ (f' := .refl ℝ _) hf (by simp)
    have h0 : (0 : HorizontalModel right left P) ∈ e.source := hd.mem_toOpenPartialHomeomorph_source (f' := .refl ℝ _) hf (by simp)
    have hs : ContDiffAt ℝ ⊤ e.symm 0 := by
      have := hd.to_localInverse (f' := .refl ℝ _) hf (by simp)
      aesop
    obtain ⟨W, hWsub, hWopen, hWzero⟩ := mem_nhds_iff.mp (inter_mem (e.open_target.mem_nhds
      ((show e 0 = 0 from horizontalProjected_zero right left P) ▸ e.map_source h0)) (hs.eventually (by simp)))
    refine ⟨⟨_, fun A => e.symm (orbitHorizontalInverse right left P (A - P)), e.open_source.inter
      (hWopen.preimage (horizontalProjected_smooth right left P).continuous),
      ⟨h0, by simp_all⟩, fun h hh => e.left_inv hh.1, fun h hh => ?_⟩⟩
    have hi : ContDiffAt ℝ ⊤ e.symm (horizontalProjected right left P h) := by aesop
    fun_prop

end GS.Shared
