module
public import GS.Spectral.Base
public import GS.Isometric.Parameter
public import GS.Spectral.Patch
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
@[expose] public section

/-! Straighten the anchor conditions in the full Cayley chart. The imaginary
component lives in `skewAdjoint 𝕜`, so the same proof includes the real case
(where there are no infinitesimal phase constraints). -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open Matrix GS.Isometric Set
open scoped ComplexOrder Topology
namespace GS.Spectral
variable {𝕜 : Type*} [RCLike 𝕜] {q : ℕ}
abbrev G (𝕜 : Type*) [RCLike 𝕜] (q : ℕ) := Generator (⊤ : Layer 𝕜 q)
def asFactor : U 𝕜 q ≃ₜ Factor (⊤ : Layer 𝕜 q) where
  toFun a := ⟨a,trivial⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val
variable (Q : U 𝕜 q) (o : Fin q)
def groupChart : OpenPartialHomeomorph (U 𝕜 q) (G 𝕜 q) :=
  ((frameChart ⊤).transHomeomorph (asFactor.symm.trans (Homeomorph.mulLeft Q))).symm
@[simp] lemma groupChart_zero : (groupChart Q).symm 0 = Q := by change Q * (frame (0 : G 𝕜 q)).val = Q; simp
lemma groupChart_source : Q ∈ (groupChart Q).source := by simpa only [groupChart_zero] using (groupChart Q).map_target (show (0 : G 𝕜 q) ∈ univ from trivial)
@[simp] lemma groupChart_base : groupChart Q Q = 0 := by simpa using (groupChart Q).right_inv (show 0 ∈ univ from trivial)

abbrev Im (𝕜 : Type*) [RCLike 𝕜] := ↥(skewAdjoint.submodule ℝ 𝕜)
abbrev Anchors (𝕜 : Type*) [RCLike 𝕜] {q} (o : Fin q) := (Fin q → Im 𝕜) × ({j : Fin q // j ≠ o} → Im 𝕜)
local notation "imP" => (skewAdjointPart ℝ : 𝕜 →ₗ[ℝ] Im 𝕜)
private lemma im_fixed (a : Im 𝕜) : imP a.val = a := LinearMap.congr_fun (skewAdjointPart_comp_subtype_skewAdjoint ℝ (A := 𝕜)) a
lemma im_zero (a : 𝕜) : imP a = 0 ↔ RCLike.im a = 0 := by
  rw [← RCLike.conj_eq_iff_im,Subtype.ext_iff]; change (⅟(2:ℝ)) • (a-star a) = 0 ↔ _
  rw [smul_eq_zero, or_iff_right (by norm_num), sub_eq_zero, RCLike.star_def, eq_comm]

def constraint : Square 𝕜 q →L[ℝ] Anchors 𝕜 o := LinearMap.toContinuousLinearMap
  { toFun A := (fun i => imP (A i o / Q.val i o),fun j => imP (A o j.val / Q.val o j.val))
    map_add' A B := by ext <;> simp [add_div]
    map_smul' c A := by apply Prod.ext <;> funext i <;> simp [smul_div_assoc] }

def levels (v : G 𝕜 q) := constraint Q o ((groupChart Q).symm v).val
lemma levels_smooth : ContDiff ℝ ⊤ (levels Q o) := (constraint Q o).contDiff.comp
  (f := fun v : G 𝕜 q => Q.val * (frame v).matrix) (smooth_matrix_product contDiff_const frame_smooth)
def derivLevel := fderiv ℝ (levels Q o) 0
lemma level_strict : HasStrictFDerivAt (levels Q o) (derivLevel Q o) 0 := (levels_smooth Q o).hasStrictFDerivAt (by simp)

variable (hne : ∀ i j, Q.val i j ≠ 0)
private lemma phase_skew (a : Fin q → Im 𝕜) : Skew (diagonal (fun i => (a i).val)) := by
  rw [Skew,diagonal_conjTranspose,diagonal_neg]; congr 1; ext <;> simp_all

include hne in
lemma level_onto : (derivLevel Q o).range = ⊤ := by
  apply LinearMap.range_eq_top.mpr; rintro ⟨a,b⟩
  let c (j : Fin q) : Im 𝕜 := if hj : j=o then 0 else b ⟨j,hj⟩ - a o
  let L := diagonal (fun i => (a i).val); let R := diagonal (fun j => (c j).val)
  let v : G 𝕜 q := ⟨Q.valᴴ*L*Q.val + R,trivial,by
    simp [Skew,Matrix.mul_assoc,show Lᴴ = -L from phase_skew a,show Rᴴ = -R from phase_skew c,add_comm]⟩
  have hv : derivLevel Q o v = constraint Q o (L*Q.val+Q.val*R) := by
    apply deriv_on_line ((levels_smooth Q o).differentiable (by simp) 0)
    have h := hasDerivAt_matrix_mul (hasDerivAt_const (0:ℝ) Q.val) (unitCayley_line_derivative v.val)
    simpa [v,mul_add,Matrix.mul_assoc] using! (constraint Q o).hasFDerivAt.comp_hasDerivAt 0 h
  have entry i j : imP ((L*Q.val+Q.val*R) i j / Q.val i j) = a i + c j := by
    rw [show (L*Q.val+Q.val*R) i j / Q.val i j = (a i + c j).val by
      simp [L,R,diagonal_mul,mul_diagonal,← add_mul,mul_comm (Q.val i j),hne]]
    exact im_fixed _
  refine ⟨v,hv.trans ?_⟩
  apply Prod.ext <;> funext i
  · exact (entry i o).trans (by simp [c])
  · exact (entry o i.val).trans (by simp [c,i.property])
end GS.Spectral
