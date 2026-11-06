module

public import GS.UnitaryManifold.BlockGroup
public import GS.Shared.Base
public import GS.Unitary.Support
public import GS.Frobenius
public import Mathlib.Data.Complex.BigOperators
public import GS.Unitary.GeometryAlgebra
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

@[expose] public section

/-! Cayley charts on the full unitary group, via the field-generic Cayley calculus. -/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry GS.Shared
namespace GS.UnitaryManifold
variable {n : ℕ}

abbrev Model (block : Fin n → ℕ) := ↥(supportedSkewSpace block)

variable (Q : BlockU (fun _ : Fin n => 0))

def chartSource : Set (BlockU (fun _ : Fin n => 0)) := {U | admissible (Q.valᴴ * U.val)}

def chartMap (X : CMat n) : Model (fun _ : Fin n => 0) :=
  (proj _).codRestrict _ (proj_mem _) (cayley (Q.valᴴ * X))

def chartInv (x : Model (fun _ : Fin n => 0)) : CMat n := Q.val * cayley x.val

theorem base_mem_chartSource : Q ∈ chartSource Q := by simp [chartSource, Q.2.2.1]

theorem chartInv_chartMap (U) (hU : U ∈ chartSource Q) : chartInv Q (chartMap Q U.val) = U.val := by
  simp only [chartInv, chartMap, ContinuousLinearMap.coe_codRestrict_apply]
  rw [proj_of_mem _ _ (show _ ∈ supportedSkewSpace _ from ⟨by tauto, cayley_isSkew (Q.2.2.conjTranspose.mul U.2.2) hU⟩),
    cayley_involutive hU, ← Matrix.mul_assoc, Q.2.2.2, Matrix.one_mul]

@[simp] theorem chartInv_zero : chartInv Q 0 = Q.val := by simp [chartInv]

@[simp] theorem chartMap_base : chartMap Q Q.val = 0 := by simp [chartMap, Q.2.2.1, cayley]

theorem chartInv_smooth : ContDiff ℝ ⊤ (chartInv Q) :=
  contDiff_iff_contDiffAt.2 fun x => smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at (contDiff_val _).contDiffAt (admissible_of_isSkew x.2.2))

theorem chartInv_fderiv_zero (v) : fderiv ℝ (chartInv Q) 0 v = (-2 : ℝ) • (Q.val * v.val) := by
  refine ((((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt).comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const v).congr_deriv (by simp)) (by simp)).unique ?_
  have h := hasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) Q.val) (cayley_line_derivative v.val v.2.2)
  aesop

/-- A genuine Cayley partial homeomorphism in the inherited matrix topology. -/
def blockPartialChart :
    OpenPartialHomeomorph (BlockU (fun _ : Fin n => 0)) (Model (fun _ : Fin n => 0)) where
  toFun U := chartMap Q U.val
  invFun x := ⟨chartInv Q x, by tauto,
    Q.2.2.mul (cayley_unitary x.2.2 (admissible_of_isSkew x.2.2))⟩
  source := chartSource Q
  target := Set.univ
  map_source' _ _ := trivial
  map_target' x _ := by
    simpa [chartSource, chartInv, ← Matrix.mul_assoc, Q.2.2.1] using
      admissible_cayley (admissible_of_isSkew x.2.2)
  left_inv' U hU := Subtype.ext (chartInv_chartMap Q U hU)
  right_inv' x _ := by
    apply Subtype.ext
    simp only [chartMap, chartInv, ContinuousLinearMap.coe_codRestrict_apply, ← Matrix.mul_assoc,
      Q.2.2.1, Matrix.one_mul, cayley_involutive (admissible_of_isSkew x.2.2)]
    simp
  open_source := admissible_open.preimage (by fun_prop)
  open_target := isOpen_univ
  continuousOn_toFun U hU := ((((proj _).codRestrict _ (proj_mem _)).continuous.continuousAt.comp
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hU).continuousAt).comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := ((chartInv_smooth Q).continuous.subtype_mk _).continuousOn

end GS.UnitaryManifold
