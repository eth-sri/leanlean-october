/-
Actual regular cubic level set via the inverse
function theorem. No supplied chart, prescribed jets or curvature conclusion.
This module supplies the regular level chart, not arbitrary-polynomial representation
or the full geometric recognition theorem.
-/
module
public import Mathlib.Tactic.Simps.Basic
public import AlbertGeometry.LinearSimp

public import AlbertGeometry.CubicDerivatives
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Tactic.Module

@[expose] public section
open scoped ContDiff Topology

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)

/-- Tangents are the actual differential's kernel. -/
def tangentSpace   : Submodule ℝ E :=
  (fderiv ℝ (diagonalCubic P.form) e).ker

/-- The explicit ambient continuous projection, before codomain restriction. -/
def tangentProjectionRaw   : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (1 / 3 : ℝ) •
    (ContinuousLinearMap.toSpanSingleton ℝ e).comp
      (fderiv ℝ (diagonalCubic P.form) e)

@[simp] theorem tangentProjectionRaw_apply 
    (e x : E) : tangentProjectionRaw P e x =
      x - (fderiv ℝ (diagonalCubic P.form) e x / 3) • e := by
  simp only [clm_eval, tangentProjectionRaw, ContinuousLinearMap.toSpanSingleton_apply, smul_smul, div_eq_mul_inv]
  congr 2
  ring

variable  
    (he : diagonalCubic P.form e = 1)

include P e he in
theorem tangentProjectionRaw_mem  (x : E) :
    tangentProjectionRaw P e x ∈ tangentSpace P e := by
  change fderiv ℝ (diagonalCubic P.form) e (tangentProjectionRaw P e x) = 0
  rw [tangentProjectionRaw_apply, map_sub, map_smul,
    fderiv_diagonalCubic_at_one P.form e he]
  simp only [smul_eq_mul]
  ring

/-- Restriction to the actual differential kernel is proved, not assumed. -/
def tangentProjection  
    (he : diagonalCubic P.form e = 1) : E →L[ℝ] tangentSpace P e :=
  (tangentProjectionRaw P e).codRestrict (tangentSpace P e)
    (tangentProjectionRaw_mem P e he)

@[simp] theorem tangentProjection_coe  (e x : E)
    (he : diagonalCubic P.form e = 1) :
    (tangentProjection P e he x : E) =
      x - (fderiv ℝ (diagonalCubic P.form) e x / 3) • e :=
  tangentProjectionRaw_apply P e x

@[simp] theorem tangentProjection_basepoint 
     (he : diagonalCubic P.form e = 1) :
    tangentProjection P e he e = 0 := by
  apply Subtype.ext
  simp only [tangentProjection_coe,
    fderiv_diagonalCubic_at_one P.form e he, div_self (by norm_num : (3 : ℝ) ≠ 0),
    one_smul, sub_self, ZeroMemClass.coe_zero]

/-- The actual derivative split is a continuous linear equivalence with its
explicit inverse. Invertibility is derived from normalization and Euler. -/
def normalSplit  
    (he : diagonalCubic P.form e = 1) : E ≃L[ℝ] ℝ × tangentSpace P e :=
  { ((fderiv ℝ (diagonalCubic P.form) e).prod
      (tangentProjection P e he)).toLinearMap with
    invFun p := (p.1 / 3) • e + p.2
    left_inv x := by
      change (fderiv ℝ (diagonalCubic P.form) e x / 3) • e +
        (tangentProjection P e he x : E) = x
      rw [tangentProjection_coe]
      module
    right_inv p := by
      change (fderiv ℝ (diagonalCubic P.form) e ((p.1 / 3) • e + (p.2 : E)),
        tangentProjection P e he ((p.1 / 3) • e + (p.2 : E))) = p
      have hv : fderiv ℝ (diagonalCubic P.form) e (p.2 : E) = 0 := p.2.property
      have hn : fderiv ℝ (diagonalCubic P.form) e ((p.1 / 3) • e + (p.2 : E)) = p.1 := by
        simp only [map_add, map_smul, fderiv_diagonalCubic_at_one P.form e he,
          hv, smul_eq_mul]
        ring
      apply Prod.ext hn
      apply Subtype.ext
      rw [tangentProjection_coe, hn]
      module
    continuous_toFun :=
      (fderiv ℝ (diagonalCubic P.form) e).continuous.prodMk
        (tangentProjection P e he).continuous
    continuous_invFun := by fun_prop }

end
end AlbertGeometry.Cubic
