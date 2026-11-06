module

public import Mathlib

public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import DedekindZetaZeroFree.Algebra.Matrices.TwoDimensionalAdjugate
public import DedekindZetaZeroFree.Algebra.MatrixGroups.SpecialUnitaryAdjugate
public import DedekindZetaZeroFree.Geometry.UnitaryGroups.Compactness
public import DedekindZetaZeroFree.Geometry.Circle.InverseSeparation

@[expose] public section


/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/SU2/Basic.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

namespace DedekindZetaZeroFree.TauCeti

abbrev SU2 : Type := Matrix.specialUnitaryGroup (Fin 2) ℂ

namespace SU2

theorem coe_add_star (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) + star (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) • 1 := by
  simp [Matrix.specialUnitaryGroup.star_eq_adjugate,
    Matrix.adjugate_fin_two_eq_trace_smul_one_sub]

theorem trace_eq_of_isConj {g h : SU2} (hgh : IsConj g h) :
    Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨u, rfl⟩ := isConj_iff.mp hgh

  simpa using
    (Matrix.trace_units_conj (Units.map (Submonoid.subtype _) (toUnits u))
      (g : Matrix (Fin 2) (Fin 2) ℂ)).symm

section
variable (z : Circle)
include z
noncomputable def torusMatrix   : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(z : ℂ), ((z : ℂ))⁻¹]

@[simp]
theorem torusMatrix_apply_zero_zero   : torusMatrix z 0 0 = (z : ℂ) := rfl

@[simp]
theorem torusMatrix_apply_one_one   : torusMatrix z 1 1 = ((z : ℂ))⁻¹ := rfl

@[simp]
theorem torusMatrix_apply_zero_one   : torusMatrix z 0 1 = 0 := rfl

@[simp]
theorem torusMatrix_apply_one_zero   : torusMatrix z 1 0 = 0 := rfl
end


@[simp]
theorem torusMatrix_one : torusMatrix 1 = 1 := by
  rw [torusMatrix, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

@[simp]
theorem torusMatrix_mul (z w : Circle) :
    torusMatrix (z * w) = torusMatrix z * torusMatrix w := by
  rw [torusMatrix, torusMatrix, torusMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_comm]

@[simp]
theorem star_torusMatrix (z : Circle) : star (torusMatrix z) = torusMatrix z⁻¹ := by
  have hz : star (z : ℂ) = ((z : ℂ))⁻¹ := (Circle.coe_inv_eq_conj z).symm
  rw [Matrix.star_eq_conjTranspose, torusMatrix, torusMatrix, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  fin_cases i <;> simp [hz]

@[simp]
theorem trace_torusMatrix (z : Circle) :
    (torusMatrix z).trace = (z : ℂ) + ((z : ℂ))⁻¹ := by
  rw [Matrix.trace_fin_two, torusMatrix_apply_zero_zero, torusMatrix_apply_one_one]

@[simp]
theorem det_torusMatrix (z : Circle) : (torusMatrix z).det = 1 := by
  rw [torusMatrix, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem torusMatrix_mem (z : Circle) :
    torusMatrix z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, det_torusMatrix z⟩
  rw [Matrix.mem_unitaryGroup_iff, star_torusMatrix, ← torusMatrix_mul, mul_inv_cancel,
    torusMatrix_one]

theorem continuous_torusMatrix : Continuous torusMatrix := by
  have hcoe : Continuous fun z : Circle => (z : ℂ) := continuous_subtype_val
  have hinv : Continuous fun z : Circle => ((z : ℂ))⁻¹ := hcoe.inv₀ fun z => z.coe_ne_zero
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  fin_cases i
  · exact hcoe
  · exact hinv

noncomputable def torusHom : Circle →* SU2 where
  toFun z := ⟨torusMatrix z, torusMatrix_mem z⟩
  map_one' := Subtype.ext torusMatrix_one
  map_mul' z w := Subtype.ext (torusMatrix_mul z w)

@[simp]
theorem coe_torusHom (z : Circle) : (torusHom z : Matrix (Fin 2) (Fin 2) ℂ) = torusMatrix z := (rfl)

theorem continuous_torusHom : Continuous torusHom :=
  continuous_induced_rng.mpr continuous_torusMatrix

noncomputable def torus  := torusHom.range

theorem torusHom_mem_torus (z : Circle) : torusHom z ∈ torus := ⟨z, rfl⟩

theorem mem_torus_iff_exists_torusHom {g : SU2} : g ∈ torus ↔ ∃ z : Circle, torusHom z = g :=
  torusHom.mem_range

@[simp]
theorem mem_torus_iff {g : SU2} :
    g ∈ torus ↔ Matrix.IsDiag (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [coe_torusHom, torusMatrix]
    exact Matrix.isDiag_diagonal _
  · intro hdiag
    have h01 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := hdiag (by decide)
    have h10 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := hdiag (by decide)
    have hunit : (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
    have hmul : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * star ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
        = 1 := by
      have h := congrFun (congrFun hunit 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_two] at h
      simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply,
        h01] using h
    have hnorm : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = 1 := by
      have h := congrArg norm hmul
      rw [norm_mul, norm_star, norm_one] at h
      nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)]
    have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := by
      have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
      rw [Matrix.det_fin_two, h01] at h
      simpa using h
    have h11 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    obtain ⟨z, hz⟩ : ∃ z : Circle, (z : ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
      ⟨⟨_, mem_sphere_zero_iff_norm.mpr hnorm⟩, rfl⟩
    refine ⟨z, Subtype.ext ?_⟩
    rw [coe_torusHom, torusMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz, h01, h10, h11]

theorem torusHom_injective : Function.Injective torusHom := fun z w h => by
  have h00 := congrArg (fun g : SU2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  apply Circle.ext <;> assumption

noncomputable def torusContinuousMulEquiv : Circle ≃ₜ* torus where
  __ := MonoidHom.ofInjective torusHom_injective
  continuous_toFun := continuous_torusHom.subtype_mk _
  continuous_invFun :=
    (Continuous.homeoOfEquivCompactToT2
      (f := (MonoidHom.ofInjective torusHom_injective).toEquiv)
      (continuous_torusHom.subtype_mk _)).continuous_invFun

instance : CompactSpace torus := torusContinuousMulEquiv.toHomeomorph.compactSpace











instance : IsMulCommutative torus :=
  .of_setLike_mul_comm <| by
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
















































theorem eq_or_eq_inv_of_trace_torusMatrix_eq {z w : Circle}
    (h : (torusMatrix w).trace = (torusMatrix z).trace) : w = z ∨ w = z⁻¹ := by
  rw [trace_torusMatrix, trace_torusMatrix] at h
  have hfac : ((w : ℂ) - (z : ℂ)) * ((w : ℂ) - ((z : ℂ))⁻¹) = 0 := by
    have hw : (w : ℂ) * ((w : ℂ))⁻¹ = 1 := mul_inv_cancel₀ w.coe_ne_zero
    have hzz : (z : ℂ) * ((z : ℂ))⁻¹ = 1 := mul_inv_cancel₀ z.coe_ne_zero
    linear_combination (w : ℂ) * h - hw + hzz
  rcases mul_eq_zero.mp hfac with hc | hc
  · exact Or.inl (Circle.ext (sub_eq_zero.mp hc))
  · exact Or.inr (Circle.ext (by rw [Circle.coe_inv]; exact sub_eq_zero.mp hc))

theorem eq_or_eq_inv_of_conj_torusHom {z w : Circle} {g : SU2}
    (h : g * torusHom z * g⁻¹ = torusHom w) : w = z ∨ w = z⁻¹ :=
  eq_or_eq_inv_of_trace_torusMatrix_eq
    ((trace_eq_of_isConj (isConj_iff.mpr ⟨g, h⟩)).symm)

noncomputable def torusExp (θ : ℝ)  := torusHom (Circle.exp θ)

theorem torusExp_def (θ : ℝ) : torusExp θ = torusHom (Circle.exp θ) := (rfl)

@[simp]
theorem coe_torusExp (θ : ℝ) :
    (torusExp θ : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.diagonal ![Complex.exp (θ * Complex.I), Complex.exp (-(θ * Complex.I))] := by
  rw [torusExp, coe_torusHom, torusMatrix]
  congr 1
  ext i
  fin_cases i <;> simp [← Complex.exp_neg]

theorem trace_torusExp (θ : ℝ) :
    Matrix.trace ((torusExp θ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 2 * (Real.cos θ : ℂ) := by

  simp [Complex.two_cos]





@[simp]
theorem torusExp_zero : torusExp 0 = 1 := by rw [torusExp, Circle.exp_zero, map_one]





theorem continuous_torusExp : Continuous torusExp :=
  (continuous_torusHom.comp Circle.exp.continuous).congr fun θ => rfl

end SU2

end DedekindZetaZeroFree.TauCeti
