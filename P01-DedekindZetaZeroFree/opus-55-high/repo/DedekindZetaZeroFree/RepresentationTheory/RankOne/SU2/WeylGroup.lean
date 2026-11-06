module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.MaximalTorus

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/Weyl/Basic.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

def weylMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

theorem weylMatrix_mem : weylMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weylMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  · simp [weylMatrix, Matrix.det_fin_two]

def weylElement : SU2 := ⟨weylMatrix, weylMatrix_mem⟩

@[simp]
theorem coe_weylElement : (weylElement : Matrix (Fin 2) (Fin 2) ℂ) = weylMatrix := (rfl)

theorem weylMatrix_mul_torusMatrix (z : Circle) :
    weylMatrix * torusMatrix z = torusMatrix z⁻¹ * weylMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem weylElement_mul_torusHom (z : Circle) :
    weylElement * torusHom z = torusHom z⁻¹ * weylElement := by
  refine Subtype.ext ?_
  simp only [Submonoid.coe_mul, coe_weylElement, coe_torusHom]
  exact weylMatrix_mul_torusMatrix z

@[simp]
theorem weylElement_conj_torusHom (z : Circle) :
    weylElement * torusHom z * weylElement⁻¹ = torusHom z⁻¹ :=
  mul_inv_eq_iff_eq_mul.mpr (weylElement_mul_torusHom z)
