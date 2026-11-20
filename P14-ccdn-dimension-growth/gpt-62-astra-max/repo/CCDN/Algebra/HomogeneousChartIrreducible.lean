/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Dehomogenization preserves degree and irreducibility when the
homogenizing coordinate does not divide the homogeneous equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K : Type*} [Field K] {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f.IsHomogeneous d) (hir : Irreducible f) (hX : ¬ X 0 ∣ f)

/-- A full-degree affine chart detects irreducibility of the original
equation; a factor lost on the chart would force a degree drop. -/
theorem irreducible_of_affineChart_irreducible
    (hdeg : (affineChart n f).totalDegree = f.totalDegree)
    (hir : Irreducible (affineChart n f)) : Irreducible f := by
  have hf0 : f ≠ 0 := by aesop
  have hunit (a : MvPolynomial (Fin (n + 1)) K) (ha : a ≠ 0)
      (hda : a.totalDegree = (affineChart n a).totalDegree)
      (hu : IsUnit (affineChart n a)) : IsUnit a := by
    have he := totalDegree_eq_zero_iff_eq_C.mp (hda.trans (isUnit_iff_totalDegree_of_isReduced.mp hu).2)
    rw [he]
    apply (isUnit_iff_ne_zero.mpr ?_).map C
    grind
  refine ⟨fun h => hir.not_isUnit (h.map (affineChart n)), ?_⟩
  intro a b hab
  have ha : a ≠ 0 := by grind
  have hb : b ≠ 0 := by grind
  have hac : affineChart n a ≠ 0 := by
    grind [hir.ne_zero, zero_mul]
  have hbc : affineChart n b ≠ 0 := by
    grind [hir.ne_zero, mul_zero]
  have hsum := totalDegree_mul_of_isDomain ha hb
  have hsumc := totalDegree_mul_of_isDomain hac hbc
  grind [affineChart_totalDegree_le, hir.isUnit_or_isUnit]

include hf hir in
/-- No variable `X j` divides an irreducible homogeneous polynomial of degree at least `2`. -/
theorem variable_not_dvd_irreducible_homogeneous (hd : 2 ≤ d) (j : Fin (n + 1)) : ¬ X j ∣ f := by
  rintro ⟨g, hg⟩
  have hx : ¬ IsUnit (X j : MvPolynomial (Fin (n + 1)) K) := by
    intro hu
    have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    simp at h
  have h := totalDegree_mul (X j) g
  rw [← hg, hf.totalDegree hir.ne_zero, totalDegree_X,
    (isUnit_iff_totalDegree_of_isReduced.mp ((hir.isUnit_or_isUnit hg).resolve_left hx)).2] at h
  omega

include hf hX in
/-- If `X 0` does not divide the homogeneous polynomial `f` of degree `d`, then the affine chart
`x₀ = 1` of `f` has total degree exactly `d`. -/
theorem affineChart_degree_of_not_variable_dvd : (affineChart n f).totalDegree = d := by
  have hle := (affineChart_totalDegree_le f).trans hf.totalDegree_le
  by_contra hne
  have hsmall : (affineChart n f).totalDegree ≤ d - 1 := by omega
  let g := scaledHomogenize (d - 1) 1 (affineChart n f)
  have hxg : (X 0 * g).IsHomogeneous d := by
    convert (isHomogeneous_X K 0).mul (scaledHomogenize_homogeneous 1 _ hsmall) using 1
    omega
  have he := by
    apply affineChart_injective_on_homogeneous hf hxg
    rw [map_mul, show affineChart n (X 0) = 1 by simp [affineChart],
      one_mul, affineChart_scaledHomogenize_one]
  exact hX ⟨g, he⟩

include hf hir hX in
/-- If `X 0` does not divide the irreducible homogeneous polynomial `f`, then the affine chart
`x₀ = 1` of `f` is irreducible. -/
theorem affineChart_irreducible_of_not_variable_dvd :
    Irreducible (affineChart n f) := by
  have hdeg := affineChart_degree_of_not_variable_dvd f hf hX
  have hd : 0 < d := by
    rw [← hf.totalDegree hir.ne_zero]
    exact MvPolynomial.totalDegree_pos_of_irreducible hir
  have hc0 : affineChart n f ≠ 0 := by
    aesop
  refine ⟨?_, ?_⟩
  · intro hu
    have hh := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · intro a b hab
    have ha0 : a ≠ 0 := by grind
    have hsum : a.totalDegree + b.totalDegree = d := by
      grind [totalDegree_mul_of_isDomain]
    have hh := by
      simpa [hsum] using (scaledHomogenize_homogeneous 1 a le_rfl).mul
        (scaledHomogenize_homogeneous 1 b le_rfl)
    have he := by
      apply affineChart_injective_on_homogeneous hf hh
      rw [map_mul, affineChart_scaledHomogenize_one, affineChart_scaledHomogenize_one]
      exact hab
    obtain ha | hb := hir.isUnit_or_isUnit he
    · left
      simpa [affineChart_scaledHomogenize_one] using ha.map (affineChart n)
    · right
      simpa [affineChart_scaledHomogenize_one] using hb.map (affineChart n)

end
end CCDN
