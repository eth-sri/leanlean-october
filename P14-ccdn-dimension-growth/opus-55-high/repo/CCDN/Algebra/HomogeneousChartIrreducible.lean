/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousChart
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Dehomogenization preserves degree and irreducibility when the
homogenizing coordinate does not divide the homogeneous equation. -/

namespace CCDN
section
open MvPolynomial

/-- A full-degree affine chart detects irreducibility of the original
equation; a factor lost on the chart would force a degree drop. -/
theorem irreducible_of_affineChart_irreducible {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K)
    (hdeg : (affineChart n f).totalDegree = f.totalDegree)
    (hir : Irreducible (affineChart n f)) : Irreducible f := by
  have hf0 : f ≠ 0 := by aesop
  have hunit (a : MvPolynomial (Fin (n + 1)) K) (ha : a ≠ 0)
      (hda : a.totalDegree = (affineChart n a).totalDegree)
      (hu : IsUnit (affineChart n a)) : IsUnit a := by
    have ha0 := hda.trans (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have he := totalDegree_eq_zero_iff_eq_C.mp ha0
    rw [he]
    apply (isUnit_iff_ne_zero.mpr ?_).map C
    intro hc
    exact ha (by grind)
  refine ⟨fun h => hir.not_isUnit (h.map (affineChart n)), ?_⟩
  intro a b hab
  have ha : a ≠ 0 := by grind
  have hb : b ≠ 0 := by grind
  have hc : affineChart n f = affineChart n a * affineChart n b := by grind
  have hac : affineChart n a ≠ 0 := by aesop
  have hbc : affineChart n b ≠ 0 := by aesop
  have hsum := totalDegree_mul_of_isDomain ha hb
  have hsumc := totalDegree_mul_of_isDomain hac hbc
  rw [← hab] at hsum
  rw [← hc, hdeg, hsum] at hsumc
  have hla := affineChart_totalDegree_le a
  have hlb := affineChart_totalDegree_le b
  obtain hau | hbu := hir.isUnit_or_isUnit hc
  · grind
  · grind

variable {K : Type*} [Field K] {n d : ℕ} (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d)
include hf

/-- No variable `X j` divides an irreducible homogeneous polynomial of degree at least `2`. -/
theorem variable_not_dvd_irreducible_homogeneous
    (hir : Irreducible f) (hd : 2 ≤ d) (j : Fin (n + 1)) : ¬ X j ∣ f := by
  rintro ⟨g, hg⟩
  have hu := (hir.isUnit_or_isUnit hg).resolve_left (by
    intro hu
    have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    simp_all)
  have h := totalDegree_mul (X j) g
  rw [← hg, hf.totalDegree hir.ne_zero, totalDegree_X,
    (isUnit_iff_totalDegree_of_isReduced.mp hu).2] at h
  omega

/-- An irreducible homogeneous polynomial of degree at least `2` divides no variable `X j`. -/
theorem irreducible_homogeneous_not_dvd_variable
    (hir : Irreducible f) (hd : 2 ≤ d) (j : Fin (n + 1)) : ¬ f ∣ X j := by
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by aesop
  have hh := congrArg totalDegree hg
  rw [totalDegree_X, totalDegree_mul_of_isDomain hir.ne_zero hg0,
    hf.totalDegree hir.ne_zero] at hh
  omega

/-- If `X 0` does not divide the homogeneous polynomial `f` of degree `d`, then the affine chart
`x₀ = 1` of `f` has total degree exactly `d`. -/
theorem affineChart_degree_of_not_variable_dvd
    (hX : ¬ X 0 ∣ f) : (affineChart n f).totalDegree = d := by
  have hle := (affineChart_totalDegree_le f).trans hf.totalDegree_le
  by_contra hne
  have hd : 0 < d := by omega
  have hsmall : (affineChart n f).totalDegree ≤ d - 1 := by omega
  let g := scaledHomogenize (d - 1) 1 (affineChart n f)
  have hg := scaledHomogenize_homogeneous 1 _ hsmall
  have he : f = X 0 * g := by
    apply affineChart_injective_on_homogeneous hf (by
      convert (isHomogeneous_X K (0 : Fin (n + 1))).mul hg using 1
      omega)
    rw [map_mul, show affineChart n (X 0) = 1 by simp [affineChart],
      one_mul, affineChart_scaledHomogenize_one]
  exact hX ⟨g, he⟩

/-- If `X 0` does not divide the irreducible homogeneous polynomial `f`, then the affine chart
`x₀ = 1` of `f` is irreducible. -/
theorem affineChart_irreducible_of_not_variable_dvd
    (hir : Irreducible f) (hX : ¬ X 0 ∣ f) :
    Irreducible (affineChart n f) := by
  have hdeg := affineChart_degree_of_not_variable_dvd f hf hX
  have hd : 0 < d := by
    rw [← hf.totalDegree hir.ne_zero]
    exact MvPolynomial.totalDegree_pos_of_irreducible hir
  have hc0 : affineChart n f ≠ 0 := by aesop
  refine ⟨?_, ?_⟩
  · intro hu
    have hh := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    grind
  · intro a b hab
    have ha0 : a ≠ 0 := by grind
    have hb0 : b ≠ 0 := by grind
    have hsum : a.totalDegree + b.totalDegree = d := by
      rw [← totalDegree_mul_of_isDomain ha0 hb0, ← hab, hdeg]
    have hh : (scaledHomogenize a.totalDegree 1 a *
        scaledHomogenize b.totalDegree 1 b).IsHomogeneous d := by
      simpa [hsum] using (scaledHomogenize_homogeneous 1 a le_rfl).mul
        (scaledHomogenize_homogeneous 1 b le_rfl)
    obtain ha | hb := hir.isUnit_or_isUnit (by
      apply affineChart_injective_on_homogeneous hf hh
      simp_all [map_mul, affineChart_scaledHomogenize_one])
    · left
      simpa [affineChart_scaledHomogenize_one] using ha.map (affineChart n)
    · right
      simpa [affineChart_scaledHomogenize_one] using hb.map (affineChart n)

