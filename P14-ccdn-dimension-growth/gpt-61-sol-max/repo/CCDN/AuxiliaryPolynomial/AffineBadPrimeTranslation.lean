/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.AffineTranslation
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
public import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.AuxiliaryPolynomial.AffineTranslationCount

/-! Integral translations preserve the affine bad-prime factor, including
degree-dropping reductions and the nonabsolute zero convention. -/

public section
namespace CCDN
open MvPolynomial

variable {n : ℕ}

private lemma hypersurfaceBadReduction_affineTranslation 
    (a : CCDN.IntPoint n) (f : CCDN.IntegerPolynomial n) (p : ℕ) :
    HypersurfaceBadReduction (affineTranslation ℤ a f) p ↔ HypersurfaceBadReduction f p := by
  apply exists_congr
  intro hp
  dsimp only
  rw [affineTranslation_map, affineTranslation_totalDegree, affineTranslation_totalDegree,
    affineTranslation_irreducible_iff]

/-- The bad-prime factor of an integral polynomial is invariant under integral affine
translation of the variables. -/
theorem hypersurfaceBadPrimeFactor_affineTranslation 
    (a : CCDN.IntPoint (n + 1)) (f : CCDN.IntegerPolynomial (n + 1)) :
    hypersurfaceBadPrimeFactor (affineTranslation ℤ a f) = hypersurfaceBadPrimeFactor f := by
  classical
  have hir : AbsolutelyIrreducible (affineTranslation ℤ a f) ↔ AbsolutelyIrreducible f := by
    grind [affineTranslation_map, affineTranslation_irreducible_iff]
  by_cases hf : AbsolutelyIrreducible f
  · let bad := (finite_fin_hypersurface_bad_primes f hf
      (absolute_integer_polynomial_totalDegree_pos f hf)).toFinset
    have hbad (p) : p ∈ bad ↔ stepanovThreshold f.totalDegree < p ∧
        HypersurfaceBadReduction f p := by
      aesop
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl bad hbad]
    exact hypersurfaceBadPrimeFactor_eq_exp _ (hir.mpr hf) (affineTranslation_totalDegree a f)
      bad (by simp_all [hypersurfaceBadReduction_affineTranslation])
  · simp_all [hypersurfaceBadPrimeFactor_eq_zero]

/-- Pull an auxiliary equation back through a bounded translation. -/
theorem affine_auxiliary_translation_transport 
    (f g : CCDN.IntegerPolynomial n) (a : CCDN.IntPoint n) {B D : ℝ}
    (hg : IsBoxAuxiliary (affineTranslation ℤ a f) g (B + D)) (ha : InBox a D) :
    ∃ G, IsBoxAuxiliary f G B ∧ G.totalDegree = g.totalDegree := by
  let G := (affineTranslation ℤ a).symm g
  have hGnd : ¬ f ∣ G := by
    intro hd
    apply hg.not_dvd
    have hh := map_dvd (affineTranslation ℤ a).toRingHom hd
    change affineTranslation ℤ a f ∣ affineTranslation ℤ a ((affineTranslation ℤ a).symm g) at hh
    simpa only [AlgEquiv.apply_symm_apply] using hh
  refine ⟨G, ⟨hGnd, ?_⟩, affineTranslation_totalDegree (-a) g⟩
  intro x hx hxf
  have hx' (j) : |((x - a) j : ℝ)| ≤ B + D := by
    change |((x j - a j : ℤ) : ℝ)| ≤ _
    rw [Int.cast_sub]
    exact (abs_sub _ _).trans (add_le_add (hx j) (ha j))
  have hf' : eval (x - a) (affineTranslation ℤ a f) = 0 := by
    rw [affineTranslation_eval, sub_add_cancel, hxf]
  change eval x (affineTranslation ℤ (-a) g) = 0
  rw [affineTranslation_eval]
  exact hg.vanishes (x - a) hx' hf'

end CCDN
