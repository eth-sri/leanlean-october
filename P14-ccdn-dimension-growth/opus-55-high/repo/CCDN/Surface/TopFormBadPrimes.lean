/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Height.PrimitiveIntegerPolynomial
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.Surface.TopFormIrreducibility

/-! Bad reduction of an affine equation is contained in bad reduction of
 its top homogeneous form. This includes degree loss in the defined predicate. -/

namespace CCDN
section
open MvPolynomial

section
variable {σ : Type*} (f : MvPolynomial σ ℤ)

/-- If the top form has good geometric reduction, the original affine
 equation keeps its degree and has good geometric reduction as well. -/
theorem hypersurfaceBadReduction_imp_top_homogeneousComponent
    (p : ℕ) :
    HypersurfaceBadReduction f p →
      HypersurfaceBadReduction (homogeneousComponent f.totalDegree f) p := by
  intro hbad
  let : Fact p.Prime := ⟨hbad.1⟩
  by_contra hgood
  have hir : Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p)))
      (homogeneousComponent f.totalDegree f)) := by
    by_contra h
    exact hgood ⟨hbad.1, Or.inr h⟩
  obtain ⟨hdegree, hfull⟩ := map_degree_and_irreducible_of_top_irreducible _ f hir
  exact hbad.2.elim (fun h => h hdegree) (fun h => h hfull)

/-- Absolute irreducibility of the highest homogeneous component implies
 absolute irreducibility of the original integer equation. -/
theorem absolute_irreducible_of_top_homogeneousComponent_irreducible
    (hir : HasAbsIrreducibleTopForm f) :
    AbsolutelyIrreducible f :=
  (map_degree_and_irreducible_of_top_irreducible _ f hir).2

end

variable {σ : Type*}

/-- Primitivity reflects the irreducibility supplied by the absolute top form
 back to the integer polynomial ring. -/
theorem PrimitiveIntegerPolynomial.irreducible_of_absolute_top
    {f : MvPolynomial σ ℤ} (hprim : PrimitiveIntegerPolynomial f)
    (hir : HasAbsIrreducibleTopForm f) : Irreducible f := by
  apply hprim.irreducible_of_rational_map
  exact rational_irreducible_of_charZero_map f
    (absolute_irreducible_of_top_homogeneousComponent_irreducible f hir)

/-- Removing nonzero integer content preserves absolute irreducibility of
 the top homogeneous form, along with the affine degree. -/
theorem absolute_top_irreducible_of_integer_scalar_factor
    {f g : MvPolynomial σ ℤ} {c : ℤ} (hc : c ≠ 0) (he : f = C c * g)
    (hir : HasAbsIrreducibleTopForm f) :
    g.totalDegree = f.totalDegree ∧
      HasAbsIrreducibleTopForm g := by
  have hf : f ≠ 0 := by
    intro hz
    exact hir.ne_zero (by grind)
  have hdegree : g.totalDegree = f.totalDegree := by
    have hg : g ≠ 0 := by
      intro hg
      apply hf
      rw [he, hg, mul_zero]
    rw [he, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr hc) hg, totalDegree_C, zero_add]
  refine ⟨hdegree, ?_⟩
  have htop : homogeneousComponent f.totalDegree f =
      C c * homogeneousComponent g.totalDegree g := by
    calc
      _ = homogeneousComponent f.totalDegree (C c * g) := congrArg (homogeneousComponent _) he
      _ = C c * homogeneousComponent f.totalDegree g := homogeneousComponent_C_mul _ _ _
      _ = _ := by grind
  dsimp [HasAbsIrreducibleTopForm, AbsolutelyIrreducible] at hir
  rw [htop, map_mul, map_C] at hir
  exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr (by simp_all)).map C)).mp hir

