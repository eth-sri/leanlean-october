/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
public import CCDN.Height.PrimitiveIntegerPolynomial
import CCDN.Algebra.PrimitiveNormalization
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.Surface.TopFormIrreducibility

/-! Bad reduction of an affine equation is contained in bad reduction of
 its top homogeneous form. This includes degree loss in the defined predicate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If the top form has good geometric reduction, the original affine
 equation keeps its degree and has good geometric reduction as well. -/
private theorem hypersurfaceBadReduction_imp_top_homogeneousComponent {σ : Type*}
    (f : MvPolynomial σ ℤ) (p : ℕ) :
    HypersurfaceBadReduction f p →
      HypersurfaceBadReduction (homogeneousComponent f.totalDegree f) p := by
  intro hbad
  let : Fact p.Prime := ⟨hbad.1⟩
  by_contra hgood
  have hir := Classical.byContradiction (fun h => hgood ⟨hbad.1, Or.inr h⟩)
  obtain ⟨hd, hi⟩ := map_degree_and_irreducible_of_top_irreducible
    (Int.castRingHom (AlgebraicClosure (ZMod p))) f hir
  exact hbad.2.elim (· hd) (· hi)

/-- Absolute irreducibility of the highest homogeneous component implies
 absolute irreducibility of the original integer equation. -/
theorem absolute_irreducible_of_top_homogeneousComponent_irreducible {σ : Type*}
    (f : MvPolynomial σ ℤ)
    (hir : HasAbsIrreducibleTopForm f) :
    AbsolutelyIrreducible f :=
  (map_degree_and_irreducible_of_top_irreducible _ f hir).2

/-- The affine bad-prime factor is no greater than that of the top
 form when the latter is absolutely irreducible. -/
theorem hypersurfaceBadPrimeFactor_le_top_homogeneousComponent {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hir : HasAbsIrreducibleTopForm f) :
    hypersurfaceBadPrimeFactor f ≤
      hypersurfaceBadPrimeFactor (homogeneousComponent f.totalDegree f) := by
  have htop : homogeneousComponent f.totalDegree f ≠ 0 := by
    intro hz
    exact hir.ne_zero (by simp_all)
  apply hypersurfaceBadPrimeFactor_mono_of_badReduction_imp
  exact Eq.symm (IsHomogeneous.totalDegree (homogeneousComponent_isHomogeneous f.totalDegree f) htop)
  tauto
  · exact hypersurfaceBadReduction_imp_top_homogeneousComponent f

/-- Primitivity reflects the irreducibility supplied by the absolute top form
 back to the integer polynomial ring. -/
theorem PrimitiveIntegerPolynomial.irreducible_of_absolute_top {σ : Type*}
    {f : MvPolynomial σ ℤ} (hprim : PrimitiveIntegerPolynomial f)
    (hir : HasAbsIrreducibleTopForm f) : Irreducible f := by
  apply hprim.irreducible_of_rational_map
  exact rational_irreducible_of_charZero_map f
    (absolute_irreducible_of_top_homogeneousComponent_irreducible f hir)

/-- Remove the integer content while preserving the rational equation and its top-form condition. -/
theorem exists_primitive_top_form {σ : Type*} {f : MvPolynomial σ ℤ}
    (hir : HasAbsIrreducibleTopForm f) :
    ∃ g, PrimitiveIntegerPolynomial g ∧ g.totalDegree = f.totalDegree ∧ HasAbsIrreducibleTopForm g ∧
      Associated (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) g) := by
  have hf : f ≠ 0 := by intro hz; exact hir.ne_zero (by simp [hz])
  obtain ⟨c, g, hc, hp, he⟩ := exists_primitive_integer_factor f hf
  have ha : Associated (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) g) := by
    rw [he, map_mul, map_C]
    exact (associated_int_C_mul _ hc).symm
  have hd : g.totalDegree = f.totalDegree := by
    simpa only [totalDegree_map_of_injective (f := Int.castRingHom ℚ) Int.cast_injective] using
      rational_model_degree ha (by simpa using (map_injective _ Int.cast_injective).ne hf)
  refine ⟨g, hp, hd, ?_, ha⟩
  · unfold HasAbsIrreducibleTopForm AbsolutelyIrreducible at hir
    rw [congrArg (homogeneousComponent f.totalDegree) he, homogeneousComponent_C_mul,
      map_mul, map_C, ← hd] at hir
    exact (associated_int_C_mul _ hc).symm.irreducible hir

end
end CCDN
