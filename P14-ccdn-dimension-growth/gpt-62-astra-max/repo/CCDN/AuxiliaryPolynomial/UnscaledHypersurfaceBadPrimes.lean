/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.ScaledHomogenization
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Comparison with the affine bad-prime factor. For degree at least two the
homogeneous and affine bad-reduction predicates agree. In degree one, the
homogeneous bad-prime set can be smaller because affine degree loss can
produce a nonzero multiple of the homogenizing variable. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {n : ℕ} (f : IntegerPolynomial n) (hf : f ≠ 0)

include hf in
lemma hypersurfaceBadReduction_unscaledHomogenize_imp (p : ℕ) :
    HypersurfaceBadReduction (scaledHomogenize f.totalDegree 1 f) p →
      HypersurfaceBadReduction f p := by
  intro hbad
  let : Fact p.Prime := ⟨hbad.1⟩
  have hnot := (homogeneous_hypersurfaceBadReduction_iff _
    (scaledHomogenize_homogeneous 1 f le_rfl)
    (scaledHomogenize_ne_zero _ one_ne_zero hf) p).mp hbad
  refine ⟨hbad.1, ?_⟩
  by_cases hd : (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree = f.totalDegree
  · right
    intro hir
    apply hnot
    rw [scaledHomogenize_map, map_one, ← hd]
    exact scaledHomogenize_irreducible _ hir one_ne_zero
  · exact Or.inl hd

end

variable {n m : ℕ} (f : IntegerPolynomial (n + 1))

/-- Inclusion of the geometric bad-prime sets gives monotonicity of
 the corresponding factors, even across different numbers of variables. -/
theorem hypersurfaceBadPrimeFactor_mono_of_badReduction_imp (g : IntegerPolynomial (m + 1))
    (hd : f.totalDegree = g.totalDegree)
    (habs : AbsolutelyIrreducible f → AbsolutelyIrreducible g)
    (hbad : ∀ q, HypersurfaceBadReduction f q → HypersurfaceBadReduction g q) :
    hypersurfaceBadPrimeFactor f ≤ hypersurfaceBadPrimeFactor g := by
  classical
  by_cases hf : AbsolutelyIrreducible f
  · have hg := habs hf
    let S := (finite_fin_hypersurface_bad_primes f hf
      (absolute_integer_polynomial_totalDegree_pos f hf)).toFinset
    let T := (finite_fin_hypersurface_bad_primes g hg
      (absolute_integer_polynomial_totalDegree_pos g hg)).toFinset
    have hS : ∀ q, q ∈ S ↔ stepanovThreshold f.totalDegree < q ∧ HypersurfaceBadReduction f q := by
      aesop
    have hT : ∀ q, q ∈ T ↔ stepanovThreshold g.totalDegree < q ∧ HypersurfaceBadReduction g q := by
      aesop
    have hsub : S ⊆ T := by
      grind
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl S hS,
      hypersurfaceBadPrimeFactor_eq_exp g hg rfl T hT]
    apply Real.exp_le_exp.mpr
    gcongr
  grind [hypersurfaceBadPrimeFactor_eq_zero, hypersurfaceBadPrimeFactor_nonneg]

end
end CCDN
