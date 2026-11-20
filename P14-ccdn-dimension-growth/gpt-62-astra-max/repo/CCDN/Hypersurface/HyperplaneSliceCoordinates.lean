/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hypersurface.IntegerHyperplaneSlices
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Coordinate transport between the graph-hyperplane construction and
the finite integral-point count. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Renaming the variables of an integer polynomial along an equivalence preserves absolute
irreducibility of its top-degree form. -/
lemma integer_top_irreducible_rename {σ τ : Type*} (e : σ ≃ τ)
    (f : MvPolynomial σ ℤ)
    (hir : HasAbsIrreducibleTopForm f) :
    HasAbsIrreducibleTopForm (rename e f) := by
  dsimp only [HasAbsIrreducibleTopForm, AbsolutelyIrreducible]
  rw [show (rename e f).totalDegree = f.totalDegree from totalDegree_renameEquiv e f,
    ← rename_homogeneousComponent, map_rename]
  exact (MulEquiv.irreducible_iff (f := renameEquiv _ e)).mpr hir

variable {n : ℕ} (D : ℤ) (a : Fin n → ℤ)

/-- The integer normal vector `(D, -a 0, …, -a (n - 1))` of the hyperplane
`D * x 0 = ∑ a i * x (i + 1)`. -/
def graphIntegerNormal : IntPoint (n + 1) :=
  Fin.cons D (fun i => -a i)

/-- If `|D|` and every `|a i|` are at most `H`, then every coordinate of `graphIntegerNormal D a`
has absolute value at most `H`. -/
lemma graphIntegerNormal_height {H : ℕ}
    (hD : |D| ≤ (H : ℤ)) (ha : ∀ i, |a i| ≤ (H : ℤ)) :
    ∀ i, |(graphIntegerNormal D a i : ℝ)| ≤ (H : ℝ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact_mod_cast hD
  · simpa [graphIntegerNormal] using
      (show |(a j : ℝ)| ≤ H by exact_mod_cast ha j)

/-- Integral equations suffice for the rational zero-locus map used by
the count: the only coordinate change is deleting coordinate zero. -/
theorem integer_slice_map_of_option_equations
    (f : IntegerPolynomial (n + 1)) (D : ℤ) (a : Fin n → ℤ)
    (g : ℤ → IntegerPolynomial n)
    (hslice : ∀ k (x : Option (Fin n) → ℤ),
      D * x none - ∑ i, a i * x (some i) = k →
      eval x (rename (finSuccEquiv' 0) f) = 0 →
      eval (fun i => x (some i)) (g k) = 0)
    (B : ℝ) (k : ℤ) (x : IntPoint (n + 1))
    (hx : x ∈ integerSlicePoints (zeroLocus (rationalEquation f))
      B (graphIntegerNormal D a) k) :
    rationalPoint (deleteIntegerCoordinate 0 x) ∈
      zeroLocus (rationalEquation (g k)) := by
  classical
  let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv' 0
  let z := x ∘ e.symm
  have hlevel := (Finset.mem_filter.mp hx).2
  have hzlevel := by
    change (∑ i, graphIntegerNormal D a i * x i) = k at hlevel
    rw [Fin.sum_univ_succ] at hlevel
    simp only [graphIntegerNormal, Fin.cons_zero, Fin.cons_succ, neg_mul,
      Finset.sum_neg_distrib] at hlevel
    exact hlevel
  have hfxZ : eval x f = 0 := by
    have he := map_eval (Int.castRingHom ℚ) x f
    exact Int.cast_injective (he.trans ((mem_integralPoints.mp (Finset.mem_filter.mp hx).1).2))
  have hz : eval z (rename e f) = 0 := by
    rw [eval_rename]
    simpa [z, Function.comp_def] using hfxZ
  have hgZ := hslice k z hzlevel hz
  change eval (rationalPoint (deleteIntegerCoordinate 0 x))
    (rationalEquation (g k)) = 0
  have he : eval (rationalPoint (deleteIntegerCoordinate 0 x))
      (rationalEquation (g k)) =
      ((eval (fun i => z (some i)) (g k) : ℤ) : ℚ) := by
    exact (map_eval (Int.castRingHom ℚ) (fun i => z (some i)) (g k)).symm
  simp_all

end
end CCDN
