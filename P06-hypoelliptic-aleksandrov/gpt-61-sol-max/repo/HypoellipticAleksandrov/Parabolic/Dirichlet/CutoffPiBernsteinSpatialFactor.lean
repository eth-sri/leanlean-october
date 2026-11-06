module

public import PDEFoundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.RingTheory.Polynomial.Bernstein
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Cutoff product-Bernstein spatial factors

This module bundles a product-Bernstein polynomial multiplied by a fixed smooth compactly
supported cutoff as a spatial weak test function.
-/

 public section

open scoped BigOperators



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Multiplying a product-Bernstein polynomial by the fixed cutoff gives a spatial weak test. -/
theorem exists_cutoffPiBernsteinSpatialFactor
    {d n : ℕ} {O : PDE.VelocityRegion d}
    (χ : PDE.ScalarField d) (hχ : ContDiff ℝ PDE.smoothOrder χ)
    (hχcompact : IsCompact (tsupport χ)) (hχO : tsupport χ ⊆ O)
    (R : ℝ) (hR : 0 < R)
    (k : Fin d → Fin (n + 1)) :
    ∃ ψ : PDE.WeakTestFunction O,
      (∀ y, ψ y = χ y *
        ∏ i : Fin d, (bernsteinPolynomial ℝ n (k i)).eval (((y i / R) + 1) / 2)) ∧
      tsupport (ψ : PDE.ScalarField d) ⊆ tsupport χ := by

  let p : PDE.ScalarField d := fun y =>
    ∏ i : Fin d, (bernsteinPolynomial ℝ n (k i)).eval (((y i / R) + 1) / 2)

  let ψ : PDE.WeakTestFunction O :=
    { toFun := fun y => χ y * p y
      contDiff := hχ.mul (by
          apply contDiff_prod
          intro i _

          simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
            Function.comp_def] using
            (Polynomial.contDiff_aeval (𝕜 := ℝ) (bernsteinPolynomial ℝ n (k i))
              (↑PDE.smoothOrder )).comp ((((contDiff_apply ℝ ℝ i).div_const R).add contDiff_const).div_const 2))
      hasCompactSupport :=
        IsCompact.of_isClosed_subset hχcompact (isClosed_tsupport _) tsupport_mul_subset_left
      tsupport_subset := tsupport_mul_subset_left.trans hχO }
  refine ⟨ψ, ?_, ?_⟩
  · intro y
    rfl
  · exact tsupport_mul_subset_left

end HypoellipticAleksandrov.Parabolic.Dirichlet
