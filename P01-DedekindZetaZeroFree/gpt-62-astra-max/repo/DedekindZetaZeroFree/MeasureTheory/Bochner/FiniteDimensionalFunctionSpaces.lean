module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import DedekindZetaZeroFree.Algebra.LinearAlgebra.FunctionInterpolation

public section

noncomputable section

open scoped Classical Topology

namespace DedekindZetaZeroFree.FiniteFunctionSpaces

open MeasureTheory Filter

theorem integral_mem_finite_linear_image
    {X Y V : Type*} [MeasurableSpace X] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (μ : Measure X) (J : V →ₗ[ℂ] (Y → ℂ))
    (f : X → Y → ℂ) (hf : ∀ᵐ x ∂μ, f x ∈ J.range)
    (hi : ∀ y, Integrable (fun x => f x y) μ) :
    (fun y => ∫ x, f x y ∂μ) ∈ J.range := by
  let := Module.Finite.range J
  obtain ⟨n, p, b, hb⟩ := exists_finite_evaluation_interpolation J.range
  have he (y : Y) :
      (fun x => f x y) =ᵐ[μ] (fun x => ∑ i, f x (p i) * (b i).val y) := by
    filter_upwards [hf] with x hx
    exact hb ⟨f x, hx⟩ y
  have hrepr : (fun y => ∫ x, f x y ∂μ) =
      ∑ i, (∫ x, f x (p i) ∂μ) • (b i).val := by
    funext y
    rw [integral_congr_ae (he y), integral_finsetSum]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_mul_const _ _
    · intro i _
      exact (hi (p i)).mul_const _
  rw [hrepr]
  exact J.range.sum_mem (fun i _ => J.range.smul_mem _ (b i).property)

end DedekindZetaZeroFree.FiniteFunctionSpaces
