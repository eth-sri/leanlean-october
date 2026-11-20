module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Finite-vector `L^p` convergence

This file turns coordinatewise `L^p` convergence of native vector fields into
`L^p` convergence of their explicit Euclidean magnitudes.  The finite
coordinate sum is used only as a convergence majorant; the resulting norm is
the exact Euclidean norm and carries no comparison constant.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

section
variable {α : Type*}

private theorem aestronglyMeasurable_vecEuclideanNorm_of_coord' [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {F : α → Vec d}
    (hF : ∀ i, AEStronglyMeasurable (fun x => F x i) μ) :
    AEStronglyMeasurable (fun x => vecEuclideanNorm (F x)) μ := by
  rw [show (fun x => vecEuclideanNorm (F x)) = fun x => Real.sqrt (∑ i, (F x i) ^ 2) from
    funext fun x => by rw [vecEuclideanNorm, vecNormSq_eq_sum_sq]]
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  rw [← Finset.sum_fn]
  exact Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => show
    AEStronglyMeasurable ((fun x => F x i) ^ 2) μ from (hF i).pow 2)

/-- The Euclidean magnitude of a vector field is bounded in `Lᵖ` by the sum of
its coordinate seminorms. -/
theorem eLpNorm_vecEuclideanNorm_le_sum [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {F : α → Vec d} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hF : ∀ i, AEStronglyMeasurable (fun x => F x i) μ) :
    eLpNorm (fun x => vecEuclideanNorm (F x)) p μ ≤ ∑ i, eLpNorm (fun x => F x i) p μ := by
  calc
    _ ≤ eLpNorm (fun x => ∑ i, |F x i|) p μ := by
      apply eLpNorm_mono (aestronglyMeasurable_vecEuclideanNorm_of_coord' hF)
      intro x
      have hsum : 0 ≤ ∑ i, |F x i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _), abs_of_nonneg hsum] using vecEuclideanNorm_le_sum_abs (F x)
    _ ≤ ∑ i, eLpNorm (fun x => |F x i|) p μ := by
      rw [← Finset.sum_fn]
      exact eLpNorm_sum_le hp
    _ = _ := Finset.sum_congr rfl fun i _ => eLpNorm_norm (fun x => F x i) (hF i)

/-- Coordinatewise `L^p` convergence of native vector fields implies
`L^p` convergence of their explicit Euclidean difference. -/
theorem tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {p : ℝ≥0∞}
    {F : ℕ → α → Vec d} {G : α → Vec d}
    (hp : 1 ≤ p)
    (hMeas :
      ∀ n i,
        AEStronglyMeasurable
          (fun x => F n x i - G x i) μ)
    (hCoordinate :
      ∀ i,
        Filter.Tendsto
          (fun n =>
            eLpNorm (fun x => F n x i - G x i) p μ)
          Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n =>
        eLpNorm
          (fun x => vecEuclideanNorm (F n x - G x))
          p μ)
      Filter.atTop (nhds 0) := by
  have hsum := tendsto_finsetSum Finset.univ (fun (i : Fin d) _ => hCoordinate i)
  rw [Finset.sum_const_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => eLpNorm_vecEuclideanNorm_le_sum (F := fun x => F n x - G x) hp (hMeas n))

end

end PDE
