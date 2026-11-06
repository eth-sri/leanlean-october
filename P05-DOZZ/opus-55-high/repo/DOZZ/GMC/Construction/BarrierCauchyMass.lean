/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyEstimates
public import DOZZ.Statements.GMC.RegularizedLogChaosTestMass

/-! Growing-barrier good masses for arbitrary compatible admissible regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The thick-point event through log scale `r`: every integer coarse field scale between `k₀`
and the current cutoff scale stays below the linear barrier. -/
def admissibleGrowingBarrierSet {Ω : Type*}
    (Y : Ω → ℝ → ℂ → ℝ) (a : ℝ) (k₀ : ℕ) (r : ℝ) : Set (Ω × ℂ) :=
  {q | ∀ k : ℕ, k₀ ≤ k → (k : ℝ) ≤ r →
    Y q.1 (Real.exp (-(k : ℝ))) q.2 ≤ a * (k : ℝ)}
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ) (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
include hY

/-- The growing-barrier event is jointly measurable in the sample and spatial point. -/
theorem admissibleGrowingBarrierSet_measurable
    (a : ℝ) (k₀ : ℕ) (r : ℝ) :
    MeasurableSet (admissibleGrowingBarrierSet Y a k₀ r) := by
  let B : ℕ → Set (Ω × ℂ) := fun k =>
    if hk : k₀ ≤ k ∧ k ≤ r then
      {q | Y q.1 (Real.exp (-k)) q.2 ≤ a * k}
    else Set.univ
  have hEq : admissibleGrowingBarrierSet Y a k₀ r = ⋂ k, B k := by
    aesop
  rw [hEq]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : k₀ ≤ k ∧ (k : ℝ) ≤ r
  · have hset : MeasurableSet
        {q : Ω × ℂ | Y q.1 (Real.exp (-(k : ℝ))) q.2 ≤ a * (k : ℝ)} :=
      measurableSet_le (hY.measurableAtScale (Real.exp (-(k : ℝ)))) measurable_const
    aesop
  · simp [B, hk]

/-- Every admissible Gaussian regularization is defined over a probability measure. -/
theorem admissibleLogRegularization_isProbabilityMeasure
    :
    IsProbabilityMeasure P := by
  let q : Fin 1 → ℝ × ℂ := fun _ => (ε₀ / 2, 0)
  have hq : ∀ i, 0 < (q i).1 ∧ (q i).1 ≤ ε₀ := by
    intro i
    simp only [q]
    constructor <;> linarith [hY.cutoffPositive]
  exact (hY.gaussian 1 q hq).1

end

/-- At each regularization scale, the variance is measurable in the spatial coordinate. -/
theorem admissibleLogRegularization_variance_measurable
    [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (ε : ℝ) :
    Measurable (fun x => gaussianVariance P (fun ω => Y ω ε x)) := by
  have hswap :=
    (hY.measurableAtScale ε).comp measurable_swap
  have hvar : Measurable (fun x : ℂ => ∫ ω, Y ω ε x ^ 2 ∂P) :=
    (hswap.pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  have heq : (fun x : ℂ => gaussianVariance P (fun ω => Y ω ε x)) =
      fun x => ∫ ω, Y ω ε x ^ 2 ∂P := by
    funext x
    simp [gaussianVariance, gaussianCovariance, pow_two]
  simp_all

end

end DOZZ.Proofs
