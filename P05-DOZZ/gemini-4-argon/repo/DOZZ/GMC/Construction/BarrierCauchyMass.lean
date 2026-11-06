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

/-- The growing-barrier event is jointly measurable in the sample and spatial point. -/
theorem admissibleGrowingBarrierSet_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) U (dens : ℂ → ℝ) ε₀
    Y
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    a k₀ r :
    MeasurableSet (admissibleGrowingBarrierSet Y a k₀ r) := by
  classical
  let B : ℕ → Set (Ω × ℂ) := fun k =>
    if hk : k₀ ≤ k ∧ (k : ℝ) ≤ r then
      {q | Y q.1 (Real.exp (-(k : ℝ))) q.2 ≤ a * (k : ℝ)}
    else Set.univ
  have hEq : admissibleGrowingBarrierSet Y a k₀ r = ⋂ k, B k := by
    ext q
    simp only [admissibleGrowingBarrierSet, Set.mem_iInter]
    constructor
    · intro h k
      by_cases hk : k₀ ≤ k ∧ (k : ℝ) ≤ r
      · simpa [B, hk] using h k hk.1 hk.2
      · simp [B, hk]
    · intro h k hk₀ hkr
      simpa [B, (⟨hk₀, hkr⟩ : k₀ ≤ k ∧ (k : ℝ) ≤ r)] using h k
  rw [hEq]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : k₀ ≤ k ∧ (k : ℝ) ≤ r
  · have hset : MeasurableSet
        {q : Ω × ℂ | Y q.1 (Real.exp (-(k : ℝ))) q.2 ≤ a * (k : ℝ)} :=
      measurableSet_le (hY.measurableAtScale (Real.exp (-(k : ℝ)))) measurable_const
    simpa [B, hk] using hset
  · simp [B, hk]

/-- Every admissible Gaussian regularization is defined over a probability measure. -/
theorem admissibleLogRegularization_isProbabilityMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) U (dens : ℂ → ℝ) ε₀
    Y
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) :
    IsProbabilityMeasure P := by
  let q : Fin 1 → ℝ × ℂ := fun _ => (ε₀ / 2, 0)
  exact (hY.gaussian 1 q (by intro i; simp only [q]; constructor <;> linarith [hY.cutoffPositive])).1

/-- At each regularization scale, the variance is measurable in the spatial coordinate. -/
theorem admissibleLogRegularization_variance_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    U (dens : ℂ → ℝ) ε₀
    Y
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) ε :
    Measurable (fun x => gaussianVariance P (fun ω => Y ω ε x)) := by
  rw [(show (fun x => gaussianVariance P (fun ω => Y ω ε x)) = fun x => ∫ ω, Y ω ε x ^ 2 ∂P by funext x; simp [gaussianVariance, gaussianCovariance, pow_two])]
  exact ((((hY.measurableAtScale ε).comp measurable_swap).pow_const 2).stronglyMeasurable.integral_prod_right.measurable)

end DOZZ.Proofs
