/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GaussianVariance

/-! The definition `DOZZ.IsGaussianL2Limit`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- `L` belongs to the Gaussian `L²(P)` closure of the real test evaluations of `X`.
See [KRV, Theorem 12.1]. -/
def IsGaussianL2Limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (L : Ω → ℝ) : Prop :=
  MemLp L 2 P ∧
    ∃ f : ℕ → TestFn,
      Tendsto (fun n => eLpNorm (fun ω => L ω - X ω (f n)) 2 P) atTop (𝓝 0)

namespace Proofs

/-- Gaussian `L²` limits of test evaluations are closed under scaling. -/
theorem IsGaussianL2Limit.const_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Distr} {L : Ω → ℝ} (hL : IsGaussianL2Limit P X L) (c : ℝ) :
    IsGaussianL2Limit P X (fun ω => c * L ω) := by
  obtain ⟨hLm, f, hf⟩ := hL
  refine ⟨hLm.const_mul c, fun n => c • f n, ?_⟩
  have he (n : ℕ) : (fun ω => c * L ω - X ω (c • f n)) = c • (fun ω => L ω - X ω (f n)) := by
    funext ω
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [he, eLpNorm_const_smul, mul_zero] using ENNReal.Tendsto.const_mul hf (Or.inr enorm_ne_top)

end Proofs

end DOZZ
