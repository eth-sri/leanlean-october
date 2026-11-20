/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyCompatibility
public import DOZZ.GMC.GoodBarrierL2Cauchy

/-! Growing-barrier tail bounds, their spatial integration, and the L² algebra criterion. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Countable version of the weighted union bound. It lets one sum all omitted integer
barriers even though the final cutoff only activates a finite initial segment. -/
theorem lintegral_mul_indicator_exists_le_tsum
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (w : Ω → ℝ≥0∞) (bad : ι → Ω → Prop)
    (hbadMeas : ∀ i, AEMeasurable (fun ω => w ω *
      Set.indicator {ω | bad i ω} (fun _ => (1 : ℝ≥0∞)) ω) P) :
    ∫⁻ ω, w ω * Set.indicator {ω | ∃ i, bad i ω}
        (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      ∑' i, ∫⁻ ω, w ω * Set.indicator {ω | bad i ω}
        (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
  calc
    ∫⁻ ω, w ω * Set.indicator {ω | ∃ i, bad i ω}
        (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      ∫⁻ ω, ∑' i, w ω * Set.indicator {ω | bad i ω}
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
            apply lintegral_mono
            intro ω
            by_cases hbad : ∃ i, bad i ω
            exact Exists.casesOn hbad fun i hi =>
              have hterm :=
                of_eq_true
                  (Eq.trans
                    (congrFun'
                      (congrArg Eq (Eq.trans (congrArg (HMul.hMul (w ω)) (indicator_of_mem hi fun x => 1)) (mul_one (w ω)))) (w ω))
                    (eq_self (w ω)));
              have hexists := Exists.intro i hi;
              Trans.trans
                (Trans.trans
                  (of_eq_true
                    (Eq.trans
                      (congrFun'
                        (congrArg Eq (Eq.trans (congrArg (HMul.hMul (w ω)) (indicator_of_mem hexists fun x => 1)) (mul_one (w ω))))
                        (w ω))
                      (eq_self (w ω))))
                  (Eq.symm hterm))
                (ENNReal.le_tsum i)
            · simp [hbad]
    _ = ∑' i, ∫⁻ ω, w ω * Set.indicator {ω | bad i ω}
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
            rw [lintegral_tsum hbadMeas]

section
variable (g a : ℝ) (hga : g < a)
include hga

/-- The mixed double-root barrier rate is summable over the coarse scales whenever the barrier
slope is strictly above the charge. -/
theorem summable_compatible_mixed_double_root_barrier_rate :
    Summable (fun k : ℕ => Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) := by
  let c  := (a - g) ^ 2 / 16
  have hc : 0 < c := by dsimp [c]; positivity
  have hfun : (fun k : ℕ => Real.exp (-c * (k : ℝ))) =
      fun k : ℕ => Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16)) := by
    funext k
    congr 1
    dsimp [c]
    ring
  rw [← hfun]
  exact summable_gaussian_barrier_tail c hc

/-- The integrated cost of all omitted integer barriers tends to zero as the finite truncation
level grows. -/
theorem tendsto_compatible_mixed_double_root_barrier_tail_sum :
    Tendsto
      (fun N : ℕ => ∑' k : ℕ,
        ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * ((k + N : ℕ) : ℝ) / 16))))
      atTop (𝓝 0) := by
  let c  := (a - g) ^ 2 / 16
  have hsummable : Summable (fun k : ℕ => Real.exp (-c * (k : ℝ))) := by
    have h := summable_compatible_mixed_double_root_barrier_rate g a hga
    apply h.congr
    intro k
    congr 1
    dsimp [c]
    ring
  let f : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.exp (-c * (k : ℝ)))
  have hfinite := hsummable.tsum_ofReal_ne_top
  have htail := ENNReal.tendsto_sum_nat_add f hfinite
  have hfun :
      (fun N : ℕ => ∑' k : ℕ,
        ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * ((k + N : ℕ) : ℝ) / 16)))) =
      fun N => ∑' k : ℕ, f (k + N) := by
    funext N
    apply tsum_congr
    intro k
    simp only [f]
    congr 1
    rw [Nat.cast_add]
    dsimp [c]
    ring_nf
  rwa [hfun]

end

end DOZZ.Proofs
