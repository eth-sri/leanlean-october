module

public import NearlyMinimax.HighMarginalScore
public import NearlyMinimax.MixtureRisk


@[expose] public section

/-! Actual tilted observable means are the means under the observed-data
mixture kernel, on the original real sample space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem highTiltedObservableMean_eq_dataMean {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    {n : ℕ} {a V aRaw bRaw B : ℝ} (ha : a ≠ 0) (haRaw : 0 < aRaw) (hB : 0 ≤ B)
    {p F : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    highTiltedObservableMean ν a V hp hF H =
      ∫ z, H z ∂(highRealSampleKernel n a V hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) := by
  have hb (ω)  :=
    highRawDensityMass_mem_Icc hp.of_uncurry_left haRaw
      (Eventually.of_forall (hraw ω))
  let _ := massPowerTilt_isProbability ν (highRawDensityMass_joint_measurable hp) n haRaw hb
  let _ := highRealSampleKernel_markov n a V hp hF haRaw hraw ha hq
  exact (probability_kernel_integral (by
    apply Integrable.of_bound hH.aestronglyMeasurable B
    solve_by_elim [Eventually.of_forall])).symm

end NearlyMinimax
