module

public import NearlyMinimax.HighObservationKernel

@[expose] public section

/-! Original real-response kernel and likelihood integrals for the high prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The jointly Borel experiment on the original real observation space. -/
def highRealSampleKernel {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) : Kernel Ω (Fin n → Observation d) :=
  (highSampleIndexKernel n a V p F hp hF).map (encodeDesignResponse a)

theorem highRealSampleKernel_apply {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω) :
    highRealSampleKernel n a V p F hp hF ω =
      (highSampleIndexKernel n a V p F hp hF ω).map (encodeDesignResponse a) :=
  Kernel.map_apply _ (encodeDesignResponse_measurable a) ω

theorem highRealSampleKernel_markov {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    IsMarkovKernel (highRealSampleKernel n a V p F hp hF) := by
  let _ := highSampleIndexKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  exact Kernel.IsMarkovKernel.map _ (encodeDesignResponse_measurable a)

/-- Each fiber is the actual original-model sample law. -/
theorem highRealSampleKernel_eq_sampleLaw {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) (ω : Ω) :
    highRealSampleKernel n a V p F hp hF ω =
      sampleLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V hF.of_uncurry_left ha (hq ω)) n := by
  rw [highRealSampleKernel_apply]
  exact highSampleIndexKernel_encode n a V p F hp hF aRaw bRaw haRaw hraw ha hq ω

end NearlyMinimax
