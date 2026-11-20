module

public import NearlyMinimax.HighRawObservable


@[expose] public section

/-! Genuine variance-path derivatives of bounded raw data observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

variable {d n : ℕ} {s : Set ℝ} {a v η t T P B : ℝ} (ha : 0 < a)
include ha

/-- Density-weighted raw likelihood and velocity share a single integrable majorant
at each order, uniformly on any time set where the ternary masses are nonnegative. -/
theorem highObservableIntegrandPath (hP : 0 ≤ P)
    {p F : Covariate d → ℝ} (hp : Measurable p) (hF : Measurable F) (hpb : ∀ x, |p x| ≤ P)
    (hq : ∀ u ∈ s, ∀ x y, 0 ≤ ternaryMass a (F x) (v - η ^ 2 * u) y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    BoundedPath s (fun u z => H (encodeDesignResponse a z) * highRawSampleLikelihood a (v-η^2*u) p F z)
      (fun u z => H (encodeDesignResponse a z) * (-η^2 * highRawSampleVarianceDerivative a (v-η^2*u) p F z))
      (B * P ^ n) (B * (η ^ 2 * (P ^ n * (n / a ^ 2)))) := by
  apply BoundedPath.weight (hm := hH.comp (encodeDesignResponse_measurable a)) (hb := fun z => hHb _)
  refine ⟨⟨fun u => by fun_prop [highRawSampleLikelihood], fun u hu =>
    highRawSampleLikelihood_abs_le hP hpb ha.ne' (hq u hu)⟩,
    ⟨fun u => by fun_prop [highRawSampleVarianceDerivative], ?_⟩,
    fun z u _ => highRawSampleLikelihood_hasDerivAt_path ..⟩
  intro u hu z
  rw [abs_mul, abs_neg]
  bound [highRawSampleVarianceDerivative_abs_le ha hP hpb (hq u hu) z]

/-- Differentiating the real bounded data observable follows from the actual
finite ternary product derivative and a derived constant majorant. -/
theorem highRawObservable_hasDerivAt_path (ht : 0 < t) (htT : t < T) (hP : 0 ≤ P)
    {p F : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Ioo 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H)
    (hHb : ∀ z, |H z| ≤ B) (ω : Ω) :
    HasDerivAt (fun u => highRawObservable a (v - η ^ 2 * u) (p ω) (F ω) H)
      (-η ^ 2 * highRawObservableVarianceDerivative a (v - η ^ 2 * t) (p ω) (F ω) H) t := by
  have path := highObservableIntegrandPath ha hP hp.of_uncurry_left hF.of_uncurry_left (hpb ω)
    (fun u hu => hq u hu ω) hH hHb
  apply ((path.integral_deriv (highSampleReference d n) (Ioo_mem_nhds ht htT)).2).congr_deriv
  rw [highRawObservableVarianceDerivative, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by ring

end NearlyMinimax
