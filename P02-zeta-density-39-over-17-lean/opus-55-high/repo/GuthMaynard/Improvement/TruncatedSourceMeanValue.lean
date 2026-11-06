module
public import GuthMaynard.Improvement.TruncatedSourceAttachment
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Literal fixed-cutoff truncated mass, uniformly in the real truncation level. -/
theorem fixed_truncated_source_mass {N T : ℝ} (hN : 2 ≤ N) (hNT : N ≤ T)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) (U : ℝ) :
    (∫ t, sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T))
      (boundedPolynomial N a) U t) ≤ 612*T*N*Real.log (2*N) := by
  have hT : 0 < T := by linarith
  pm_5702
  obtain ⟨_,hi,_,_,hs,hdom⟩ := fixed_truncated_source_regular hN hT a ha U
  have hz : ∀ t ∉ Icc (-2*T) (3*T), μ t=0 := by
    pm_8234 hm
  have hp : IntegrableOn (fun t => ‖boundedPolynomial N a t‖^2) (Icc (-2*T) (3*T)) :=
    ((boundedPolynomial_regular N a).1.norm.pow 2).integrableOn_Icc
  have hmass : (∫ t, μ t) ≤
      (5*T+4*(⌊2*N⌋₊:ℝ)*(1+Real.log (⌊2*N⌋₊:ℝ)))*(N+1) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    calc
      _ ≤ ∫ t in Icc (-2*T) (3*T), ‖boundedPolynomial N a t‖^2 :=
        setIntegral_mono_on hi.integrableOn hp measurableSet_Icc
          (fun t _ => (hdom t).trans (min_le_left _ _))
      _ ≤ _ := by
        convert boundedPolynomial_mean_value (by linarith : 0 < N) a ha
          (show -2*T ≤ 3*T by linarith) using 1; ring
  pm_4553
  have hscalar := separated_second_moment_scalar hN (show 0 ≤ 5*T by positivity)
  have hmass0 : 0 ≤ ∫ t, μ t := MeasureTheory.integral_nonneg
    (fun t => (fixed_truncated_source_regular hN hT a ha U).2.2.2.1 t)
  have hraw : (∫ t, μ t) ≤ 102*N*(5*T+N*Real.log (2*N)) := by
    nlinarith
  pm_6303
  have ht := mul_le_mul_of_nonneg_left hlog hT.le
  have hb : 5*T+N*Real.log (2*N) ≤ 6*T*Real.log (2*N) := by linarith
  exact hraw.trans (by nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 102*N by positivity)])

end GuthMaynard.Improvement
