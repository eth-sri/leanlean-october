module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaBufferedUniformError
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# A global sharp-source comparison with arbitrary positive power error

Long intervals retain the actual interior stationary integers. In the
short branch the retained set is empty and the ORIGINAL source sum is
bounded by its genuine interval cardinality. This is an error-paid branch,
not a replacement of the phase or source by a constant.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem one_add_log_add_one_le_rpow {T ε : ℝ} (hT : 1 ≤ T) (hε : 0 < ε) :
    1+Real.log (T+1) ≤ (1+(2 : ℝ)^ε/ε)*T^ε := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  pm_153 hp T ε hT hε.le
  have hlog := Real.log_le_rpow_div (show 0 ≤ T+1 by linarith) hε
  have hpow := Real.rpow_le_rpow (show 0 ≤ T+1 by linarith)
    (show T+1 ≤ 2*T by linarith) hε.le
  pm_5164 hTpos.le hpow
  have hd := div_le_div_of_nonneg_right hpow hε.le
  grind

theorem modelPhase_buffered_source_power_error
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N T : ℝ) (a b : ℕ),
      1 ≤ N → 1 ≤ T → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N →
      ∀ (F : ℝ → ℝ) (δ : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        ‖exponentialSumAt F T N a b-
          (∑ q ∈ Finset.Ioo
            (modelPhaseBufferedPlateauLower F ((b : ℝ)/N) ((Real.sqrt T)⁻¹) T N)
            (modelPhaseBufferedPlateauUpper F ((a : ℝ)/N) ((Real.sqrt T)⁻¹) T N),
            modelPhaseStationaryMainTerm F T N q)‖ ≤
          C*(N/Real.sqrt T+T^ε) := by
  obtain ⟨M,hM,hsource⟩ := modelPhase_buffered_source_uniform_error hσ
  let K := 1+(2 : ℝ)^ε/ε
  have hK : 1 ≤ K := by
    have h : 0 ≤ (2 : ℝ)^ε/ε := by positivity
    dsimp [K]
    linarith
  refine ⟨M*K,by nlinarith,?_⟩
  intro N T a b hN hT ha hb hflat F δ hδ hF
  have h := hsource N T a b hN hT ha hb hflat F δ hδ hF
  pm_1357
  have hlog := one_add_log_add_one_le_rpow hT hε
  have hleft : N/Real.sqrt T ≤ K*(N/Real.sqrt T) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hx
  apply h.trans
  calc
    M*(N/Real.sqrt T+1+Real.log (T+1)) =
        M*(N/Real.sqrt T+(1+Real.log (T+1))) := by ring
    _ ≤ M*(K*(N/Real.sqrt T)+K*T^ε) :=
      mul_le_mul_of_nonneg_left (add_le_add hleft hlog) (zero_le_one.trans hM)
    _ = _ := by ring

def modelPhaseSharpStationarySet (F : ℝ → ℝ) (T N : ℝ) (a b : ℕ) : Finset ℤ := by
  classical
  exact if (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N then
    Finset.Ioo
      (modelPhaseBufferedPlateauLower F ((b : ℝ)/N) ((Real.sqrt T)⁻¹) T N)
      (modelPhaseBufferedPlateauUpper F ((a : ℝ)/N) ((Real.sqrt T)⁻¹) T N)
  else ∅

section
variable {F : ℝ → ℝ} {T N : ℝ} {a b : ℕ}
include F T N a b
theorem modelPhaseSharpStationarySet_of_long
    (hlong : (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N) :
    modelPhaseSharpStationarySet F T N a b =
      Finset.Ioo
        (modelPhaseBufferedPlateauLower F ((b : ℝ)/N) ((Real.sqrt T)⁻¹) T N)
        (modelPhaseBufferedPlateauUpper F ((a : ℝ)/N) ((Real.sqrt T)⁻¹) T N) := by
  simp only [modelPhaseSharpStationarySet,ite_eq_left hlong]

theorem modelPhaseSharpStationarySet_of_short
    (hshort : (b : ℝ)/N ≤ (a : ℝ)/N+4*(Real.sqrt T)⁻¹) :
    modelPhaseSharpStationarySet F T N a b = ∅ := by
  simp only [modelPhaseSharpStationarySet,ite_eq_right (not_lt.mpr hshort)]
end

theorem modelPhase_source_sharp_comparison
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N T : ℝ) (a b : ℕ),
      1 ≤ N → 1 ≤ T → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        ‖exponentialSumAt F T N a b-
          (∑ q ∈ modelPhaseSharpStationarySet F T N a b,
            modelPhaseStationaryMainTerm F T N q)‖ ≤ C*(N/Real.sqrt T+T^ε) := by
  pm_69 M hM hsource modelPhase_buffered_source_power_error hσ hε
  refine ⟨max M 5,hM.trans (le_max_left _ _),?_⟩
  intro N T a b hN hT ha hb F δ hδ hF
  pm_1610 hNpos N hN hTpos T hT
  pm_1357
  pm_153 hp T ε hT hε.le
  pm_1651
  · rw [modelPhaseSharpStationarySet_of_long hlong]
    exact (hsource N T a b hN hT ha hb hlong F δ hδ hF).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hshort := le_of_not_gt hlong
    rw [modelPhaseSharpStationarySet_of_short hshort,Finset.sum_empty,sub_zero]
    have hs := norm_exponentialSumAt_le_buffered_short hNpos
      (show 0 ≤ (Real.sqrt T)⁻¹ by positivity) F T a b hshort
    calc
      _ ≤ 4*(N/Real.sqrt T)+1 := hs.trans_eq (by ring)
      _ ≤ 5*(N/Real.sqrt T+T^ε) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end TaoTrudgianYang2025
