module
public import TaoTrudgianYang2025.ExponentPairLowFrequencyCore
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-! Closed-source first-derivative estimate, retaining all boundary terms. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

def modelPhaseFirstDerivativeConstant (σ : ℝ) : ℝ :=
  2/(2 : ℝ)^(-σ)+3

theorem modelPhaseFirstDerivativeConstant_pos (σ : ℝ) :
    0 < modelPhaseFirstDerivativeConstant σ := by
  unfold modelPhaseFirstDerivativeConstant
  positivity

theorem norm_exponentialSumAt_le_firstDerivative
    {σ δ T N : ℝ} {F : ℝ → ℝ} {a b : ℕ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (hslope : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hcurv : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hscale : T ≤ N/4) :
    ‖exponentialSumAt F T N a b‖ ≤ modelPhaseFirstDerivativeConstant σ*(N/T) := by
  have hratio : 1 ≤ N/T := (le_div_iff₀ hT).mpr (by linarith)
  let K : ℝ := 2/(2 : ℝ)^(-σ)
  pm_64 hK K
  change ‖exponentialSumAt F T N a b‖ ≤ (K+3)*(N/T)
  by_cases hlong : a+3 ≤ b
  · obtain ⟨L,hL⟩ := Nat.exists_eq_add_of_le hlong
    pm_472
    have hcore := norm_modelPhaseCore_le_firstDerivative (A := (a : ℝ)+1) (L := L)
      hσ hT hN hslope hcurv hF (by linarith) (by linarith) hscale
    pm_173
  pm_361

end TaoTrudgianYang2025
