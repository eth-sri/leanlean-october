module
public import TaoTrudgianYang2025.BetaFiniteSum
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-! Uniform second-derivative bound for the actual closed-interval
ANTEDB model-phase sum, including all endpoints. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

def modelPhaseSumConstant (σ : ℝ) : ℝ :=
  betaBProcessConstant (2*Real.pi*modelPhaseCurvatureLower σ)
    (2*Real.pi*(σ+1))+3

theorem modelPhaseSumConstant_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < modelPhaseSumConstant σ := by
  have hc : 0 < 2*Real.pi*modelPhaseCurvatureLower σ :=
    mul_pos (by positivity) (modelPhaseCurvatureLower_pos hσ)
  have hC : 0 ≤ 2*Real.pi*(σ+1) := by positivity
  have hk := betaBProcessConstant_pos hc hC
  unfold modelPhaseSumConstant
  linarith

theorem norm_exponentialSumAt_le_secondDerivative
    {σ δ T N : ℝ} {F : ℝ → ℝ} {a b : ℕ}
    (hσ : 0 < σ) (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hscale : T ≤ N^2) :
    ‖exponentialSumAt F T N a b‖ ≤
      modelPhaseSumConstant σ*(Real.sqrt T+N/Real.sqrt T) := by
  pm_1190 hTpos T hT hNpos N hN
  have hsqrt : 1 ≤ Real.sqrt T := by simp_all
  have hsum : 1 ≤ Real.sqrt T+N/Real.sqrt T := by
    have : 0 ≤ N/Real.sqrt T := by positivity
    linarith
  let K := betaBProcessConstant (2*Real.pi*modelPhaseCurvatureLower σ)
    (2*Real.pi*(σ+1))
  have hK : 0 < K := betaBProcessConstant_pos
    (mul_pos (by positivity) (modelPhaseCurvatureLower_pos hσ)) (by positivity)
  change ‖exponentialSumAt F T N a b‖ ≤
    (K+3)*(Real.sqrt T+N/Real.sqrt T)
  by_cases hlong : a+3 ≤ b
  · obtain ⟨L,hL⟩ := Nat.exists_eq_add_of_le hlong
    pm_472
    have hcore := norm_modelPhaseCore_le (A := (a : ℝ)+1) (L := L)
      hσ hTpos hNpos hδ hF (by linarith) (by linarith)
      (by linarith) hscale
    pm_173
  pm_361

end TaoTrudgianYang2025
