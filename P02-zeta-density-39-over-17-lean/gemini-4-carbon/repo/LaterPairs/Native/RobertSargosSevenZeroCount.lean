module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import MathCollab.Density.Stronger.Atkinson.ZetaBandSecondDerivatives
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative
public import MathCollab.Density.Stronger.Atkinson.FresnelEvaluation
public import MathCollab.Density.Stronger.Atkinson.ContinuousKernelPrimitive
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.SecondDerivativeComposition
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges
public import MathCollab.Density.Stronger.Fourth.SquareTail
public import LaterPairs.Native.RobertSargosZeroFibers

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                        

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_seven_zero_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosSevenPoint) (R H Q N δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 1 ≤ N →
      (∀ p ∈ S, RobertSargosSevenSystem R H Q N δ p) →
      (∀ p ∈ S, p.n₁ = p.n₂) →
      (S.card:ℝ) ≤ C*(R*N*H*Q)^(1+ε) := by
  classical
  obtain ⟨C,hC,hfiber⟩ := exists_robertSargos_zero_fiber_bound ε hε
  refine ⟨30*C*(4:ℝ)^ε,by positivity,?_⟩
  intro S R H Q N δ hR hH hQ hN hmem hzero
  have hRp : 0 < R := by linarith
  have hHp : 0 < H := by linarith
  have hQp : 0 < Q := by linarith
  have hNp : 0 < N := by linarith
  have hB : 0 < R*N*H*Q := by positivity
  let U := S.image robertSargosZeroKey
  have hU : (U.card:ℝ) ≤ 30*(R*N*H*Q) := by
    exact (robertSargos_zero_image_card_le S hR hH hQ hN hmem).trans_eq (by ring)
  have hmaps : Set.MapsTo robertSargosZeroKey S U := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcardR : (S.card:ℝ) =
      ∑ z ∈ U, ((S.filter (fun p => robertSargosZeroKey p = z)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hf : ∀ z : (ℤ × ℤ × ℤ) × ℤ,
      ((S.filter (fun p => robertSargosZeroKey p = z)).card:ℝ) ≤ C*(4*H*Q)^ε := by
    intro z
    exact hfiber _ R H Q N δ z hHp hQp
      (fun p hp => hmem p (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun p hp => hzero p (Finset.mem_filter.mp hp).1)
  have hHQ : H*Q ≤ R*N*H*Q := by
    have hm := mul_le_mul_of_nonneg_right
      (one_le_mul_of_one_le_of_one_le hR hN) (mul_nonneg hHp.le hQp.le)
    nlinarith
  have hpow : (4*H*Q)^ε ≤ (4:ℝ)^ε*(R*N*H*Q)^ε := by
    calc
      _ = (4:ℝ)^ε*(H*Q)^ε := by
        rw [mul_assoc,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hHQ hε.le) (by positivity)
  calc
    _ = _ := hcardR
    _ ≤ ∑ _z ∈ U, C*(4*H*Q)^ε := Finset.sum_le_sum (fun z _ => hf z)
    _ = (U.card:ℝ)*(C*(4*H*Q)^ε) := by
      simp
    _ ≤ (30*(R*N*H*Q))*(C*(4*H*Q)^ε) :=
      mul_le_mul_of_nonneg_right hU (by positivity)
    _ ≤ (30*(R*N*H*Q))*(C*((4:ℝ)^ε*(R*N*H*Q)^ε)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC.le) (by positivity)
    _ = _ := by rw [Real.rpow_add hB,Real.rpow_one]; ring

end TaoTrudgianYang2025

