module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosComplementaryAlgebra
public import LaterPairs.Native.RobertSargosWideFrequencyBound
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                          

noncomputable section
namespace TaoTrudgianYang2025

section
variable (ε : ℝ) (hε : 0 < ε)
include ε hε
theorem exists_robertSargos_primitive_count_narrow_frequency :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → δ ∈ Set.Icc 0 1 → Q ≤ H →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*(R*H*Q)^(1+ε)*(1+δ*Q) := by
  pm_69 Cc hCc hconic exists_robertSargos_primitive_count_conic_weight ε hε
  pm_69 Cl hCl hlinear exists_robertSargos_primitive_count_linear_weight ε hε
  refine ⟨Cc*1000+Cl*7300,by positivity,?_⟩
  intro S R H Q δ hR hH hQ hδ hQH hmem
  have hδ0 : 0 ≤ δ := hδ.1
  pm_254 hHp H hR0 R
  have hQp : 0 < Q := by linarith
  pm_2534
  by_cases hs : δ ≤ R/H
  · have ha := robertSargos_conic_count_algebra hR hH hQ hδ0 hQH hs
    have hl := robertSargos_frequency_loss_algebra hR hH hQ hε.le
      (show 0 ≤ Q*(1+(δ*Q+99*R*Q/H))*(Q+8*H^2*δ) by positivity) ha
    calc
      _ ≤ Cc*Q^ε*Q*(1+(δ*Q+99*R*Q/H))*(Q+8*H^2*δ) :=
        hconic S R H Q δ hR0 hHp hQ hδ hmem
      _ = Cc*(Q^ε*(Q*(1+(δ*Q+99*R*Q/H))*(Q+8*H^2*δ))) := by ring
      _ ≤ Cc*(1000*(R*H*Q)^(1+ε)*(1+δ*Q)) := mul_le_mul_of_nonneg_left hl hCc.le
      _ = (Cc*1000)*((R*H*Q)^(1+ε)*(1+δ*Q)) := by ring
      _ ≤ (Cc*1000+Cl*7300)*((R*H*Q)^(1+ε)*(1+δ*Q)) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hCl]) hnonneg
      _ = _ := by ring
  · have ha := robertSargos_linear_count_algebra hR hH hQ hδ0 hQH (le_of_not_ge hs)
    have hl := robertSargos_frequency_loss_algebra hR hH hQ hε.le
      (show 0 ≤ Q*(1+(δ*Q+99*R*Q/H))*(Q+72*H*R) by positivity) ha
    calc
      _ ≤ Cl*Q^ε*Q*(1+(δ*Q+99*R*Q/H))*(Q+72*H*R) :=
        hlinear S R H Q δ hR0 hHp hQ hδ hmem
      _ = Cl*(Q^ε*(Q*(1+(δ*Q+99*R*Q/H))*(Q+72*H*R))) := by ring
      _ ≤ Cl*(7300*(R*H*Q)^(1+ε)*(1+δ*Q)) := mul_le_mul_of_nonneg_left hl hCl.le
      _ = (Cl*7300)*((R*H*Q)^(1+ε)*(1+δ*Q)) := by ring
      _ ≤ (Cc*1000+Cl*7300)*((R*H*Q)^(1+ε)*(1+δ*Q)) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hCc]) hnonneg
      _ = _ := by ring

theorem exists_robertSargos_primitive_count_small_tolerance :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → δ ∈ Set.Icc 0 1 → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*(R*H*Q)^(1+ε)*(1+δ*Q) := by
  pm_69 Cw hCw hw exists_robertSargos_primitive_count_wide_frequency ε hε
  pm_69 Cn hCn hn exists_robertSargos_primitive_count_narrow_frequency ε hε
  refine ⟨Cw+Cn,by positivity,?_⟩
  pm_1677
  have hδ0 : 0 ≤ δ := hδ.1
  pm_2534
  rcases le_total H Q with hHQ | hQH
  · calc
      _ ≤ Cw*(R*H*Q)^(1+ε)*(1+δ*Q) :=
        hw S R H Q δ hR hH hQ hδ0 hRH hHQ hmem
      _ ≤ (Cw+Cn)*((R*H*Q)^(1+ε)*(1+δ*Q)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith only [hCn]) hnonneg
      _ = _ := by ring
  · calc
      _ ≤ Cn*(R*H*Q)^(1+ε)*(1+δ*Q) :=
        hn S R H Q δ hR hH hQ hδ hQH hmem
      _ ≤ (Cw+Cn)*((R*H*Q)^(1+ε)*(1+δ*Q)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith only [hCw]) hnonneg
      _ = _ := by ring
end

end TaoTrudgianYang2025

