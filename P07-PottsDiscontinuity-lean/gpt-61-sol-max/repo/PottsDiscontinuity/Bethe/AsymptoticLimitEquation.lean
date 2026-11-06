module
public import Mathlib

public import PottsDiscontinuity.Bethe.AsymptoticLimitTools
public import PottsDiscontinuity.Bethe.Prop21Tau

/-! # Identification of the limiting offset equation -/

@[expose] public section

open Set Filter MeasureTheory


namespace PottsDiscontinuity.Bethe

/-- Uniqueness for a scalar multiple of (cOE), including the homogeneous
case. Adding `(1-r)τ` avoids dividing by `r`. -/
theorem eq_mul_tauCont_of_scaled_cOE {Δ r : ℝ} (hΔ : Δ < -1)
    {g : ℝ → ℝ} (hg : Continuous g)
    (heq : ∀ x ∈ Icc (-Real.pi) Real.pi,
      2 * Real.pi * g x = r * (theta Δ x (-Real.pi) + theta Δ x Real.pi) / 2 -
        ∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y * g y) :
    ∀ x ∈ Icc (-Real.pi) Real.pi, g x = r * tauCont Δ x := by
  let h  := fun x => g x + (1 - r) * tauCont Δ x
  
  have hcoe : IsCOESolution Δ h := by
    intro x hx
    
    have hgi : IntervalIntegrable (fun y => d2Theta Δ x y * g y) volume (-Real.pi) Real.pi :=
      (((continuous_d2Theta_pair hΔ).comp (continuous_const.prodMk continuous_id)).mul hg).intervalIntegrable (-Real.pi) Real.pi
    have hτi : IntervalIntegrable (fun y => d2Theta Δ x y * tauCont Δ y) volume (-Real.pi) Real.pi :=
      (((continuous_d2Theta_pair hΔ).comp (continuous_const.prodMk continuous_id)).mul (continuous_tauCont hΔ)).intervalIntegrable (-Real.pi) Real.pi
    have hτ := tauCont_isCOESolution hΔ x hx
    unfold cOEop at hτ ⊢
    
    
    rw [(by
           funext y
           
           ring : (fun y => d2Theta Δ x y * h y) =
        fun y => d2Theta Δ x y * g y + (1 - r) * (d2Theta Δ x y * tauCont Δ y)), intervalIntegral.integral_add hgi (hτi.const_mul (1 - r)),
      intervalIntegral.integral_const_mul]
    
    nlinarith only [heq x hx,  congrArg (fun z  => (1 - r) * z) hτ ]
  
  intro x hx
  have hi := (eq_tauCont_of_isCOESolution_of_integrableOn hΔ
                (integrableOn_Icc_of_continuous (hg.add ((continuous_tauCont hΔ).const_mul (1 - r)))) hcoe) x hx
  dsimp  at hi
  nlinarith only [hi]

end PottsDiscontinuity.Bethe
