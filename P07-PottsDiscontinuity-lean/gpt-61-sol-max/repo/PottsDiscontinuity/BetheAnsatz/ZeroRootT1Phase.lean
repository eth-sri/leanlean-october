module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# First derivative of the corrected T₁ phase

For an ordinary ML edge, the paired quotient is
`-exp(i(Θ(t,p)-Θ(0,p)))`. At the cyclic seam it has the additional exponent
`iNt`. This module records its derivative, including the seam contribution.
-/

@[expose] public section

open Complex

namespace PottsDiscontinuity.BetheAnsatz

/-- The corrected real phase increment in the T₁ pair ratio. -/
noncomputable def zeroRootPhaseExponent {N : ℕ} (Δ p : ℝ) (seam : Prop)
    [Decidable seam] : ℝ → ℝ :=
  (fun t => Bethe.theta Δ t p) - (fun _ => Bethe.theta Δ 0 p) +
    if seam then  fun t => (N : ℝ) * t  else 0

/-- The first-order coefficient of the corrected T₁ exponent. -/
noncomputable def zeroRootPhaseDerivative {N : ℕ} (Δ p : ℝ) (seam : Prop)
    [Decidable seam]  :=
  deriv (fun t => Bethe.theta Δ t p) 0 + if seam then (N : ℝ) else 0

/-- The exponential of the corrected T₁ phase has derivative `i` times its real slope. -/
theorem hasDerivAt_zeroRootPhaseExp {N : ℕ} {c p : ℝ} (hc : 2 < c)
    (seam : Prop) [Decidable seam] :
    HasDerivAt
      (fun t : ℝ => Complex.exp
        (I * (zeroRootPhaseExponent (N := N) (anisotropy c) p seam t : ℂ)))
      (I * (zeroRootPhaseDerivative (N := N) (anisotropy c) p seam : ℂ)) 0 := by
  let θ  := fun t => Bethe.theta (anisotropy c) t p
  
  
  
  have hshiftC := (((Bethe.analyticAt_theta_left (anisotropy_lt_neg_one hc) 0 p).differentiableAt.hasDerivAt).sub_const (θ 0)).ofReal_comp
  have htime : HasDerivAt (fun t  => (N : ℝ) * t) N 0 := by
    simpa  using (hasDerivAt_id  0 ).const_mul (N : ℝ)
  have htimeC := htime.ofReal_comp
  have hδC : HasDerivAt
      (fun t  => (zeroRootPhaseExponent (N := N) (anisotropy c) p seam t : ℂ))
      (zeroRootPhaseDerivative (N := N) (anisotropy c) p seam ) 0 := by
    by_cases hs : seam
    · 
      convert (hshiftC.add htimeC) using 1
      · ext t
        simp [zeroRootPhaseExponent, θ, hs]
      · simp [zeroRootPhaseDerivative, hs]
    · simp_all [zeroRootPhaseExponent, zeroRootPhaseDerivative]
  
  
  
  
  have hcomp := HasDerivAt.comp_of_eq  0  (Complex.hasDerivAt_exp 0)  (hδC.const_mul I)  (by simp [(by
                                                                                                       by_cases hs : seam <;> simp [zeroRootPhaseExponent, hs] : zeroRootPhaseExponent (N := N) (anisotropy c) p seam 0 = 0)])
  simpa only [Function.comp_def, Complex.exp_zero, one_mul] using hcomp

end PottsDiscontinuity.BetheAnsatz
