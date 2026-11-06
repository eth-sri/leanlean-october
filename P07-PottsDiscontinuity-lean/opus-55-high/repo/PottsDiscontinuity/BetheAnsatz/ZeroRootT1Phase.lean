module

public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# First derivative of the corrected T₁ phase

For an ordinary ML edge, the paired quotient is
`-exp(i(Θ(t,p)-Θ(0,p)))`. At the cyclic seam it has the additional exponent
`iNt`. This module records its derivative, including the seam contribution.
-/

@[expose] public noncomputable section

open Complex

namespace PottsDiscontinuity.BetheAnsatz

section
variable {N : ℕ} (Δ p : ℝ) (seam : Prop) [Decidable seam]
/-- The corrected real phase increment in the T₁ pair ratio. -/
def zeroRootPhaseExponent  : ℝ → ℝ :=
  (fun t => Bethe.theta Δ t p) - (fun _ => Bethe.theta Δ 0 p) +
    if seam then (fun t => (N : ℝ) * t) else 0

/-- The first-order coefficient of the corrected T₁ exponent. -/
def zeroRootPhaseDerivative  : ℝ :=
  deriv (fun t => Bethe.theta Δ t p) 0 + if seam then (N : ℝ) else 0
end

/-- The exponential of the corrected T₁ phase has derivative `i` times its real slope. -/
theorem hasDerivAt_zeroRootPhaseExp {N : ℕ} {c p : ℝ} (hc : 2 < c)
    (seam : Prop) [Decidable seam] :
    HasDerivAt
      (fun t : ℝ => Complex.exp
        (I * (zeroRootPhaseExponent (N := N) (anisotropy c) p seam t : ℂ)))
      (I * (zeroRootPhaseDerivative (N := N) (anisotropy c) p seam : ℂ)) 0 := by
  have hθ := (Bethe.analyticAt_theta_left (anisotropy_lt_neg_one hc) 0 p).differentiableAt.hasDerivAt.sub_const
    (Bethe.theta (anisotropy c) 0 p)
  have hδC : HasDerivAt
      (fun t : ℝ => (zeroRootPhaseExponent (N := N) (anisotropy c) p seam t : ℂ))
      (zeroRootPhaseDerivative (N := N) (anisotropy c) p seam : ℂ) 0 := by
    by_cases hs : seam
    · convert (hθ.add ((hasDerivAt_id (0 : ℝ)).const_mul (N : ℝ))).ofReal_comp using 1
      · ext t
        simp [zeroRootPhaseExponent, hs, mul_comm]
      simp [zeroRootPhaseDerivative, hs]
    simpa [zeroRootPhaseExponent, zeroRootPhaseDerivative, hs] using hθ.ofReal_comp
  have hδ0 : zeroRootPhaseExponent (N := N) (anisotropy c) p seam 0 = 0 := by
    by_cases hs : seam <;> simp [zeroRootPhaseExponent, hs]
  simpa [hδ0] using (hδC.const_mul I).cexp

end PottsDiscontinuity.BetheAnsatz
