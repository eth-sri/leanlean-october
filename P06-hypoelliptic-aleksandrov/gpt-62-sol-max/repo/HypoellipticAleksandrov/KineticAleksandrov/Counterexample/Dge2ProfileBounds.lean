module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileConstruction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry

/-! # Compact gauge-shell comparison for the actual homogeneous profile -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The actual profile is quantitatively comparable with the source kinetic gauge power. -/
theorem geometricProfile_comparison {d : ℕ} (alpha C₀ sigma R : ℝ) (ha : 0 < alpha)
    (hC₀ : 0 ≤ C₀) (hsigma : 0 < sigma) (hR : 0 < R) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q : XV d,
      c * Real.rpow (rho q) alpha ≤ geometricProfile alpha C₀ sigma R q ∧
      geometricProfile alpha C₀ sigma R q ≤ C * Real.rpow (rho q) alpha := by
  apply homogeneous_profile_comparison alpha ha (geometricProfile alpha C₀ sigma R)
    (geometricProfile_zero d alpha C₀ sigma R ha)
    (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR).continuousOn
    (geometricProfile_pos alpha C₀ sigma R hC₀ hsigma hR)
  exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
