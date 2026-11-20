module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPositive
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry
import Mathlib.Tactic

/-!
# Scalar kinetic gauge comparison

Continuity and strict positivity on the compact unit gauge shell give the two-sided bound.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set

/-- The actual reflected source profile is comparable with the literal native kinetic gauge. -/
theorem scalarProfile_comparison (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q : XV 1,
      c * Real.rpow (rho q) (3 * gamma.1) ≤ scalarProfile gamma Lam q ∧
      scalarProfile gamma Lam q ≤ C * Real.rpow (rho q) (3 * gamma.1) :=
  homogeneous_profile_comparison (3 * gamma.1) (mul_pos (by norm_num) gamma.2.1) (scalarProfile gamma Lam)
    (scalarProfile_zero gamma Lam) (scalarProfile_continuous gamma Lam hLam hmatch).continuousOn
    (scalarProfile_pos gamma Lam hLam hmatch) (scalarProfile_homogeneous gamma Lam)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
