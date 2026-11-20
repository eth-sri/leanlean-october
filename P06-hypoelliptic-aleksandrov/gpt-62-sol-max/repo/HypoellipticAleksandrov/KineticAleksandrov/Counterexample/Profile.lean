module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Explicit profile statements for Appendix C

These are named conditional statements.
They state the profile construction's conclusions; definitions do not prove existence.
The classical branch deliberately has no distributional conclusion at the origin.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory
open scoped MatrixOrder

/-- The dimension-at-least-two profile statement. -/
def CounterProfileGeTwoStatement (d : ℕ) (alpha : ℝ) : Prop :=
  ∃ lam Lam c C : ℝ, ∃ A : XV d → PDE.Mat d, ∃ H : XV d → ℝ,
    0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
    (∀ i k, Measurable (fun q => A q i k)) ∧
    (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
    H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)) ∧
    (∀ q : XV d, q ≠ 0 → matrixContraction (A q) (dvv H q) =
      PDE.vecDot q.2 (dx H q)) ∧
    (∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (dv H q) ≤ C * Real.rpow (rho q) (alpha - 1))

/-- The literal autonomous scalar coefficient, including its specified axial values. -/
noncomputable def scalarProfileCoefficient (Lam : ℝ) (q : XV 1) : PDE.Mat 1 :=
  (if q.1 0 * q.2 0 < 0 then Lam else 1) • (1 : PDE.Mat 1)

/-- The analytic properties of a profile and its weak derivative representatives. -/
structure HasCounterProfile {d : ℕ} (alpha lam Lam c C : ℝ)
    (A : XV d → PDE.Mat d) (H : XV d → ℝ)
    (gx gv : XV d → PDE.Vec d) (hess : XV d → PDE.Mat d) : Prop where
  lower_pos : 0 < lam
  ellipticity_order : lam ≤ Lam
  comparison_lower_pos : 0 < c
  comparison_upper_pos : 0 < C
  measurable_matrix : ∀ i k, Measurable (fun q => A q i k)
  elliptic : ∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)
  continuous : Continuous H
  at_zero : H 0 = 0
  homogeneous : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q
  comparison : ∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧ H q ≤ C * Real.rpow (rho q) alpha
  measurable_position : Measurable gx
  measurable_velocity : Measurable gv
  measurable_hessian : ∀ i k, Measurable (fun q => hess q i k)
  ae_jets : ∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q
  ae_equation : ∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)
  gradient_bound : ∀ q : XV d, q ≠ 0 →
    PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)
  compact_jet_bound : ∀ K : Set (XV d), IsCompact K → 0 ∉ K →
    ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M
  position_locallyIntegrable : ∀ i, LocallyIntegrable (fun q => gx q i) volume
  velocity_locallyIntegrable : ∀ i, LocallyIntegrable (fun q => gv q i) volume
  hessian_locallyIntegrable : ∀ i k, LocallyIntegrable (fun q => hess q i k) volume
  weak_identities : ∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
    (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
    (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
    (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))
  ae_contDiff : ∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q

/-- The shared profile surface, with actual weak derivatives on the whole native carrier. -/
def CounterProfileStatement (d : ℕ) (alpha : ℝ) : Prop :=
  ∃ lam Lam c C : ℝ, ∃ A : XV d → PDE.Mat d, ∃ H : XV d → ℝ,
    ∃ gx gv : XV d → PDE.Vec d, ∃ hess : XV d → PDE.Mat d,
    HasCounterProfile alpha lam Lam c C A H gx gv hess

/-- A profile together with its ellipticity bounds, size estimates and weak jets. -/
structure CounterProfileData (d : ℕ) (alpha : ℝ) where
  lam : ℝ
  Lam : ℝ
  c : ℝ
  C : ℝ
  A : XV d → PDE.Mat d
  H : XV d → ℝ
  gx : XV d → PDE.Vec d
  gv : XV d → PDE.Vec d
  hess : XV d → PDE.Mat d
  spec : HasCounterProfile alpha lam Lam c C A H gx gv hess

noncomputable section

variable {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha)

/-- Choose all witnesses together, so every projection uses the same profile. -/
def selectProfile : CounterProfileData d alpha := Classical.choice <| by
  obtain ⟨lam, Lam, c, C, A, H, gx, gv, hess, hs⟩ := h
  exact ⟨⟨lam, Lam, c, C, A, H, gx, gv, hess, hs⟩⟩

abbrev profileLowerEllipticity := (selectProfile h).lam
abbrev profileUpperEllipticity := (selectProfile h).Lam
abbrev profileLowerComparison := (selectProfile h).c
abbrev profileUpperComparison := (selectProfile h).C
abbrev profileMatrix := (selectProfile h).A
abbrev profileFunction := (selectProfile h).H
abbrev profilePositionJet := (selectProfile h).gx
abbrev profileVelocityJet := (selectProfile h).gv
abbrev profileHessian := (selectProfile h).hess

theorem selectedProfile_spec :
    HasCounterProfile alpha (profileLowerEllipticity h) (profileUpperEllipticity h)
      (profileLowerComparison h) (profileUpperComparison h) (profileMatrix h) (profileFunction h)
      (profilePositionJet h) (profileVelocityJet h) (profileHessian h) :=
  (selectProfile h).spec

end
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
