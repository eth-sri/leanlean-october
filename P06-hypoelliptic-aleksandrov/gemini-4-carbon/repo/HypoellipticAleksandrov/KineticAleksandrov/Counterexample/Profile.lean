module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory
open scoped MatrixOrder

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

noncomputable def scalarProfileCoefficient (Lam : ℝ) (q : XV 1) : PDE.Mat 1 :=
  (if q.1 0 * q.2 0 < 0 then Lam else 1) • (1 : PDE.Mat 1)

def CounterProfileOneStatement (alpha : ℝ) : Prop :=
  ∃ Lam c C : ℝ, ∃ H : XV 1 → ℝ,
    ∃ gx gv : XV 1 → PDE.Vec 1, ∃ hess : XV 1 → PDE.Mat 1,
    1 < Lam ∧ 0 < c ∧ 0 < C ∧ Continuous H ∧ H 0 = 0 ∧
    (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
    (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha) ∧
    Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
    (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
    (∀ᵐ q ∂volume, matrixContraction (scalarProfileCoefficient Lam q) (hess q) =
      PDE.vecDot q.2 (gx q)) ∧
    (∀ q : XV 1, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
    (∀ K : Set (XV 1), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
    (∀ r : ℝ, 0 < r → ∀ q,
      gx (dilate r q) = Real.rpow r (alpha - 3) • gx q ∧
      gv (dilate r q) = Real.rpow r (alpha - 1) • gv q ∧
      hess (dilate r q) = Real.rpow r (alpha - 2) • hess q) ∧
    (∀ test : XV 1 → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (0 : XV 1) ∉ tsupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
    ContDiffOn ℝ 2 H {q : XV 1 | q.1 0 ≠ 0}

abbrev IsCounterProfileWitness {d : ℕ} (alpha lam Lam c C : ℝ)
    (A : XV d → PDE.Mat d) (H : XV d → ℝ) (gx gv : XV d → PDE.Vec d)
    (hess : XV d → PDE.Mat d) : Prop :=
  0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
  (∀ i k, Measurable (fun q => A q i k)) ∧
  (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
  Continuous H ∧ H 0 = 0 ∧
  (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
  (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
    H q ≤ C * Real.rpow (rho q) alpha) ∧
  Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
  (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
  (∀ᵐ q ∂volume, matrixContraction (A q) (hess q) = PDE.vecDot q.2 (gx q)) ∧
  (∀ q : XV d, q ≠ 0 →
    PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) ∧
  (∀ K : Set (XV d), IsCompact K → 0 ∉ K →
    ∃ M : ℝ, ∀ q ∈ K, ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
  (∀ i, LocallyIntegrable (fun q => gx q i) volume) ∧
  (∀ i, LocallyIntegrable (fun q => gv q i) volume) ∧
  (∀ i k, LocallyIntegrable (fun q => hess q i k) volume) ∧
  (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
    (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
    (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
    (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
  (2 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) ∧
  (∀ᵐ q ∂volume, ContDiffAt ℝ 2 H q)

def CounterProfileStatement (d : ℕ) (alpha : ℝ) : Prop :=
  ∃ lam Lam c C : ℝ, ∃ A : XV d → PDE.Mat d, ∃ H : XV d → ℝ,
    ∃ gx gv : XV d → PDE.Vec d, ∃ hess : XV d → PDE.Mat d,
    IsCounterProfileWitness alpha lam Lam c C A H gx gv hess

noncomputable def profileLowerEllipticity {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : ℝ := h.choose

noncomputable def profileUpperEllipticity {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : ℝ := h.choose_spec.choose

noncomputable def profileLowerComparison {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : ℝ := h.choose_spec.choose_spec.choose

noncomputable def profileUpperComparison {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : ℝ := h.choose_spec.choose_spec.choose_spec.choose

noncomputable def profileMatrix {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → PDE.Mat d :=
  h.choose_spec.choose_spec.choose_spec.choose_spec.choose

noncomputable def profileFunction {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → ℝ :=
  h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

noncomputable def profilePositionJet {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → PDE.Vec d :=
  h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

noncomputable def profileVelocityJet {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → PDE.Vec d :=
  h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

noncomputable def profileHessian {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) : XV d → PDE.Mat d :=
  h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

theorem selectedProfile_spec {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha) :
    IsCounterProfileWitness alpha (profileLowerEllipticity h) (profileUpperEllipticity h)
      (profileLowerComparison h) (profileUpperComparison h) (profileMatrix h)
      (profileFunction h) (profilePositionJet h) (profileVelocityJet h) (profileHessian h) :=
  h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
