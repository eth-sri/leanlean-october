module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp

/-! # Differentiating kinetic homogeneity -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The continuous linear map realizing kinetic dilation. -/
def dilationLinearMap (d : ℕ) (r : ℝ) : XV d →L[ℝ] XV d :=
  (r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
    (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))

section
variable {d : ℕ} (r : ℝ) (q : XV d)

/-- Kinetic dilation has its constant linear differential. -/
theorem hasFDerivAt_dilate :
    HasFDerivAt (dilate r : XV d → XV d) (dilationLinearMap d r) q :=
  (dilationLinearMap d r).hasFDerivAt

end

variable {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ) (hr : 0 < r)
    (hhom : ∀ q, H (dilate r q) = Real.rpow r alpha * H q) (q : XV d)
    (hq : DifferentiableAt ℝ H q) (hrq : DifferentiableAt ℝ H (dilate r q)) (i : Fin d)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
