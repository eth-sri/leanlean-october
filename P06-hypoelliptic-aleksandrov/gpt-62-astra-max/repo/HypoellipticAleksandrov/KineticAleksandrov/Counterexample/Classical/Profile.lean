module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry
import Mathlib.Tactic

/-! # The stationary supersolution needed for the counterexamples

Only a supersolution inequality is needed, and only away from the origin: the
classical test functions will already be flat in a neighborhood of the origin.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory
open scoped MatrixOrder ContDiff

structure ClassicalProfile (d : ℕ) (α : ℝ) where
  lam : ℝ
  Lam : ℝ
  A : XV d → PDE.Mat d
  H : XV d → ℝ
  hlam : 0 < lam
  ordered : lam ≤ Lam
  measurable : ∀ i j, Measurable fun q => A q i j
  elliptic : ∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)
  smooth : ContDiffOn ℝ ∞ H ({0}ᶜ : Set (XV d))
  positive : ∀ q ≠ 0, 0 < H q
  homogeneous : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = r^α * H q
  super : ∀ᵐ q ∂volume, 0 ≤ statOp A H q

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
