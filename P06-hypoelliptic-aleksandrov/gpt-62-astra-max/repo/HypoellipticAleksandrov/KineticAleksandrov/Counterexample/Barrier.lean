module

public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.Analysis.EuclideanNormCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Trace bound for the quadratic velocity barrier

The Loewner bound controls the operator on the velocity quadratic.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open HypoellipticAleksandrov.Parabolic
open scoped BigOperators MatrixOrder

/-- Loewner lower control implies the dimension-normalized trace lower bound. -/
theorem barrier_trace_lower {d : ℕ} (A : PDE.Mat d) (lam : ℝ)
    (hA : lam • 1 ≤ A) : d * lam ≤ A.trace := by
  have hdiag : ∀ i : Fin d, lam ≤ A i i := by
    intro i
    have h := (Matrix.le_iff.mp hA).diag_nonneg (i := i)
    simpa using h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdiag i)
  simpa [Matrix.trace] using hsum


end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
