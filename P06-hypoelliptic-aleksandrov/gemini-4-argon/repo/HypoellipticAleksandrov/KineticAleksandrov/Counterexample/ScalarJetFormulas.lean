module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarJetFields
import Mathlib.Tactic

/-! # Literal rescaled scalar derivative formulae -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/- Exact position derivative in the form exposing the leading-term cancellation. -/
theorem scalarAnsatz_deriv_x_cancel (gamma : ScalarGamma) (Lam x v : ℝ)
    (hLam : 0 < Lam) (hx : 0 < x) :
    deriv (fun y => scalarAnsatz gamma Lam y v) x =
      Real.rpow x (gamma.1 - 1) * (gamma.1 * F gamma Lam (scalarSimilarity x v) -
        scalarSimilarity x v / 3 * deriv (F gamma Lam) (scalarSimilarity x v)) := by
  rw [(scalarAnsatz_hasDerivAt_x gamma Lam x v hx
    ((F_contDiff_two gamma Lam hLam).differentiable (by norm_num) _)).deriv]
  have hxp : Real.rpow x (gamma.1 - 1) = Real.rpow x gamma.1 / x := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hx, Real.rpow_one]
  have hxn : Real.rpow x (-(4 / 3)) = (x * Real.rpow x (1 / 3))⁻¹ := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hx.le, show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num,
      Real.rpow_add hx, Real.rpow_one]
  rw [hxp, hxn]
  unfold scalarSimilarity
  ring

/- Exact velocity derivative with the source kinetic degree. -/
theorem scalarAnsatz_deriv_v_power (gamma : ScalarGamma) (Lam x v : ℝ)
    (hLam : 0 < Lam) (hx : 0 < x) :
    deriv (scalarAnsatz gamma Lam x) v = -Real.rpow x (gamma.1 - 1 / 3) *
      deriv (F gamma Lam) (scalarSimilarity x v) := by
  rw [(scalarAnsatz_hasDerivAt_v gamma Lam x v
    ((F_contDiff_two gamma Lam hLam).differentiable (by norm_num) _)).deriv]
  simp only [Real.rpow_eq_pow, Real.rpow_sub hx]

/- Exact second velocity derivative with the source kinetic degree. -/
theorem scalarAnsatz_deriv2_v_power (gamma : ScalarGamma) (Lam x v : ℝ)
    (hLam : 0 < Lam) (hx : 0 < x) :
    deriv (deriv (scalarAnsatz gamma Lam x)) v = Real.rpow x (gamma.1 - 2 / 3) *
      deriv (deriv (F gamma Lam)) (scalarSimilarity x v) := by
  rw [scalarAnsatz_deriv2_v gamma Lam x v (F_contDiff_two gamma Lam hLam).contDiffAt]
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_sub hx, ← Real.rpow_natCast (x ^ (1 / 3 : ℝ)) 2,
    ← Real.rpow_mul hx.le]
  norm_num

/- The positive-position velocity selector is the literal scalar velocity derivative. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
