module

public import NearlyMinimax.IncrementPilotCoordinates
public import NearlyMinimax.IncrementPilotLocalization

@[expose] public section

/-! Exact global derivative kernels for the actual unbiased dyadic pilot.
They preserve the actual local raw energies and parent support, and their
centered factorial expansion is exactly the original polynomial pilot error. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def dyadicIncrementKernel {d : ℕ} {C : ModelConstants d} (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin k => Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) ℝ :=
  (iteratedFDeriv ℝ k (incrementFinScalar
    C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
      (dyadicIncrementRawMean θ j x)).compContinuousLinearMap
        (fun _ => incrementPilotCoordinate j x)

section
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (y : ℝ) (m : ℕ) (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ)

theorem dyadicIncrementKernel_raw (z : Fin k → Observation d) :
    dyadicIncrementKernel θ j x y m row k (fun i => incrementGlobalVector j (z i)) =
      iteratedFDeriv ℝ k (incrementFinScalar
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
        (dyadicIncrementRawMean θ j x) (fun i => dyadicIncrementRawVector j x (z i)) := by
  simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem dyadicIncrementKernel_symmetric {C : ModelConstants d}
    (θ : RegressionParameter d) {j : ℕ} (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ) {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (v : Fin k → Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) :
    dyadicIncrementKernel θ j x y m row k (fun i => v (σ i)) =
      dyadicIncrementKernel θ j x y m row k v := by
  let F := rowIncrementPolynomial C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  have hF : (fun z => eval z F) = incrementFinScalar
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    apply rowIncrementPolynomial_eval
  simp [dyadicIncrementKernel]
  rw [← hF]
  exact (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm
    (fun i => incrementPilotCoordinate j x (v i)) σ

theorem dyadicIncrementKernel_disjoint {C : ModelConstants d}
    (θ : RegressionParameter d) (j k : ℕ) (hk : 0 < k) {x v : Covariate d}
    (hxv : dyadicPilotLabel (j - 1) x ≠ dyadicPilotLabel (j - 1) v)
    (y t : ℝ) (m l : ℕ) (row s : Fin (anchoredDimension d C.order) → ℝ)
    (z : Fin k → Observation d) :
    dyadicIncrementKernel θ j x y m row k (fun i => incrementGlobalVector j (z i)) *
      dyadicIncrementKernel θ j v t l s k (fun i => incrementGlobalVector j (z i)) = 0 := by
  rw [dyadicIncrementKernel_raw, dyadicIncrementKernel_raw]
  solve_by_elim [dyadic_increment_raw_kernels_disjoint]

include hθ in
theorem dyadicIncrementKernel_centered
    (z : Fin k → Observation d) :
    dyadicIncrementKernel θ j x y m row k
      (fun i => incrementGlobalVector j (z i) - incrementGlobalMean θ j) =
      iteratedFDeriv ℝ k (incrementFinScalar
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
        (dyadicIncrementRawMean θ j x)
        (fun i => dyadicIncrementRawVector j x (z i) - dyadicIncrementRawMean θ j x) := by
  simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    map_sub, incrementPilotCoordinate_mean hθ]

end

/-- Exact translation of the original coefficient pilot to a single fixed
global feature vector, with no covariance or mean premise. -/
theorem dyadicPolynomialPilot_centered_global {d : ℕ} {C : ModelConstants d}
    [Nonempty (AnchoredIndex d C.order)] {θ : RegressionParameter d} (hθ : Admissible C θ)
    (n j : ℕ) (x : Covariate d) (y : ℝ) {m : ℕ}
    (row : Fin (anchoredDimension d C.order) → ℝ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n) (z : Fin n → Observation d) :
    LiftL2.centeredKernelExpansion 0
      (fun r : Fin (m + anchoredDimension d C.order + 1) =>
        dyadicIncrementKernel θ j x y m row (r.val + 1))
      (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z =
      dyadicPolynomialPilot n j x y m row z -
        incrementFinScalar C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m row (dyadicIncrementRawMean θ j x) := by
  let F := rowIncrementPolynomial C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  have hF : (fun z => eval z F) = incrementFinScalar
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    apply rowIncrementPolynomial_eval
  have he := LiftL2.polynomialLift_centering_l2 (F := F)
    (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector j x (z i))
    (dyadicIncrementRawMean θ j x) (rowIncrementPolynomial_degree ..) hdegree
  change _ = RoughRegime.Upper.polynomialLift F
    (fun i z => dyadicIncrementRawVector j x (z i)) z - _
  rw [he]
  change _ = eval (dyadicIncrementRawMean θ j x) F + _ - _
  rw [rowIncrementPolynomial_eval, add_sub_cancel_left]
  simp [LiftL2.centeredKernelExpansion, zero_add]
  apply Finset.sum_congr rfl
  intro r _
  apply congrArg (fun a => ((r.val + 1).factorial *
    (n.descFactorial (r.val + 1) : ℝ))⁻¹ * a)
  apply Finset.sum_congr rfl
  intro e _
  rw [hF]
  solve_by_elim [dyadicIncrementKernel_centered]

end NearlyMinimax
