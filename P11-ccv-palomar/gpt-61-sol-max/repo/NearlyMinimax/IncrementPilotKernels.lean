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

section
variable {d : ℕ} (C : ModelConstants d)

section
variable (θ : RegressionParameter d)
include θ

section
variable (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ)
include x y m row

def dyadicIncrementKernel  
     :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin k => Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) ℝ :=
  (iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
    C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
      (dyadicIncrementRawMean θ j x)).compContinuousLinearMap
        (fun _ => incrementPilotCoordinate j x)

theorem dyadicIncrementKernel_raw  
     (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k (fun i => incrementGlobalVector j (z i)) =
      iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
        (dyadicIncrementRawMean θ j x) (fun i => dyadicIncrementRawVector j x (z i)) := by
  simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem dyadicIncrementKernel_symmetric 
     
    (σ : Equiv.Perm (Fin k)) v :
    dyadicIncrementKernel C θ j x y m row k (fun i => v (σ i)) =
      dyadicIncrementKernel C θ j x y m row k v := by
  let F := rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  have hF : (fun z => eval z F) = incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    exact rowIncrementPolynomial_eval _ _ _ _ _ _ _ _
  simp only [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [← hF]
  exact (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm
    (fun i => incrementPilotCoordinate j x (v i)) σ
end


theorem dyadicIncrementKernel_disjoint 
     j k (hk : 0 < k) x v
    (hxv : dyadicPilotLabel (j - 1) x ≠ dyadicPilotLabel (j - 1) v)
    y t m l row s
    (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k (fun i => incrementGlobalVector j (z i)) *
      dyadicIncrementKernel C θ j v t l s k (fun i => incrementGlobalVector j (z i)) = 0 := by
  rw [dyadicIncrementKernel_raw, dyadicIncrementKernel_raw]
  exact dyadic_increment_raw_kernels_disjoint hk j x v hxv _ _ z

theorem dyadicIncrementKernel_centered 
     (hθ : Admissible C θ) j x
    y m row k
    (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k
      (fun i => incrementGlobalVector j (z i) - incrementGlobalMean θ j) =
      iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
        (dyadicIncrementRawMean θ j x)
        (fun i => dyadicIncrementRawVector j x (z i) - dyadicIncrementRawMean θ j x) := by
  simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    map_sub, incrementPilotCoordinate_mean C θ hθ]
end


/-- Exact translation of the original coefficient pilot to a single fixed
global feature vector, with no covariance or mean premise. -/
theorem dyadicPolynomialPilot_centered_global 
    [Nonempty (AnchoredIndex d C.order)] θ (hθ : Admissible C θ)
    n j x y m
    row
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n) z :
    LiftL2.centeredKernelExpansion 0
      (fun r : Fin (m + anchoredDimension d C.order + 1) =>
        dyadicIncrementKernel C θ j x y m row (r.val + 1))
      (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z =
      dyadicPolynomialPilot C n j x y m row z -
        incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m row (dyadicIncrementRawMean θ j x) := by
  let F := rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  have hF : (fun z => eval z F) = incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    exact rowIncrementPolynomial_eval _ _ _ _ _ _ _ _
  have he := LiftL2.polynomialLift_centering_l2 F
    (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector j x (z i))
    (dyadicIncrementRawMean θ j x) (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree
  change _ = RoughRegime.Upper.polynomialLift F
    (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector j x (z i)) z - _
  rw [he]
  change _ = eval (dyadicIncrementRawMean θ j x) F + _ - _
  rw [rowIncrementPolynomial_eval, add_sub_cancel_left]
  simp only [LiftL2.centeredKernelExpansion, zero_add]
  apply Finset.sum_congr rfl
  intro r _
  unfold LiftL2.kernelStatistic LiftL2.kernelSum
  apply congrArg (fun a => (((r.val + 1).factorial : ℝ) *
    (n.descFactorial (r.val + 1) : ℝ))⁻¹ * a)
  apply Finset.sum_congr rfl
  intro e _
  rw [hF]
  exact dyadicIncrementKernel_centered C θ hθ j x y m row _ (fun i => z (e i))
end


end NearlyMinimax
