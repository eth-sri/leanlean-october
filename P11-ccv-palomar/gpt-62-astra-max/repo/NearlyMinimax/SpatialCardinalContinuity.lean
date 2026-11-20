module

public import NearlyMinimax.SpatialCardinalCovariance

@[expose] public section

noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

/-- Coefficients of any finite polynomial product vary continuously
when each factor coefficient does; the antidiagonal convolution is
finite and independent of the parameter. -/
theorem mvpolynomial_product_coefficients_continuous {α κ σ : Type*}
    [TopologicalSpace α] [DecidableEq σ] (s : Finset κ)
    (P : κ → α → MvPolynomial σ ℝ)
    (hP : ∀ k ∈ s, ∀ β, Continuous (fun x => (P k x).coeff β)) :
    ∀ β, Continuous (fun x => (∏ k ∈ s, P k x).coeff β) := by
  classical
  induction s using Finset.induction_on with
  | empty => apply continuous_pi_iff.mp <;> fun_prop
  | @insert k s hk ih =>
    intro β
    simp [Finset.prod_insert hk, coeff_mul]
    continuity

theorem spatial_cardinal_polynomial_coefficients_continuous {d n : ℕ}
    (i : Fin n) (β : Fin d →₀ ℕ) :
    Continuous (fun U => (spatialCardinalPolynomial U i).coeff β) := by
  have hcoeff j δ :
      Continuous (fun U : DesignSample d n => (spatialCardinalAffine (U i) (U j)).coeff δ) := by
    simp only [spatialCardinalAffine, coeff_sum, coeff_sub, coeff_C_mul]
    apply continuous_finsetSum
    intro r _
    apply Continuous.sub
    · by_cases hδ : 0 = δ
      · simp only [coeff_C, hδ, ite_true]; fun_prop
      · simp only [coeff_C, hδ, ite_false]; exact continuous_const
    · fun_prop
  solve_by_elim [mvpolynomial_product_coefficients_continuous]

end NearlyMinimax
