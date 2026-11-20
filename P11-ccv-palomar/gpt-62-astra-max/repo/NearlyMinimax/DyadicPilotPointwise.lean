module

public import NearlyMinimax.KernelMomentBounds

public import NearlyMinimax.IncrementPilotFeatures
public import NearlyMinimax.PopulationRowDerivatives
public import NearlyMinimax.DyadicFit


@[expose] public section

/-! Actual original-law factorial pilots at a dyadic anchor.  Their population
point and derivative constants are derived from the original admissibility
conditions, rather than supplied as stochastic budget assumptions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d ℓ : ℕ} (r : ℕ)

def rowIncrementPolynomial {r : ℕ} (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  ∑ i, C (row i) * incrementFinPolynomial r a b T y m i

theorem rowIncrementPolynomial_eval (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) (z : Fin (Fintype.card (incrementVariables r)) → ℝ) :
    eval z (rowIncrementPolynomial a b T y m row) = incrementFinScalar a b T y m row z := by
  simp [rowIncrementPolynomial, incrementFinScalar, incrementFinVector, dotProduct]

theorem rowIncrementPolynomial_degree [NeZero r] (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    (rowIncrementPolynomial a b T y m row).totalDegree ≤ m + r + 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C, zero_add, incrementFinPolynomial] using
    (totalDegree_rename_le _ _).trans (incrementEntryPolynomial_degree a b T y m i)

theorem anchoredFinNormalizedGram_one (u : Covariate d) :
    anchoredFinNormalizedGram (ℓ := ℓ) u (fun _ => 1) = 1 := by
  have hG : anchoredDensityGram (ℓ := ℓ) u (fun _ => 1) = anchoredGram u := by
    ext γ δ
    simp [anchoredDensityGram, anchoredGram]
  unfold anchoredFinNormalizedGram
  rw [hG, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_posDef u).isUnit)]
  exact map_one _

def dyadicPolynomialPilot {C : ModelConstants d} (n j : ℕ) (x : Covariate d)
    (y : ℝ) (m : ℕ) (row : Fin (anchoredDimension d C.order) → ℝ)
    (z : Fin n → Observation d) : ℝ :=
  RoughRegime.Upper.polynomialLift
    (rowIncrementPolynomial C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m row)
    (fun i z => dyadicIncrementRawVector j x (z i)) z

/-- The concrete coefficient lift is L² and exactly unbiased at its genuine
population polynomial, even though the observed responses are unbounded. -/
theorem dyadicPolynomialPilot_moment_facts {C : ModelConstants d}
    [Nonempty (AnchoredIndex d C.order)] {θ : RegressionParameter d} (hθ : Admissible C θ)
    (n j : ℕ) {x : Covariate d} (hx : x ∈ unitCube d) (y : ℝ) {m : ℕ}
    (row : Fin (anchoredDimension d C.order) → ℝ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (dyadicPolynomialPilot n j x y m row) 2 (sampleLaw θ n) ∧
    (∫ z, dyadicPolynomialPilot n j x y m row z ∂sampleLaw θ n) =
      incrementFinScalar C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) y m row (dyadicIncrementRawMean θ j x) := by
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts hθ j hx
  refine ⟨LiftL2.polynomialLift_memLp_two_l2 (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree ..) hdegree hind hmeas hL2, ?_⟩
  rw [← rowIncrementPolynomial_eval]
  exact LiftL2.polynomialLift_expectation_l2
    (rowIncrementPolynomial_degree ..) hdegree hind hmeas hid hL2 hmean

end

/-- The scalar derivative estimate used by both the kernel and the variance bounds. -/
abbrev PilotDerivativeBound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (Y D A : ℝ) : Prop :=
  ∀ j, ∀ x ∈ unitCube d, ∀ y, |y| ≤ Y → ∀ m k,
      ∀ row,
        ‖iteratedFDeriv ℝ k (incrementFinScalar
          C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
          (dyadicIncrementRawMean θ j x)‖ ≤ (∑ i, |row i|) * D * k.factorial * A ^ k

/-- Pointwise variance budget for a single dyadic polynomial pilot. -/
abbrev PilotVarianceBound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (D A : ℝ) : Prop :=
  ∀ n j,
      ∀ x ∈ unitCube d, ∀ y, |y| ≤ C.holderBound → ∀ m,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
      m + anchoredDimension d C.order + 1 ≤ n →
      ∀ Λ, 0 < Λ → Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1 →
        variance (dyadicPolynomialPilot n j x y m row) (sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 *
            dyadicPilotSeries C A Λ j m

theorem dyadicPolynomialPilot_variance_of_derivative {d : ℕ} {C : ModelConstants d}
    [Nonempty (AnchoredIndex d C.order)] {θ : RegressionParameter d} (hθ : Admissible C θ)
    {D A : ℝ} (hD : 0 < D) (hA : 0 < A)
    (hder : PilotDerivativeBound C θ C.holderBound D A) :
    PilotVarianceBound C θ D A := by
  intro n j x hx y hy m row hdegree Λ hΛ hΛn
  let := sampleLaw_isProbability C θ hθ n
  let F := rowIncrementPolynomial C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  let X (i : Fin n) (z : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := C.order) j x (z i)
  let E := dyadicFeatureEnergy C j
  have hE : 0 ≤ E := dyadicFeatureEnergy_nonneg C j
  have hrow : 0 ≤ (∑ i, |row i|) * D :=
    mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts hθ j hx
  have hv := LiftL2.polynomialLift_variance_le_raw_power_l2 (F := F)
    (rowIncrementPolynomial_degree ..) hdegree hind hmeas hid hL2 hmean hΛ
    (by simpa only [Nat.cast_add, Nat.cast_one] using hΛn)
  apply hv.trans
  rw [dyadicPilotSeries, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  let e := Fin.castLEEmb ((Nat.succ_le_of_lt t.isLt).trans hdegree)
  have hFeval : (fun z => eval z F) = incrementFinScalar
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    exact rowIncrementPolynomial_eval ..
  have hd : ‖iteratedFDeriv ℝ (t.val + 1) (fun z => eval z F) (dyadicIncrementRawMean θ j x)‖ ≤
      ((∑ i, |row i|) * D) * (t.val + 1).factorial * A ^ (t.val + 1) := by
    rw [hFeval]
    exact hder j x hx y hy m (t.val + 1) row
  have hb := KernelMomentBounds.factorial_kernel_budget (hind.precomp e.injective) (fun i => hmeas (e i))
    (fun i a => hL2 (e i) a) hE hrow hA.le hΛ
    (fun i => dyadicIncrementRawVector_sample_second_le hθ j hx (e i)) hd
  simpa only [E, e, mul_assoc] using hb

end NearlyMinimax
