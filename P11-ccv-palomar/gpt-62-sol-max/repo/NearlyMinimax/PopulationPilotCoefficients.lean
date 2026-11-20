module

public import NearlyMinimax.FiniteBounds

public import NearlyMinimax.PopulationPilotMeans

@[expose] public section

/-! Original multiscale mean coefficient vector, its uniform cap, Borel
measurability, and exact residual identity. -/

noncomputable section
open Matrix MeasureTheory Set
open scoped RealInnerProductSpace BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def dyadicPopulationPilotSum {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (t : Bool) (w : CovariatePair d) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j w.1 w.2 ⬝ᵥ dyadicPopulationRawPolynomial C θ j w.1 t (m j)

def dyadicPopulationCoefficients {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (w : CovariatePair d) : PairVector :=
  WithLp.toLp 2 ![1, -1 + dyadicPopulationPilotSum C θ J m true w,
    -dyadicPopulationPilotSum C θ J m false w]

theorem finite_row_abs_dot_le_pi_norm {ι : Type*} [Fintype ι] (row v : ι → ℝ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖v‖ := by
  apply abs_weighted_sum_le
  intro i _
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i

theorem dyadic_geometric_sum_le (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ (J + 1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, pow_succ _ (J + 1)]
    linarith

theorem dyadicPilotRow_total_abs_le {d ℓ : ℕ} (J : ℕ) (x y : Covariate d)
    (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) (hc : y ∈ dyadicPilotCell J x) :
    (∑ j ∈ Finset.range (J + 1), ∑ i, |dyadicPilotRow (ℓ := ℓ) j x y i|) ≤
      2 * (anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1),
      (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      apply dyadicPilotRow_sum_abs_le_fine_cell <;> simp_all
    _ = ((anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹) *
      ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      ring
    _ ≤ ((anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹) * (2 : ℝ) ^ (J + 1) :=
      mul_le_mul_of_nonneg_left (dyadic_geometric_sum_le J) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

section
variable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d)

theorem dyadicPopulationCoefficients_residual (J : ℕ) (m : ℕ → ℕ) (x y : Covariate d) :
    ⟪dyadicPopulationCoefficients C θ J m (x, y), pairResponseVector (θ.regression x) (θ.regression y)⟫ =
      dyadicPopulationResidual C θ J m x y := by
  have hsum : (∑ j ∈ Finset.range (J + 1),
      dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)) =
      dyadicPopulationPilotSum C θ J m false (x, y) -
        θ.regression x * dyadicPopulationPilotSum C θ J m true (x, y) := by
    simp only [dyadicPopulationPolynomial_affine, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      Finset.sum_sub_distrib, dyadicPopulationPilotSum]
    rw [Finset.mul_sum]
  rw [pairResponseVector_inner]
  change 1 * θ.regression y + (-1 + dyadicPopulationPilotSum C θ J m true (x, y)) * θ.regression x +
    (-dyadicPopulationPilotSum C θ J m false (x, y)) = dyadicPopulationResidual C θ J m x y
  unfold dyadicPopulationResidual
  linarith

section
variable (hθ : Admissible C θ)
include hθ

theorem dyadicPopulationRawPolynomial_measurable (j : ℕ) (t : Bool) (m : ℕ) :
    Measurable (fun x => dyadicPopulationRawPolynomial C θ j x t m) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (MvPolynomial.continuous_eval (MvPolynomial.rename
    (Fintype.equivFin (incrementVariables (anchoredDimension d C.order)))
      (rawIncrementEntryPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) t m i))).measurable.comp
      (dyadicIncrementRawMean_measurable C θ hθ j)

theorem dyadicPopulationPilotSum_measurable (J : ℕ) (m : ℕ → ℕ) (t : Bool) :
    Measurable (dyadicPopulationPilotSum C θ J m t) := by
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro i _
  exact (dyadicAnchoredFeature_joint_measurable j (anchoredFinIndex i)).mul
    (((dyadicPopulationRawPolynomial_measurable C θ hθ j t (m j)).eval (a := i)).comp measurable_fst)

theorem dyadicPopulationCoefficients_measurable (J : ℕ) (m : ℕ → ℕ) :
    Measurable (dyadicPopulationCoefficients C θ J m) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · simp
  · exact measurable_const.add (dyadicPopulationPilotSum_measurable C θ hθ J m true)
  · exact (dyadicPopulationPilotSum_measurable C θ hθ J m false).neg

end

end

end NearlyMinimax
