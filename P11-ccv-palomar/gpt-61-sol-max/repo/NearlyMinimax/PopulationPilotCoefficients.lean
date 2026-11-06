module

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

section
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (J : ℕ) (m : ℕ → ℕ)
include C θ J m

def dyadicPopulationPilotSum  (t : Bool) (w : Covariate d × Covariate d)  :=
  ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j w.1 w.2 ⬝ᵥ dyadicPopulationRawPolynomial C θ j w.1 t (m j)

def dyadicPopulationCoefficients  (w : Covariate d × Covariate d) : PairVector :=
  WithLp.toLp 2 ![1, -1 + dyadicPopulationPilotSum C θ J m true w,
    -dyadicPopulationPilotSum C θ J m false w]
end


theorem finite_row_abs_dot_le_pi_norm {ι : Type*} [Fintype ι] (row v : ι → ℝ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖v‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i, |row i * v i|) ≤ ∑ i, |row i| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem dyadic_geometric_sum_le J :
    (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) ≤ 2 ^ (J + 1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, pow_succ _ (J + 1)]
    linarith

theorem dyadicPilotRow_total_abs_le {d ℓ } J x y
    (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) (hc : y ∈ dyadicPilotCell J x) :
    (∑ j ∈ Finset.range (J + 1), ∑ i, |dyadicPilotRow (ℓ := ℓ) j x y i|) ≤
      2 * (anchoredDimension d ℓ) * Real.sqrt d := by
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1),
      (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      exact dyadicPilotRow_sum_abs_le_fine_cell j J (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x y hx hy hc
    _ = ((anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹) *
      ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ((anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹) * (2 : ℝ) ^ (J + 1) :=
      mul_le_mul_of_nonneg_left (dyadic_geometric_sum_le J) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

section
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)

theorem dyadicPopulationCoefficients_residual  J m x y :
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
  rw [hsum]
  ring

section
variable (hθ : Admissible C θ)
include hθ

theorem dyadicPopulationRawPolynomial_measurable   j (t : Bool) m :
    Measurable (fun x => dyadicPopulationRawPolynomial C θ j x t m) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (MvPolynomial.continuous_eval (MvPolynomial.rename
    (Fintype.equivFin (incrementVariables (anchoredDimension d C.order)))
      (rawIncrementEntryPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) t m i))).measurable.comp
      (dyadicIncrementRawMean_measurable C θ hθ j)

theorem dyadicPopulationPilotSum_measurable   J m (t : Bool) :
    Measurable (dyadicPopulationPilotSum C θ J m t) := by
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro i _
  exact (dyadicAnchoredFeature_joint_measurable j (anchoredFinIndex i)).mul
    (((dyadicPopulationRawPolynomial_measurable C θ hθ j t (m j)).eval (a := i)).comp measurable_fst)

theorem dyadicPopulationCoefficients_measurable   J m :
    Measurable (dyadicPopulationCoefficients C θ J m) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_const
  · exact measurable_const.add (dyadicPopulationPilotSum_measurable C θ hθ J m true)
  · exact (dyadicPopulationPilotSum_measurable C θ hθ J m false).neg
end

end


end NearlyMinimax
