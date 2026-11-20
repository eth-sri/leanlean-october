module

public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.CardinalCoefficientBounds

@[expose] public section

/-! Fixed coefficient costs for the two actual fine-pair response matrices.
The caps depend only on d and are uniform in the frame truncation F. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem finePairCoordinatePolynomial_monomial {d : ℕ} (l : Fin d) :
    finePairCoordinatePolynomial l = monomial (Finsupp.single l 1) 8 := C_mul_X_eq_monomial

section
variable (d F : ℕ)

theorem finePairSquarePolynomial_monomial_sum :
    finePairSquarePolynomial d = ∑ l,
      monomial (Finsupp.single l 1 + Finsupp.single l 1) 64 := by
  unfold finePairSquarePolynomial
  simp [finePairCoordinatePolynomial_monomial, pow_two, monomial_mul]
  norm_num

theorem finePairCoordinateCoefficients_l1_le {d F : ℕ} (l : Fin d) :
    (∑ β : HighFrameIndex d F, |highFrameCoefficients (finePairCoordinatePolynomial l) β|) ≤ 8 := by
  apply (highFrameCoefficients_sum_abs_le _).trans
  rw [finePairCoordinatePolynomial_monomial]
  simp [frameCoefficientL1, MvPolynomial.support_monomial]

theorem finePairSquareCoefficients_l1_le :
    (∑ β : HighFrameIndex d F, |highFrameCoefficients (finePairSquarePolynomial d) β|) ≤ 64 * d := by
  apply (highFrameCoefficients_sum_abs_le _).trans
  rw [finePairSquarePolynomial_monomial_sum]
  apply (frameCoefficientL1_sum_monomial_le _ _).trans_eq
  norm_num <;> linarith

theorem finePairUnitCoefficients_l1_le :
    (∑ β : HighFrameIndex d F, |highFrameCoefficients 1 β|) ≤ 1 :=
  (highFrameCoefficients_sum_abs_le _).trans_eq frameCoefficientL1_one

theorem spatial_matrix_l1_outer {d F : ℕ} (u v : HighFrameVector d F) :
    spatialMatrixL1 (fun β β' => u β * v β') =
      (∑ β, |u β|) * (∑ β, |v β|) := by
  simp only [spatialMatrixL1, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]

theorem finePairUnitMatrix_l1_le :
    spatialMatrixL1 (finePairUnitMatrix d F) ≤ 1 := by
  unfold finePairUnitMatrix
  rw [spatial_matrix_l1_outer]
  simpa using mul_le_mul (finePairUnitCoefficients_l1_le d F)
    (finePairUnitCoefficients_l1_le d F) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (by norm_num)

end

section
variable {κ I : Type*} [Fintype κ] (u v : κ → ℝ) (t : ℝ) (A : κ → κ → ℝ)

private def finePairMatrixEntryCost : ℝ :=
  ∑ i, ∑ j, |A i j|

private theorem fine_pair_entry_cost_outer :
    finePairMatrixEntryCost (fun i j => u i * v j) = (∑ i, |u i|) * (∑ j, |v j|) := by
  simp only [finePairMatrixEntryCost, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]

private theorem fine_pair_entry_cost_sub_le (B : κ → κ → ℝ) :
    finePairMatrixEntryCost (fun i j => A i j - B i j) ≤ finePairMatrixEntryCost A + finePairMatrixEntryCost B := by
  simp only [finePairMatrixEntryCost, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => abs_sub _ _))

private theorem fine_pair_entry_cost_sum_le [Fintype I]
    (A : I → κ → κ → ℝ) :
    finePairMatrixEntryCost (fun i j => ∑ l, A l i j) ≤ ∑ l, finePairMatrixEntryCost (A l) := by
  unfold finePairMatrixEntryCost
  apply (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => Finset.abs_sum_le_sum_abs _ _))).trans_eq
  simp_rw [Finset.sum_comm (f := fun j l => |A l _ j|)]
  rw [Finset.sum_comm]

private theorem fine_pair_entry_cost_scalar :
    finePairMatrixEntryCost (fun i j => t * A i j) = |t| * finePairMatrixEntryCost A := by
  simp only [finePairMatrixEntryCost, abs_mul, ← Finset.mul_sum]

private theorem finite_quadratic_matrix_cost {d : ℕ}
    {c0 cs : κ → ℝ} {cl : Fin d → κ → ℝ}
    (h0 : (∑ β, |c0 β|) ≤ 1) (hs : (∑ β, |cs β|) ≤ 64 * d)
    (hl : ∀ l, (∑ β, |cl l β|) ≤ 8) :
    finePairMatrixEntryCost (fun β β' => (∑ l, 2 * cl l β * cl l β') -
      cs β * c0 β' - c0 β * cs β') ≤ 256 * d := by
  let B β β'  := ∑ l, 2 * cl l β * cl l β'
  have houterS : finePairMatrixEntryCost (fun β β' => cs β * c0 β') ≤ 64 * d := by
    rw [fine_pair_entry_cost_outer]
    exact (mul_le_mul hs h0
      (by positivity) (by positivity)).trans_eq (mul_one _)
  have houterS' : finePairMatrixEntryCost (fun β β' => c0 β * cs β') ≤ 64 * d := by
    rw [fine_pair_entry_cost_outer, mul_comm]
    exact (mul_le_mul hs h0
      (by positivity) (by positivity)).trans_eq (mul_one _)
  have hB : finePairMatrixEntryCost B ≤ 128 * d := by
    apply (fine_pair_entry_cost_sum_le (fun l β β' => 2 * cl l β * cl l β')).trans
    calc
      _ ≤ ∑ _l, (128 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        have he : (fun β β' => 2 * cl l β * cl l β') =
            (fun β β' => 2 * (cl l β * cl l β')) := by funext β β'; ring
        rw [he, fine_pair_entry_cost_scalar, fine_pair_entry_cost_outer]
        have hh := mul_le_mul (hl l) (hl l)
          (by positivity) (by norm_num)
        exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by norm_num)
      _ = _ := by simp; ring
  bound [fine_pair_entry_cost_sub_le B (fun β β' => cs β * c0 β'), fine_pair_entry_cost_sub_le (fun β β' => B β β' - cs β * c0 β') (fun β β' => c0 β * cs β')]

end

theorem finePairDistanceMatrix_l1_le (d F : ℕ) :
    spatialMatrixL1 (finePairDistanceMatrix d F) ≤ 256 * d :=
  finite_quadratic_matrix_cost (finePairUnitCoefficients_l1_le d F) (finePairSquareCoefficients_l1_le d F)
      (fun l => finePairCoordinateCoefficients_l1_le l)

end NearlyMinimax
