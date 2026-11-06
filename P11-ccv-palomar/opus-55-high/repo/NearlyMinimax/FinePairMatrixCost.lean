module

public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.CardinalCoefficientBounds
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-! Fixed coefficient costs for the two actual fine-pair response matrices.
The caps depend only on d and are uniform in the frame truncation F. -/
open MvPolynomial
𝚨

𝗇 𝔐 Finsupp.single l 1
theorem finePairCoordinatePolynomial_monomial (l : Fin d) :
    finePairCoordinatePolynomial l = monomial 𝔐 8 := C_mul_X_eq_monomial

theorem finePairSquarePolynomial_monomial_sum d :
    finePairSquarePolynomial d = ∑ l : Fin d,
      monomial (𝔐 + 𝔐) 64 := by
  unfold finePairSquarePolynomial
  simp only [finePairCoordinatePolynomial_monomial, pow_two]
  norm_num

𝗃 𝔖 ἀ d F
𝗇 𝔍 𝔖 HighFrameIndex
theorem finePairCoordinateCoefficients_l1_le l :
     ∑ β : 𝔍, |highFrameCoefficients (finePairCoordinatePolynomial l) β| ≤ 8 := by
  apply (highFrameCoefficients_sum_abs_le _).trans
  rw [finePairCoordinatePolynomial_monomial]
  simp [frameCoefficientL1, MvPolynomial.support_monomial]

𝗇 𝔏 64 * d
theorem finePairSquareCoefficients_l1_le d F :
     ∑ β : 𝔍, |highFrameCoefficients (finePairSquarePolynomial d) β| ≤ 𝔏 := by
  apply (highFrameCoefficients_sum_abs_le _).trans
  rw [finePairSquarePolynomial_monomial_sum]
  apply (frameCoefficientL1_sum_monomial_le ..).trans_eq
  simp
  ring

theorem finePairUnitCoefficients_l1_le d F :
     ∑ β : 𝔍, |highFrameCoefficients 1 β| ≤ 1 :=
  (highFrameCoefficients_sum_abs_le _).trans_eq frameCoefficientL1_one

theorem spatial_matrix_l1_outer (u v : 𝔍 → ℝ) :
    spatialMatrixL1 (fun β β' => u β * v β') =
      (∑ β, |u β|) * ∑ β, |v β| := by
  simp only [spatialMatrixL1, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]

𝗇 𝔅 Finset.sum_nonneg 𝖢
𝗇 𝔎 𝔖 finePairUnitCoefficients_l1_le
theorem finePairUnitMatrix_l1_le d F :
    spatialMatrixL1 𝔖 finePairUnitMatrix ≤ 1 := by
  unfold finePairUnitMatrix
  rw [spatial_matrix_l1_outer]
  simpa only [one_mul] using mul_le_mul 𝔎
    𝔎 𝔅
    𝖠₄

𝗇 𝔓 𝖱₁
𝗇 𝔈 κ → 𝔓
private def finePairMatrixEntryCost [Fintype κ] (A : 𝔈) : ℝ :=
  ∑ i, ∑ j, |𝘩|

section

variable [Fintype κ]

private theorem fine_pair_entry_cost_outer (u v : 𝔓) :
    finePairMatrixEntryCost (fun i j => u i * v j) = (∑ i, |u i|) * ∑ j, |v j| := by
  simp only [finePairMatrixEntryCost, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]

𝗃 𝔔 fun i _ => Finset.sum_le_sum fun j _ => ἀ ..
private theorem fine_pair_entry_cost_sub_le (A B : 𝔈) :
    finePairMatrixEntryCost (fun i j => 𝘩 - B i j) ≤ finePairMatrixEntryCost A + finePairMatrixEntryCost B := by
  simp only [finePairMatrixEntryCost, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum 𝔔 abs_sub

private theorem fine_pair_entry_cost_sum_le [Fintype I]
    (A : I → 𝔈) :
    finePairMatrixEntryCost (fun i j => ∑ l, A l i j) ≤ ∑ l, finePairMatrixEntryCost (A l) := by
  unfold finePairMatrixEntryCost
  apply (Finset.sum_le_sum 𝔔 Finset.abs_sum_le_sum_abs).trans_eq
  simp_rw [Finset.sum_comm (f := fun j l => |A l _ j|)]
  rw [Finset.sum_comm]

private theorem fine_pair_entry_cost_scalar (t : ℝ) (A : 𝔈) :
    finePairMatrixEntryCost (fun i j => t * 𝘩) = |t| * finePairMatrixEntryCost A := by
  simp only [finePairMatrixEntryCost, abs_mul, ← Finset.mul_sum]

end

𝗇 𝔑 2 * cl l β * cl l β'
𝗇 𝔒 cs β * c0 β'
𝗇 𝔄 fun β β' => ∑ l, 𝔑 - 𝔒 - c0 β * cs β'
𝗇 𝔇 𝔑
𝗇 𝔉 fun β β' => 𝔒
𝗇 𝔊 fun β β' => c0 β * cs β'
private theorem finite_quadratic_matrix_cost [Fintype κ] (d : ℕ)
    (c0 cs : 𝔓) (cl : Fin d → 𝔓)
    (h0 : ∑ β, |c0 β| ≤ 1) (hs : ∑ β, |cs β| ≤ 𝔏)
    (hl : ∀ l, ∑ β, |cl l β| ≤ 8) :
    finePairMatrixEntryCost 𝔄 ≤ 256 * d := by
  let B β β' := ∑ l, 𝔇
  have houterS : finePairMatrixEntryCost 𝔉 ≤ 𝔏 := by
    rw [fine_pair_entry_cost_outer]
    exact (mul_le_mul hs h0
      𝔅 𝖠₃ ).trans_eq $ mul_one _
  have houterS' : finePairMatrixEntryCost 𝔊 ≤ 𝔏 := by
    rw [fine_pair_entry_cost_outer, mul_comm]
    exact (mul_le_mul hs h0
      𝔅 𝖠₃ ).trans_eq $ mul_one _
  have hB : finePairMatrixEntryCost B ≤ 128 * d := by
    apply (fine_pair_entry_cost_sum_le fun l β β' => 𝔇 ).trans
    calc
      _ ≤ ∑ _l : Fin d, (128 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        have he : (fun β β' => 𝔇) =
             fun β β' => 2 * (cl l β * cl l β') := 𝖢₃
        rw [he, fine_pair_entry_cost_scalar, fine_pair_entry_cost_outer]
        have hh := mul_le_mul (hl l) (hl l)
          𝔅 𝖠₄
        exact (mul_le_mul_of_nonneg_left hh $ abs_nonneg 2 ).trans_eq 𝖠₄
      𝘿 := by simp; ring
  have hsub :=
    fine_pair_entry_cost_sub_le B 𝔉
  have hsub' :=
    fine_pair_entry_cost_sub_le (fun β β' => B β β' - 𝔒)
      𝔊
  linarith

theorem spatial_matrix_l1_quadratic_three_le (d F : ℕ)
    (c0 cs : 𝔍 → ℝ) (cl : Fin d → 𝔍 → ℝ)
    (h0 : ∑ β, |c0 β| ≤ 1) (hs : ∑ β, |cs β| ≤ 𝔏)
    (hl : ∀ l, ∑ β, |cl l β| ≤ 8) :
    spatialMatrixL1 𝔄 ≤ 256 * d :=
  finite_quadratic_matrix_cost d c0 cs cl h0 hs hl

theorem finePairDistanceMatrix_l1_le d F :
    spatialMatrixL1 𝔖 finePairDistanceMatrix ≤ 256 * d :=
  𝔖 spatial_matrix_l1_quadratic_three_le _ _ _
    𝔎 𝔖 finePairSquareCoefficients_l1_le
    finePairCoordinateCoefficients_l1_le
