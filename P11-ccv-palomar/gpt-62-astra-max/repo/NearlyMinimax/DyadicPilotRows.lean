module

public import NearlyMinimax.IncrementPilotKernels
public import NearlyMinimax.DyadicTaylor


@[expose] public section

/-! Genuine physical feature-row factors for the sharp pair pilot. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

theorem dyadicPilotCell_subset_coarser {d j J : ℕ} (hj : j ≤ J) (x : Covariate d) :
    dyadicPilotCell J x ⊆ dyadicPilotCell j x := by
  induction J with
  | zero =>
    grind
  | succ J ih =>
    grind [dyadicPilotCell_subset_parent]

variable {d ℓ j J : ℕ} (hj : j ≤ J) {x z : Covariate d} (hx : x ∈ unitCube d) (hz : z ∈ unitCube d)
    (hc : z ∈ dyadicPilotCell j x)

include hx hz hc in
theorem dyadicAnchoredFeature_abs_le_distance
    (γ : AnchoredIndex d ℓ) :
    |dyadicAnchoredFeature j x z γ| ≤ 2 ^ j * euclideanNorm (z - x) := by
  have hv i : |((2 : ℝ) ^ j • (z - x)) i| ≤ 1 := by
    have hr := regular_grid_same_cell_radius (by positivity) hz hx hc i
    have he : ((2 : ℕ) ^ j : ℕ) = (2 : ℝ) ^ j := by simp
    rw [he] at hr
    change |2 ^ j * (z i - x i)| ≤ 1
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq (by field_simp)
  have h := anchoredMonomial_abs_le_euclideanNorm γ hv
  rw [euclideanNorm_smul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j)] at h
  exact h

def dyadicPilotRow (j : ℕ) (x z : Covariate d) : Fin (anchoredDimension d ℓ) → ℝ :=
  fun i => dyadicAnchoredFeature j x z (anchoredFinIndex i)

include hx hz hc in
theorem dyadicPilotRow_sum_abs_le_distance :
    (∑ i, |dyadicPilotRow (ℓ := ℓ) j x z i|) ≤
      (anchoredDimension d ℓ) * 2 ^ j * euclideanNorm (z - x) := by
  apply (Finset.sum_le_sum (fun i _ => dyadicAnchoredFeature_abs_le_distance hx hz hc _)).trans_eq
  simp [mul_assoc]

include hj hx hz in
/-- Every feature row for a coarser pilot satisfies its genuine `h 2^j`
factor on the actual finest dyadic same-cell pair support. -/
theorem dyadicPilotRow_sum_abs_le_fine_cell
    (hc : z ∈ dyadicPilotCell J x) :
    (∑ i, |dyadicPilotRow (ℓ := ℓ) j x z i|) ≤
      (anchoredDimension d ℓ) * 2 ^ j * Real.sqrt d * (2 ^ J)⁻¹ := by
  apply (dyadicPilotRow_sum_abs_le_distance hx hz
    (dyadicPilotCell_subset_coarser hj x hc)).trans
  apply (mul_le_mul_of_nonneg_left (euclideanNorm_le_coordinate_radius (by positivity) (regular_grid_same_cell_radius (by positivity) hz hx hc)) (by positivity)).trans_eq
  simp [mul_assoc]

end NearlyMinimax
