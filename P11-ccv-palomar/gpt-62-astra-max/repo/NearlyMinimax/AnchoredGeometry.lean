module

public import NearlyMinimax.AnchoredFeatures
public import NearlyMinimax.ModelRegularity

@[expose] public section

/-! Quantitative geometry of the exact nonconstant monomial feature vector. -/

noncomputable section
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

section
variable {d ℓ : ℕ} {u w : Covariate d} (hu : u ∈ unitCube d) (hw : w ∈ unitCube d)
    (γ : AnchoredIndex d ℓ) {v : Covariate d} (hv : ∀ i, |v i| ≤ 1)

include hv in
/-- Every nonconstant bounded monomial vanishes at least linearly at the origin. -/
theorem anchoredMonomial_abs_le_coordinate :
    ∃ i : Fin d, |anchoredMonomial γ v| ≤ |v i| := by
  classical
  obtain ⟨i, hi, hip⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (ne_of_gt γ.property.1)
  have hpow : |v i| ^ (γ.val i).val ≤ |v i| := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hip
    rw [hk, pow_succ]
    have hle  := (pow_le_pow_left₀ (abs_nonneg _) (hv i) k).trans_eq (one_pow k)
    simpa using mul_le_mul_of_nonneg_right hle (abs_nonneg (v i))
  have hrest : (∏ j ∈ Finset.univ.erase i,
      |v j| ^ (γ.val j).val) ≤ 1 := (Finset.prod_le_prod₀ (fun j _ => by positivity)
      (fun j _ => (pow_le_pow_left₀ (abs_nonneg _) (hv j) _))).trans_eq (by simp)
  refine ⟨i, ?_⟩
  unfold anchoredMonomial
  rw [Finset.abs_prod]
  simp
  rw [← Finset.prod_erase_mul _ _ hi]
  exact (mul_le_mul_of_nonneg_right hrest (by positivity)).trans
    (by bound)

include hv in
theorem anchoredMonomial_abs_le_euclideanNorm :
    |anchoredMonomial γ v| ≤ euclideanNorm v := by
  obtain ⟨i, hi⟩ := anchoredMonomial_abs_le_coordinate γ hv
  bound [abs_coordinate_le_euclideanNorm v i]

include hu hw in
/-- The actual normalized features satisfy the Lipschitz-at-anchor bound. -/
theorem anchoredFeature_abs_le_euclideanNorm :
    |anchoredFeature u w γ| ≤ euclideanNorm (w - u) := by
  apply anchoredMonomial_abs_le_euclideanNorm
  intro i
  change |w i - u i| ≤ 1
  rw [abs_le]
  constructor <;> linarith [(hu i).1, (hu i).2, (hw i).1, (hw i).2]

/-- Every monomial transport factor is at most one half. -/
theorem anchoredTransport_entry_bound :
    |(2 : ℝ) ^ (-(anchoredDegree γ : ℤ))| ≤ 1 / 2 := by
  simpa using (inv_le_inv₀ (by norm_num) (by norm_num)).mpr (by
    bound)

end

/-- The exact diagonal transport obeys the manuscript's genuine operator-norm bound. -/
theorem anchoredTransport_norm_le_half (d ℓ : ℕ) :
    ‖anchoredTransport d ℓ‖ ≤ 1 / 2 := by
  classical
  rw [anchoredTransport, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  exact anchoredTransport_entry_bound

end NearlyMinimax
