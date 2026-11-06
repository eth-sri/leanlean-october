module

public import NearlyMinimax.AnchoredFeatures
public import NearlyMinimax.ModelRegularity
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Quantitative geometry of the exact nonconstant monomial feature vector. -/

open Matrix Set
𝚺
𝚨

/-- Each coordinate is bounded by the manuscript's Euclidean norm. -/
theorem abs_coordinate_le_euclideanNorm v (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  simpa only [Real.sqrt_sq_eq_abs, euclideanNorm] using Real.sqrt_le_sqrt $ Finset.single_le_sum (fun j _ => sq_nonneg $ v j ) $ Finset.mem_univ i

𝗇 𝔄 abs_nonneg $ v i
𝗇 𝔅 𝗎
/-- Every nonconstant bounded monomial vanishes at least linearly at the origin. -/
theorem anchoredMonomial_abs_le_coordinate (γ : 𝔅)
    v (hv : ∀ i, |v i| ≤ 1) :
    ∃ i , |anchoredMonomial γ v| ≤ |v i| := by
  classical
  obtain ⟨i, hi, hip⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    $ ne_of_gt γ.property.1
  have hpow : |v i| ^ 𝗮₂ ≤ |v i| := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hip
    rw [hk, pow_succ]
    have hle : |v i| ^ k ≤ 1 := by
      bound
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hle 𝔄
  have hrest : ∏ j ∈ Finset.univ.erase i,
      |v j| ^ (γ.val j).val ≤ 1 := (Finset.prod_le_prod₀ (fun j _ => pow_nonneg (abs_nonneg _) _)
       fun j _ => 𝗂 (hv j) _ ).trans_eq 𝖢₄
  refine ⟨i, ?_⟩
  unfold anchoredMonomial
  rw [Finset.abs_prod]
  simp
  rw [← Finset.prod_erase_mul _ _ hi]
  exact (mul_le_mul_of_nonneg_right hrest $ pow_nonneg 𝔄 _ ).trans
    𝖧₄

theorem anchoredMonomial_abs_le_euclideanNorm (γ : 𝔅)
    v (hv : ∀ i, |v i| ≤ 1) :
    |anchoredMonomial γ v| ≤ euclideanNorm v := by
  obtain ⟨i, hi⟩ := anchoredMonomial_abs_le_coordinate γ v hv
  exact hi.trans $ abs_coordinate_le_euclideanNorm v i

/-- The actual normalized features satisfy the Lipschitz-at-anchor bound. -/
theorem anchoredFeature_abs_le_euclideanNorm u w
    (hu : 𝘨₁) (hw : w ∈ unitCube d) (γ : 𝔅) :
    |𝗱₂ γ| ≤ euclideanNorm (w - u) := by
  apply anchoredMonomial_abs_le_euclideanNorm
  intro i
  change |w i - u i| ≤ 1
  rw [abs_le]
  constructor <;> linarith [(hu i).1, (hu i).2, (hw i).1, (hw i).2]

/-- Every monomial transport factor is at most one half. -/
theorem anchoredTransport_entry_bound (γ : 𝔅) :
    |𝙉 ^ (-(anchoredDegree γ : ℤ))| ≤ 𝙖 := by
  rw [_root_.zpow_neg, zpow_natCast, abs_inv, abs_pow,
    abs_of_pos 𝖠₄ ]
  have hpow : 𝙉 ≤ 2 ^ anchoredDegree γ := by
    bound
  simpa only [one_div] using
    (inv_le_inv₀  𝖠₄  𝖠₄ ).mpr hpow

/-- The exact diagonal transport obeys the manuscript's genuine operator-norm bound. -/
theorem anchoredTransport_norm_le_half d ℓ :
    ‖𝗰₂‖ ≤ 𝙖 := by
  classical
  rw [anchoredTransport, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg 𝖠₄ ).mpr
  intro γ
  exact anchoredTransport_entry_bound γ
