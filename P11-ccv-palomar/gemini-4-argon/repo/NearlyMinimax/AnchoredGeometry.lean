module
public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.TernaryMeasure
@[expose] public section
noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace NearlyMinimax

variable {d ℓ : ℕ}
abbrev AnchoredIndex (d ℓ : ℕ) :=
  {γ : PolynomialBox d ℓ // 0 < ∑ i, (γ i).val ∧ (∑ i, (γ i).val) ≤ ℓ}
def anchoredDegree  (γ : AnchoredIndex d ℓ) : ℕ := ∑ i, (γ.val i).val
def anchoredExponent  (γ : AnchoredIndex d ℓ) : Fin d →₀ ℕ :=
  polynomialBoxExponent γ.val
theorem anchoredExponent_injective  :
    Function.Injective (anchoredExponent (d := d) (ℓ := ℓ)) := by
  intro γ δ h
  exact Subtype.ext (polynomial_box_exponent_injective h)
def anchoredMonomial  (γ : AnchoredIndex d ℓ) (v : Covariate d) : ℝ :=
  ∏ i, (v i) ^ (γ.val i).val
def anchoredFeature  (u w : Covariate d) (γ : AnchoredIndex d ℓ) : ℝ :=
  anchoredMonomial γ (w - u)
def dyadicAnchoredFeature  (j : ℕ) (x z : Covariate d)
    (γ : AnchoredIndex d ℓ) : ℝ :=
  anchoredMonomial γ (fun i => 2 ^ j * (z i - x i))
theorem dyadicAnchoredFeature_scale  (j : ℕ) (x z : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicAnchoredFeature (j + 1) x z γ =
      ↑2 ^ anchoredDegree γ * dyadicAnchoredFeature j x z γ := by
  unfold dyadicAnchoredFeature
  rw [show (fun i => 2 ^ (j + 1) * (z i - x i)) =
    (fun i => 2 * (↑2 ^ j * (z i - x i))) by funext i; rw [pow_succ]; ring]
  have h_anchoredMonomial_scale (v : Covariate d) : anchoredMonomial γ (fun i => 2 * v i) = 2 ^ anchoredDegree γ * anchoredMonomial γ v := by
    unfold anchoredMonomial anchoredDegree
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  exact h_anchoredMonomial_scale _
def anchoredTransport (d ℓ : ℕ) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  Matrix.diagonal (fun γ => ↑2 ^ (-(anchoredDegree γ : ℤ)))
theorem anchoredMonomial_continuous  (γ : AnchoredIndex d ℓ) :
    Continuous (anchoredMonomial γ) := continuous_finset_prod Finset.univ (fun i _ => (continuous_apply i).pow _)
theorem anchoredFeature_continuous  (γ : AnchoredIndex d ℓ) :
    Continuous (fun z : Covariate d × Covariate d => anchoredFeature z.1 z.2 γ) := (anchoredMonomial_continuous γ).comp (continuous_snd.sub continuous_fst)
theorem anchoredMonomial_abs_le_one  (γ : AnchoredIndex d ℓ)
    (v : Covariate d) (hv : ∀ i, |v i| ≤ 1) : |anchoredMonomial γ v| ≤ 1 := by
  unfold anchoredMonomial
  rw [Finset.abs_prod]
  simp only [abs_pow]
  exact (Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
    (fun i _ => (pow_le_pow_left₀ (abs_nonneg _) (hv i) _))).trans_eq
    (by simp)
def anchoredPolynomial  (c : AnchoredIndex d ℓ → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ γ, monomial (anchoredExponent γ) (c γ)
theorem anchoredPolynomial_coeff  (c : AnchoredIndex d ℓ → ℝ)
    (γ : AnchoredIndex d ℓ) : (anchoredPolynomial c).coeff (anchoredExponent γ) = c γ := by
  simp only [anchoredPolynomial, coeff_sum, coeff_monomial]
  have heq : ∀ δ : AnchoredIndex d ℓ, anchoredExponent δ = anchoredExponent γ ↔ δ = γ :=
    fun δ => ⟨fun h => anchoredExponent_injective h, fun h => congrArg anchoredExponent h⟩
  simp only [heq]
  simp
theorem anchoredPolynomial_eval  (c : AnchoredIndex d ℓ → ℝ)
    (v : Covariate d) :
    eval v (anchoredPolynomial c) = ∑ γ, c γ * anchoredMonomial γ v := by
  unfold anchoredPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have h_anchoredExponent_apply (γ : AnchoredIndex d ℓ) (i : Fin d) : anchoredExponent γ i = (γ.val i).val := polynomial_box_exponent_apply γ.val i
  simp only [h_anchoredExponent_apply, anchoredMonomial]
theorem unitCube_isCompact (d ) : IsCompact (unitCube d) := by
  rw [unitCube_eq_pi]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)
def anchoredGram  (u : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  fun γ δ => ∫ w, anchoredFeature u w γ * anchoredFeature u w δ ∂cubeVolume d
theorem anchoredFeature_product_integrable  (u : Covariate d)
    (γ δ : AnchoredIndex d ℓ) :
    Integrable (fun w => anchoredFeature u w γ * anchoredFeature u w δ) (cubeVolume d) := by
  apply ContinuousOn.integrableOn_compact (unitCube_isCompact d)
  exact (((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).mul
    ((anchoredMonomial_continuous δ).comp (continuous_id.sub continuous_const))).continuousOn
theorem anchoredGram_isHermitian  (u : Covariate d) :
    (anchoredGram (ℓ := ℓ) u).IsHermitian := by
  ext γ δ
  simp only [conjTranspose_apply, star_trivial, anchoredGram]
  congr 1
  funext w
  exact mul_comm _ _
theorem anchoredGram_quadratic  (u : Covariate d)
    (c : AnchoredIndex d ℓ → ℝ) :
    c ⬝ᵥ (anchoredGram u *ᵥ c) =
      ∫ w, (∑ γ, c γ * anchoredFeature u w γ) ^ 2 ∂cubeVolume d := by
  have heq : (fun w => (∑ γ, c γ * anchoredFeature u w γ) ^ 2) =
      (fun w => ∑ γ, ∑ δ, c γ *
        (anchoredFeature u w γ * anchoredFeature u w δ) * c δ) := by
    funext w
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro δ hδ
    ring
  rw [heq, integral_finset_sum]
  · simp only [dotProduct, mulVec, Finset.mul_sum, anchoredGram]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [integral_finset_sum]
    · simp_rw [integral_mul_const, integral_const_mul]
      apply Finset.sum_congr rfl
      intro δ hδ
      ring
    · intro δ hδ
      exact ((anchoredFeature_product_integrable u γ δ).const_mul (c γ)).mul_const (c δ)
  · intro γ hγ
    exact integrable_finset_sum _ (fun δ hδ =>
      ((anchoredFeature_product_integrable u γ δ).const_mul (c γ)).mul_const (c δ))
theorem anchoredGram_posDef  (u : Covariate d) :
    (anchoredGram (ℓ := ℓ) u).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (anchoredGram_isHermitian u)
  intro c hc
  simp only [star_trivial]
  rw [anchoredGram_quadratic]
  let f : Covariate d → ℝ := fun w => ∑ γ, c γ * anchoredFeature u w γ
  have hf : Continuous f := by
    apply continuous_finset_sum
    intro γ hγ
    exact ((anchoredMonomial_continuous γ).comp
      (continuous_id.sub continuous_const)).const_mul (c γ)
  by_contra hnot
  have hae  :=
    ((integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg (f w)) (ContinuousOn.integrableOn_compact (unitCube_isCompact d) (hf.pow 2).continuousOn)).mp (le_antisymm (le_of_not_gt hnot) (integral_nonneg (fun w => sq_nonneg (f w))))).mono
      (fun w hw => (sq_eq_zero_iff.mp hw))
  have hpoly : anchoredPolynomial c = 0 := by
    apply MvPolynomial.funext_set (fun i => Ioo (-u i) (1 - u i))
      (fun i => Ioo_infinite (by linarith))
    intro v hv
    have hvU : (fun i => v i + u i) ∈ (univ.pi (fun _ => Ioo 0 1)) := by
      intro i hi
      have hi' := hv i (mem_univ i)
      constructor <;> linarith [hi'.1, hi'.2]
    have hfv := (Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset (by intro w hw i; exact ⟨(hw i (mem_univ i)).1.le, (hw i (mem_univ i)).2.le⟩) hae) (isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)) hf.continuousOn continuous_const.continuousOn) hvU
    have hs : (fun i => v i + u i) - u = v := by
      funext i
      simp only [Pi.sub_apply]
      ring
    simp only [f, anchoredFeature, hs] at hfv
    rw [anchoredPolynomial_eval]
    exact hfv
  have h_anchoredPolynomial_eq_zero_iff : anchoredPolynomial c = 0 ↔ c = 0 := by
    constructor
    · intro h
      funext γ
      have := congrArg (fun P => P.coeff (anchoredExponent γ)) h
      simpa [anchoredPolynomial_coeff] using this
    · rintro rfl
      simp [anchoredPolynomial]
  exact hc (h_anchoredPolynomial_eq_zero_iff.mp hpoly)
theorem abs_coordinate_le_euclideanNorm  (v : Covariate d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  simpa only [Real.sqrt_sq_eq_abs, euclideanNorm] using Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
theorem anchoredMonomial_abs_le_euclideanNorm  (γ : AnchoredIndex d ℓ)
    (v ) (hv : ∀ i, |v i| ≤ 1) :
    |anchoredMonomial γ v| ≤ euclideanNorm v := by
  have h_anchoredMonomial_abs_le_coordinate : ∃ i : Fin d, |anchoredMonomial γ v| ≤ |v i| := by
    obtain ⟨i, hi, hip⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (ne_of_gt γ.property.1 : (∑ i, (γ.val i).val) ≠ 0)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hip
    have hrest : (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
        |v j| ^ (γ.val j).val) ≤ 1 := by
      exact (Finset.prod_le_prod₀ (fun j _ => pow_nonneg (abs_nonneg _) _)
        (fun j _ => (pow_le_pow_left₀ (abs_nonneg _) (hv j) _))).trans_eq (by simp)
    refine ⟨i, ?_⟩
    unfold anchoredMonomial
    rw [Finset.abs_prod]
    simp only [abs_pow]
    rw [← Finset.prod_erase_mul _ _ hi]
    exact (mul_le_mul_of_nonneg_right hrest (pow_nonneg (abs_nonneg (v i)) _)).trans
      (by simpa only [one_mul] using (by rw [hk, pow_succ]; have hle  := (pow_le_pow_left₀ (abs_nonneg _) (hv i) k).trans_eq (one_pow k); simpa only [one_mul] using mul_le_mul_of_nonneg_right hle (abs_nonneg (v i))))
  obtain ⟨i, hi⟩ := h_anchoredMonomial_abs_le_coordinate
  exact hi.trans (abs_coordinate_le_euclideanNorm v i)
end NearlyMinimax
