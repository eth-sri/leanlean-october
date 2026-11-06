module

public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.TernaryMeasure


@[expose] public section

/-! Concrete nonconstant centered monomials and their Lebesgue Gram matrix. -/

noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators ENNReal

namespace NearlyMinimax

/-- Exactly the nonconstant monomials of total degree at most `ℓ`. -/
abbrev AnchoredIndex d ℓ :=
  {γ : PolynomialBox d ℓ // 0 < ∑ i, (γ i).val ∧ (∑ i, (γ i).val) ≤ ℓ}

section
variable {d ℓ : ℕ}

def anchoredDegree  (γ : AnchoredIndex d ℓ)  := ∑ i, (γ.val i).val

def anchoredExponent  (γ : AnchoredIndex d ℓ)  :=
  polynomialBoxExponent γ.val

@[simp] theorem anchoredExponent_apply  (γ : AnchoredIndex d ℓ)
    i : anchoredExponent γ i = (γ.val i).val :=
  polynomial_box_exponent_apply γ.val i

theorem anchoredExponent_injective  :
    Function.Injective (anchoredExponent (d := d) (ℓ := ℓ)) := by
  intro γ δ h
  exact Subtype.ext (polynomial_box_exponent_injective h)

def anchoredMonomial  (γ : AnchoredIndex d ℓ) (v : Covariate d)  :=
  ∏ i, (v i) ^ (γ.val i).val

def anchoredFeature  u w (γ : AnchoredIndex d ℓ)  :=
  anchoredMonomial γ (w - u)

/-- The exact scale-`j` feature from the manuscript. -/
def dyadicAnchoredFeature  j (x z : Covariate d)
    (γ : AnchoredIndex d ℓ)  :=
  anchoredMonomial γ (fun i => (2 : ℝ) ^ j * (z i - x i))

section
variable (γ : AnchoredIndex d ℓ)

theorem anchoredMonomial_scale  
    a v :
    anchoredMonomial γ (fun i => a * v i) = a ^ anchoredDegree γ * anchoredMonomial γ v := by
  unfold anchoredMonomial anchoredDegree
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]


end




theorem dyadicAnchoredFeature_scale  j x z
    (γ : AnchoredIndex d ℓ) :
    dyadicAnchoredFeature (j + 1) x z γ =
      2 ^ anchoredDegree γ * dyadicAnchoredFeature j x z γ := by
  unfold dyadicAnchoredFeature
  rw [show (fun i => (2 : ℝ) ^ (j + 1) * (z i - x i)) =
    (fun i => 2 * ((2 : ℝ) ^ j * (z i - x i))) by funext i; rw [pow_succ]; ring]
  exact anchoredMonomial_scale γ 2 _
end


/-- The fixed transport is diagonal, with precisely the paper's monomial factors. -/
def anchoredTransport d ℓ : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  Matrix.diagonal (fun γ => (2 : ℝ) ^ (-(anchoredDegree γ : ℤ)))

section
variable {d ℓ : ℕ}

theorem dyadicAnchoredFeature_transport  j x z :
    anchoredTransport d ℓ *ᵥ dyadicAnchoredFeature (j + 1) x z =
      dyadicAnchoredFeature j x z := by
  classical
  ext γ
  rw [anchoredTransport, mulVec_diagonal, dyadicAnchoredFeature_scale]
  simp_all

section
variable (γ : AnchoredIndex d ℓ)

theorem anchoredMonomial_continuous   :
    Continuous (anchoredMonomial γ) := continuous_finset_prod Finset.univ (fun i _ => (continuous_apply i).pow _)

theorem anchoredFeature_continuous   :
    Continuous (fun z : Covariate d × Covariate d => anchoredFeature z.1 z.2 γ) := (anchoredMonomial_continuous γ).comp (continuous_snd.sub continuous_fst)

theorem anchoredMonomial_abs_le_one  
    v (hv : ∀ i, |v i| ≤ 1) : |anchoredMonomial γ v| ≤ 1 := by
  unfold anchoredMonomial
  rw [Finset.abs_prod]
  simp only [abs_pow]
  exact (Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
    (fun i _ => (pow_le_pow_left₀ (abs_nonneg _) (hv i) _))).trans_eq
    (by simp)
end


theorem anchoredFeature_abs_le_one  u w
    (hu : u ∈ unitCube d) (hw : w ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    |anchoredFeature u w γ| ≤ 1 := by
  apply anchoredMonomial_abs_le_one
  intro i
  change |w i - u i| ≤ 1
  rw [abs_le]
  constructor <;> linarith [(hu i).1, (hu i).2, (hw i).1, (hw i).2]

/-- Coefficients in the concrete nonconstant monomial index set. -/
def anchoredPolynomial  (c : AnchoredIndex d ℓ → ℝ)  :=
  ∑ γ, monomial (anchoredExponent γ) (c γ)

section
variable (c : AnchoredIndex d ℓ → ℝ)

theorem anchoredPolynomial_coeff  
    γ : (anchoredPolynomial c).coeff (anchoredExponent γ) = c γ := by
  classical
  simp only [anchoredPolynomial, coeff_sum, coeff_monomial]
  have heq : ∀ δ : AnchoredIndex d ℓ, anchoredExponent δ = anchoredExponent γ ↔ δ = γ :=
    fun δ => ⟨fun h => anchoredExponent_injective h, fun h => congrArg anchoredExponent h⟩
  simp only [heq]
  simp

theorem anchoredPolynomial_eval  
    (v : Covariate d) :
    eval v (anchoredPolynomial c) = ∑ γ, c γ * anchoredMonomial γ v := by
  unfold anchoredPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem anchoredPolynomial_eq_zero_iff   :
    anchoredPolynomial c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext γ
    have := congrArg (fun P => P.coeff (anchoredExponent γ)) h
    simpa [anchoredPolynomial_coeff] using this
  · rintro rfl
    simp [anchoredPolynomial]
end

end


theorem unitCube_isCompact d : IsCompact (unitCube d) := by
  rw [unitCube_eq_pi]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

section
variable {d ℓ : ℕ} (u : Covariate d)
include u

/-- The actual known Lebesgue Gram, with no positivity hypothesis built into its definition. -/
def anchoredGram  :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  fun γ δ => ∫ w, anchoredFeature u w γ * anchoredFeature u w δ ∂cubeVolume d

theorem anchoredFeature_product_integrable 
    (γ δ : AnchoredIndex d ℓ) :
    Integrable (fun w => anchoredFeature u w γ * anchoredFeature u w δ) (cubeVolume d) := by
  apply ContinuousOn.integrableOn_compact (unitCube_isCompact d)
  exact (((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).mul
    ((anchoredMonomial_continuous δ).comp (continuous_id.sub continuous_const))).continuousOn

theorem anchoredGram_isHermitian  :
    (anchoredGram (ℓ := ℓ) u).IsHermitian := by
  ext γ δ
  simp only [conjTranspose_apply, star_trivial, anchoredGram]
  congr 1
  funext w
  exact mul_comm _ _

section
variable (c : AnchoredIndex d ℓ → ℝ)

theorem anchoredGram_quadratic 
     :
    c ⬝ᵥ (anchoredGram u *ᵥ c) =
      ∫ w, (∑ γ, c γ * anchoredFeature u w γ) ^ 2 ∂cubeVolume d := by
  classical
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

/-- A nonzero concrete centered polynomial has strictly positive squared
Lebesgue integral on the cube. Positivity is proved, rather than assumed. -/
theorem anchoredPolynomial_square_integral_pos 
     (hc : c ≠ 0) :
    0 < ∫ w, (∑ γ, c γ * anchoredFeature u w γ) ^ 2 ∂cubeVolume d := by
  classical
  let f  := fun w => ∑ γ, c γ * anchoredFeature u w γ
  have hf : Continuous f := by
    unfold f
    apply continuous_finset_sum
    intro γ hγ
    exact ((anchoredMonomial_continuous γ).comp
      (continuous_id.sub continuous_const)).const_mul (c γ)
  have hint : Integrable (fun w => f w ^ 2) (cubeVolume d) :=
    ContinuousOn.integrableOn_compact (unitCube_isCompact d) (hf.pow 2).continuousOn
  have hn : 0 ≤ ∫ w, f w ^ 2 ∂cubeVolume d := integral_nonneg (fun w => sq_nonneg (f w))
  change 0 < ∫ w, f w ^ 2 ∂cubeVolume d
  by_contra hnot
  have hz  := le_antisymm (le_of_not_gt hnot) hn
  have hae  :=
    ((integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg (f w)) hint).mp hz).mono
      (fun w hw => (sq_eq_zero_iff.mp hw))
  let U : Set (Covariate d) := univ.pi (fun _ => Ioo (0 : ℝ) 1)
  have hU : IsOpen U := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : U ⊆ unitCube d := by
    intro w hw i
    exact ⟨(hw i (mem_univ i)).1.le, (hw i (mem_univ i)).2.le⟩
  have haU  :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have heq := Measure.eqOn_open_of_ae_eq haU hU hf.continuousOn continuous_const.continuousOn
  have hpoly : anchoredPolynomial c = 0 := by
    apply MvPolynomial.funext_set (fun i : Fin d => Ioo (-u i) (1 - u i))
      (fun i => Ioo_infinite (by linarith))
    intro v hv
    have hvU : (fun i => v i + u i) ∈ U := by
      intro i hi
      have hi' := hv i (mem_univ i)
      constructor <;> linarith [hi'.1, hi'.2]
    have hfv := heq hvU
    have hs : (fun i => v i + u i) - u = v := by
      funext i
      simp only [Pi.sub_apply]
      ring
    simp only [Pi.zero_apply, f, anchoredFeature, hs] at hfv
    rw [anchoredPolynomial_eval]
    exact hfv
  exact hc ((anchoredPolynomial_eq_zero_iff c).mp hpoly)
end


/-- The known anchored Gram is positive definite for every anchor, including
all boundary anchors, since translation preserves monomial independence. -/
theorem anchoredGram_posDef  :
    (anchoredGram (ℓ := ℓ) u).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (anchoredGram_isHermitian u)
  intro c hc
  simp only [star_trivial]
  rw [anchoredGram_quadratic]
  exact anchoredPolynomial_square_integral_pos u c hc
end


end NearlyMinimax
