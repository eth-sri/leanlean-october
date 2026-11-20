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
abbrev AnchoredIndex (d ℓ : ℕ) :=
  {γ : PolynomialBox d ℓ // 0 < ∑ i, (γ i).val ∧ (∑ i, (γ i).val) ≤ ℓ}

section
variable {d ℓ : ℕ} (γ : AnchoredIndex d ℓ)

def anchoredDegree : ℕ := ∑ i, (γ.val i).val

def anchoredExponent : Fin d →₀ ℕ :=
  polynomialBoxExponent γ.val

end

theorem anchoredExponent_injective {d ℓ : ℕ} :
    Function.Injective (anchoredExponent (d := d) (ℓ := ℓ)) := fun γ δ h => Subtype.ext (polynomial_box_exponent_injective h)

section
variable {d ℓ : ℕ} (j : ℕ) (x z u w : Covariate d) (γ : AnchoredIndex d ℓ) (a : ℝ) (v : Covariate d)

def anchoredMonomial : ℝ :=
  ∏ i, (v i) ^ (γ.val i).val

def anchoredFeature : ℝ :=
  anchoredMonomial γ (w - u)

/-- The exact scale-`j` feature from the manuscript. -/
def dyadicAnchoredFeature : ℝ :=
  anchoredMonomial γ (fun i => 2 ^ j * (z i - x i))

theorem dyadicAnchoredFeature_scale :
    dyadicAnchoredFeature (j + 1) x z γ =
      2 ^ anchoredDegree γ * dyadicAnchoredFeature j x z γ := by
  unfold dyadicAnchoredFeature
  rw [show (fun i => 2 ^ (j + 1) * (z i - x i)) =
    (fun i => 2 * (2 ^ j * (z i - x i))) by funext i; rw [pow_succ]; ring]
  exact by unfold anchoredMonomial anchoredDegree; simp only [mul_pow]; rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end

/-- The fixed transport is diagonal, with precisely the paper's monomial factors. -/
def anchoredTransport (d ℓ : ℕ) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  Matrix.diagonal (fun γ => 2 ^ (-(anchoredDegree γ : ℤ)))

section
variable {d ℓ : ℕ} (u : Covariate d) (c : AnchoredIndex d ℓ → ℝ)

theorem dyadicAnchoredFeature_transport (j : ℕ) (x z : Covariate d) :
    anchoredTransport d ℓ *ᵥ dyadicAnchoredFeature (j + 1) x z =
      dyadicAnchoredFeature j x z := by
  classical
  ext γ
  rw [anchoredTransport, mulVec_diagonal, dyadicAnchoredFeature_scale]
  simp

theorem anchoredMonomial_continuous (γ : AnchoredIndex d ℓ) :
    Continuous (anchoredMonomial γ) := continuous_finset_prod Finset.univ (fun i _ => (continuous_apply i).pow _)

theorem anchoredMonomial_abs_le_one (γ : AnchoredIndex d ℓ)
    (v : Covariate d) (hv : ∀ i, |v i| ≤ 1) : |anchoredMonomial γ v| ≤ 1 := by
  unfold anchoredMonomial
  rw [Finset.abs_prod]
  simp
  exact (Finset.prod_le_prod₀ (fun i _ => by positivity)
    (fun i _ => (pow_le_pow_left₀ (abs_nonneg _) (hv i) _))).trans_eq
    (by simp)

theorem anchoredFeature_abs_le_one {u w : Covariate d}
    (hu : u ∈ unitCube d) (hw : w ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    |anchoredFeature u w γ| ≤ 1 := by
  apply anchoredMonomial_abs_le_one
  intro i
  change |w i - u i| ≤ 1
  rw [abs_le]
  constructor <;> linarith [(hu i).1, (hu i).2, (hw i).1, (hw i).2]

/-- Coefficients in the concrete nonconstant monomial index set. -/
def anchoredPolynomial : MvPolynomial (Fin d) ℝ :=
  ∑ γ, monomial (anchoredExponent γ) (c γ)

theorem anchoredPolynomial_coeff
    (γ : AnchoredIndex d ℓ) : (anchoredPolynomial c).coeff (anchoredExponent γ) = c γ := by
  classical
  simp [anchoredPolynomial]
  have heq : ∀ δ, anchoredExponent δ = anchoredExponent γ ↔ δ = γ :=
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

theorem anchoredPolynomial_eq_zero_iff :
    anchoredPolynomial c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext γ
    have := congrArg (fun P => P.coeff (anchoredExponent γ)) h
    simpa [anchoredPolynomial_coeff] using this
  · rintro rfl
    simp [anchoredPolynomial]

theorem unitCube_isCompact (d : ℕ) : IsCompact (unitCube d) := by
  rw [unitCube_eq_pi]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- The actual known Lebesgue Gram, with no positivity hypothesis built into its definition. -/
def anchoredGram :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  fun γ δ => ∫ w, anchoredFeature u w γ * anchoredFeature u w δ ∂cubeVolume d

theorem anchoredFeature_product_integrable
    (γ δ : AnchoredIndex d ℓ) :
    Integrable (fun w => anchoredFeature u w γ * anchoredFeature u w δ) (cubeVolume d) := by
  apply ContinuousOn.integrableOn_compact (unitCube_isCompact d)
  exact (((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).mul
    ((anchoredMonomial_continuous δ).comp (continuous_id.sub continuous_const))).continuousOn

theorem anchoredGram_isHermitian :
    (anchoredGram (ℓ := ℓ) u).IsHermitian := by
  ext γ δ
  simp [anchoredGram]
  congr 1
  exact mul_comm _ _

theorem anchoredGram_quadratic :
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
      ring
    · intro δ hδ
      exact ((anchoredFeature_product_integrable u γ δ).const_mul (c γ)).mul_const (c δ)
  · intro γ hγ
    exact integrable_finset_sum _ (fun δ hδ =>
      ((anchoredFeature_product_integrable u γ δ).const_mul (c γ)).mul_const (c δ))

/-- A nonzero concrete centered polynomial has strictly positive squared
Lebesgue integral on the cube. Positivity is proved, rather than assumed. -/
theorem anchoredPolynomial_square_integral_pos
    {c : AnchoredIndex d ℓ → ℝ} (hc : c ≠ 0) :
    0 < ∫ w, (∑ γ, c γ * anchoredFeature u w γ) ^ 2 ∂cubeVolume d := by
  classical
  let f  := fun w => ∑ γ, c γ * anchoredFeature u w γ
  have hf : Continuous f := by
    apply continuous_finset_sum
    intro γ hγ
    exact ((anchoredMonomial_continuous γ).comp
      (continuous_id.sub continuous_const)).const_mul (c γ)
  have hint : Integrable (fun w => f w ^ 2) (cubeVolume d) :=
    ContinuousOn.integrableOn_compact (unitCube_isCompact d) (hf.pow 2).continuousOn
  by_contra hnot
  have hae  :=
    ((integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg (f w)) hint).mp (le_antisymm (le_of_not_gt hnot) (by positivity))).mono
      (fun w hw => (sq_eq_zero_iff.mp hw))
  let U : Set (Covariate d) := univ.pi (fun _ => Ioo 0 1)
  have hsub : U ⊆ unitCube d := fun w hw i => ⟨(hw i (mem_univ i)).1.le, (hw i (mem_univ i)).2.le⟩
  have haU  :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have hpoly : anchoredPolynomial c = 0 := by
    apply MvPolynomial.funext_set (fun i => Ioo (-u i) (1 - u i))
      (fun i => Ioo_infinite (by linarith))
    intro v hv
    have hvU : (fun i => v i + u i) ∈ U := by
      intro i hi
      have hi' := hv i (mem_univ i)
      constructor <;> linarith [hi'.1, hi'.2]
    have hfv := (Measure.eqOn_open_of_ae_eq haU (isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)) hf.continuousOn continuous_const.continuousOn) hvU
    have hs : (fun i => v i + u i) - u = v := by
      funext i
      simp
    simp only [Pi.zero_apply, f, anchoredFeature, hs] at hfv
    rw [anchoredPolynomial_eval]
    exact hfv
  exact hc ((anchoredPolynomial_eq_zero_iff c).mp hpoly)

end

/-- The known anchored Gram is positive definite for every anchor, including
all boundary anchors, since translation preserves monomial independence. -/
theorem anchoredGram_posDef {d ℓ : ℕ} (u : Covariate d) :
    (anchoredGram (ℓ := ℓ) u).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (anchoredGram_isHermitian u)
  intro c hc
  simp
  rw [anchoredGram_quadratic]
  exact anchoredPolynomial_square_integral_pos u hc

end NearlyMinimax
