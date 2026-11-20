module

public import NearlyMinimax.AnchoredSpectrum
public import NearlyMinimax.AnchoredGeometry


@[expose] public section

/-! Actual bounded vector moments for normalized population inverse pilots. -/

noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace NearlyMinimax

section
variable {d ℓ : ℕ} (u : Covariate d) (p g : Covariate d → ℝ)

/-- The normalized scalar-feature moment before known-Gram preconditioning. -/
def anchoredVectorMoment : AnchoredIndex d ℓ → ℝ :=
  fun γ => ∫ w, p w * anchoredFeature u w γ * g w ∂cubeVolume d

/-- The actual density and regression vector moments in the manuscript. -/
def anchoredPreconditionedMoment : AnchoredIndex d ℓ → ℝ :=
  (anchoredGram u)⁻¹ *ᵥ anchoredVectorMoment u p g

end

section
variable {d ℓ : ℕ} {u : Covariate d} (hu : u ∈ unitCube d) {p g : Covariate d → ℝ} {b F : ℝ} (hb : 0 ≤ b)
    (hF : 0 ≤ F) (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) (hg : ∀ w ∈ unitCube d, |g w| ≤ F)
include hF hb hg hp hu

theorem anchoredVectorMoment_coordinate_bound (γ : AnchoredIndex d ℓ) :
    |anchoredVectorMoment u p g γ| ≤ b * F := by
  let := cubeVolume_isProbability d
  have hbound : ∀ᵐ w ∂cubeVolume d,
      ‖p w * anchoredFeature u w γ * g w‖ ≤ b * F := by
    filter_upwards [hp, ae_restrict_mem (show MeasurableSet (unitCube d) from
      (unitCube_isCompact d).isClosed.measurableSet)] with w hw hcube
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw.1]
    have hφ := anchoredFeature_abs_le_one hu hcube γ
    calc
      _ ≤ b * 1 * F :=
        mul_le_mul (by bound) (hg w hcube) (abs_nonneg (g w)) (by positivity)
      _ = _ := by ring
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, anchoredVectorMoment]
    using norm_integral_le_of_norm_le_const hbound

theorem anchoredVectorMoment_norm_bound :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredVectorMoment u p g)‖ ≤
      Real.sqrt (Fintype.card (AnchoredIndex d ℓ)) * (b * F) := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hb hF)
  · calc
      _ ≤ ∑ _γ, (b * F) ^ 2 := by
        apply Finset.sum_le_sum
        intro γ hγ
        bound [anchoredVectorMoment_coordinate_bound hu hb hF hp hg γ]
      _ = (Fintype.card (AnchoredIndex d ℓ)) * (b * F) ^ 2 := by simp
      _ = _ := by
        grind

end

variable {d ℓ : ℕ}

/-- The actual known-Gram inverse has a fixed finite bound on all cube anchors. -/
theorem anchoredGram_inverse_uniform_bound :
    ∃ N : ℝ, 0 < N ∧ ∀ u ∈ unitCube d, ‖(anchoredGram (ℓ := ℓ) u)⁻¹‖ ≤ N := by
  have hc : Continuous (fun u : Covariate d => (anchoredGram (ℓ := ℓ) u)⁻¹) := by
    rw [(funext anchoredWhitening_square)]
    exact (anchoredWhitening_continuous).mul anchoredWhitening_continuous
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hc.norm.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  exact (hM (mem_image_of_mem _ hu)).trans (le_max_right _ _)

/-- A uniform scalar bound for every actual preconditioned vector family. -/
theorem anchoredPreconditionedMoment_uniform_bound
    (b F : ℝ) (hb : 0 ≤ b) (hF : 0 ≤ F) :
    ∃ W : ℝ, 0 < W ∧ ∀ u ∈ unitCube d, ∀ p g,
      (∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) →
      (∀ w ∈ unitCube d, |g w| ≤ F) →
      ‖anchoredPreconditionedMoment (ℓ := ℓ) u p g‖ ≤ W := by
  obtain ⟨N, hN, hNu⟩ := anchoredGram_inverse_uniform_bound
  let W := max 1 (N * (Real.sqrt (Fintype.card (AnchoredIndex d ℓ)) * (b * F)))
  refine ⟨W, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu p g hp hg
  have hA := Matrix.l2_opNorm_mulVec ((anchoredGram u)⁻¹)
    ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredVectorMoment u p g))
  have hpre : ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm
      (anchoredPreconditionedMoment u p g)‖ ≤ W := by
    apply hA.trans
    apply (mul_le_mul (hNu u hu) (anchoredVectorMoment_norm_bound (ℓ := ℓ) hu hb hF hp hg) (norm_nonneg _) hN.le).trans
    exact le_max_right _ _
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro γ
  exact (PiLp.norm_apply_le _ γ).trans hpre

end NearlyMinimax
