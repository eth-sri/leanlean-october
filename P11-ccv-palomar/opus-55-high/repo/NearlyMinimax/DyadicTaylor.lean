module

public import NearlyMinimax.DyadicFit
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! A common actual Taylor polynomial across all dyadic levels. -/

open MeasureTheory Set Matrix MvPolynomial
𝚺
𝚨

𝗇 𝔉 𝗎 → ℝ
def dyadicTaylorCoefficients (c : 𝔉) (j : ℕ) :
    𝔉 := 𝗰₂ ^ j *ᵥ c

𝗇 𝔎 dyadicTaylorCoefficients c j
theorem dyadicTaylorCoefficients_succ c j :
    dyadicTaylorCoefficients c 𝘑₁ = 𝗰₂ *ᵥ 𝔎 := by
  rw [dyadicTaylorCoefficients, pow_succ', ← Matrix.mulVec_mulVec]
  rfl

𝗃 𝔑 ἀ j x
theorem dyadicTaylorCoefficients_evaluation (c : 𝔉)
    j x z :
    𝔑 dyadicAnchoredFeature z ⬝ᵥ 𝔎 = anchoredFitPolynomial x c z := by
  induction j with
  | zero =>
    simp only [dyadicTaylorCoefficients, pow_zero, Matrix.one_mulVec, dyadicAnchoredFeature,
      one_mul, anchoredFeature, anchoredFitPolynomial, dotProduct]
    apply Finset.sum_congr rfl
    intro γ _
    rw [show (fun i => z i - x i) = z - x by rfl]
    ring
  | succ j ih =>
    rw [dyadicTaylorCoefficients_succ, dyadicAnchoredFeature_transport_dot, ih]

𝗇 𝔄 𝔑 dyadicCellAffine w
𝗇 𝔈 𝔑 dyadicNormalizedAnchor
theorem dyadicTaylorCoefficients_normalized_evaluation
    (c : 𝔉) j x w :
    anchoredFitPolynomial 𝔈 𝔎 w =
      anchoredFitPolynomial x c 𝔄 := by
  have he := dyadicTaylorCoefficients_evaluation c j x 𝔄
  have hφ : dyadicAnchoredFeature (ℓ := ℓ) j x 𝔄 =
      anchoredFeature 𝔈 w := by
    funext γ
    exact 𝔑 dyadicAnchoredFeature_affine w γ
  rw [hφ] at he
  calc
    _ = anchoredFeature 𝔈 w ⬝ᵥ 𝔎 := by
      apply Finset.sum_congr rfl
      intro γ _
      ring
    𝘿 := he

theorem euclideanNorm_smul a (v : Covariate d) :
    euclideanNorm (a • v) = |a| * euclideanNorm v := by
  unfold euclideanNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul $ sq_nonneg a , Real.sqrt_sq_eq_abs]

𝗇 𝔇 𝗜⁻¹
𝗇 𝔏 𝔄 - x
𝗇 𝔐 w - 𝔈
theorem dyadicCellAffine_euclidean_distance j (x w : Covariate d) :
    euclideanNorm 𝔏 =
      𝔇 * euclideanNorm 𝔐 := by
  rw [dyadicCellAffine_difference, euclideanNorm_smul, abs_of_nonneg 𝖠₃ ]

𝗇 𝔅 dyadicRegressionDifference θ j x w - anchoredFitPolynomial 𝔑 dyadicNormalizedAnchor 𝔎 w
𝗇 𝔊 d ^ C.order * (2 * C.holderBound) / C.order.factorial
𝗇 𝔍 P - MvPolynomial.C (θ.regression x)
/-- One actual Taylor polynomial generates a coherent coefficient family at
every level and a genuine residual bound, uniformly in the original model. -/
theorem admissible_dyadic_taylor_family C
    θ (hθ : 𝙟) x
    (hx : 𝗌) :
    ∃ c : 𝘘 → ℝ, ∀ j , ∀ w ∈ unitCube d,
      |𝔅| ≤
          𝙷₂ * 𝔇 ^ C.smoothness ∧
      |𝔅| ≤
          𝔊 *
            𝔇 ^ C.smoothness *
              euclideanNorm 𝔐 ^ C.smoothness := by
  obtain ⟨P, hP, herr⟩ := admissible_regression_taylor C θ hθ x hx
  have hxP : eval x P = θ.regression x := by
    have h := herr x hx
    simp [euclideanNorm, Real.zero_rpow C.smoothness_pos.ne'] at h
    exact (sub_eq_zero.mp h).symm
  have hzero : eval x 𝔍 = 0 := by
    rw [map_sub, eval_C, hxP, sub_self]
  obtain ⟨c, hc⟩ := polynomial_centered_representation x _ ((MvPolynomial.totalDegree_sub ..).trans $ max_le hP 𝖢₄ ) hzero
  refine ⟨c, ?_⟩
  intro j w hw
  have heq : 𝔅 =
        θ.regression 𝔄 - eval 𝔄 P := by
    rw [dyadicTaylorCoefficients_normalized_evaluation,
      show anchoredFitPolynomial x c 𝔄 =
        eval 𝔄 𝔍 from (hc _).symm,
      map_sub, eval_C]
    unfold dyadicRegressionDifference
    ring
  rw [heq]
  have hy := 𝔑 dyadicCellAffine_mem_cube w hw
  have hcoef : 0 ≤ 𝔊 :=
    div_nonneg (mul_nonneg 𝘑₂
      $ mul_nonneg  𝖠₄  C.holderBound_pos.le ) $ Nat.cast_nonneg _
  constructor
  · have hdist := euclideanNorm_le_coordinate_radius 𝔏
       𝘷⁻¹  𝖠₃  $ 𝔑 dyadicCellAffine_radius w hx hw
    apply (herr _ hy).trans
    apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hdist C.smoothness_pos.le) hcoef).trans_eq
    rw [Real.mul_rpow (Real.sqrt_nonneg _) 𝖠₃ ]
    unfold taylorErrorFactor
    ring
  · convert herr _ hy using 1
    rw [dyadicCellAffine_euclidean_distance, Real.mul_rpow  𝖠₃ 
      $ by unfold euclideanNorm; positivity ]
    ring
