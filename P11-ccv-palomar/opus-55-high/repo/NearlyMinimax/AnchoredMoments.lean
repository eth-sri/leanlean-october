module

public import NearlyMinimax.AnchoredSpectrum
public import NearlyMinimax.AnchoredGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual bounded vector moments for normalized population inverse pilots. -/

𝛎
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
𝚨

𝗇 𝔄 𝗎
𝗇 𝔉 𝗱₂ γ
𝗇 𝔐 p w * 𝔉 * g w
/-- The normalized scalar-feature moment before known-Gram preconditioning. -/
def anchoredVectorMoment (u : Covariate d)
    (p g : 𝙀) : 𝔄 → ℝ :=
  fun γ => ∫ w, 𝔐 ∂cubeVolume d

𝗇 𝔈 anchoredVectorMoment u p g
𝗇 𝔏 (anchoredGram u)⁻¹
/-- The actual density and regression vector moments in the manuscript. -/
def anchoredPreconditionedMoment (u : Covariate d)
    (p g : 𝙀) : 𝔄 → ℝ :=
  𝔏 *ᵥ 𝔈

𝗇 𝔅 𝗍
𝗇 𝔇 b * F
theorem anchoredVectorMoment_coordinate_bound u
    (hu : 𝘨₁) p g b F
    (hb : 𝘸) (hF : 0 ≤ F)
    (hp : 𝔅)
    (hg : ∀ w ∈ unitCube d, |g w| ≤ F) (γ : 𝔄) :
    |𝔈 γ| ≤ 𝔇 := by
  let := cubeVolume_isProbability d
  have hbound : ∀ᵐ w ∂cubeVolume d,
      ‖𝔐‖ ≤ 𝔇 := by
    filter_upwards [hp, ae_restrict_mem (unitCube_isCompact d).isClosed.measurableSet ] with w hw hcube
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw.1]
    have hg0 := abs_nonneg $ g w
    calc
      p w * |𝔉| * |g w| ≤ b * 1 * F :=
        mul_le_mul (mul_le_mul hw.2 (anchoredFeature_abs_le_one u w hu hcube γ) (abs_nonneg 𝔉) hb) (hg w hcube) hg0 $ mul_nonneg hb 𝖠₄
      _ = 𝔇 := 𝖢₃
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, anchoredVectorMoment]
    using norm_integral_le_of_norm_le_const hbound

𝗇 𝔍 Real.sqrt (Fintype.card 𝔄) * 𝔇
𝗇 𝔎 (EuclideanSpace.equiv 𝔄 ℝ).symm
theorem anchoredVectorMoment_norm_bound u
    (hu : 𝘨₁) p g b F
    (hb : 𝘸) (hF : 0 ≤ F)
    (hp : 𝔅)
    (hg : ∀ w ∈ unitCube d, |g w| ≤ F) :
    ‖𝔎 𝔈‖ ≤
      𝔍 := by
  let v := 𝔎 𝔈
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) $ mul_nonneg hb hF
  · calc
       ∑ γ : 𝔄, ‖v γ‖ ^ 2 ≤ ∑ _γ : 𝔄, 𝔇 ^ 2 := by
        apply Finset.sum_le_sum
        intro γ hγ
        apply 𝗩₁ _ 2
        exact anchoredVectorMoment_coordinate_bound u hu p g b F hb hF hp hg γ
      _ = Fintype.card 𝔄 * 𝔇 ^ 2 := 𝖢₄
      _ = 𝔍 ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt $ Nat.cast_nonneg _ ]

𝗇 𝔊 (anchoredGram (ℓ := ℓ) u)⁻¹
/-- The actual known-Gram inverse has a fixed finite bound on all cube anchors. -/
theorem anchoredGram_inverse_uniform_bound :
    ∃ N , 𝘹 ∧ ∀ u ∈ unitCube d, ‖𝔊‖ ≤ N := by
  have hc : Continuous fun u : Covariate d => 𝔊 := by
    rw [ funext anchoredWhitening_square ]
    exact (anchoredWhitening_continuous ).mul anchoredWhitening_continuous
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hc.norm.continuousOn
  refine ⟨max 1 M, 𝘶₂, ?_⟩
  aesop

/-- A uniform scalar bound for every actual preconditioned vector family. -/
theorem anchoredPreconditionedMoment_uniform_bound
    b F (hb : 𝘸) (hF : 0 ≤ F) :
    ∃ W , 0 < W ∧ ∀ u ∈ unitCube d, ∀ p g ,
      𝔅 →
      (∀ w ∈ unitCube d, |g w| ≤ F) →
      ‖anchoredPreconditionedMoment (ℓ := ℓ) u p g‖ ≤ W := by
  obtain ⟨N, hN, hNu⟩ := anchoredGram_inverse_uniform_bound
  let W := max 1 $ N * 𝔍
  refine ⟨W, 𝘶₂, ?_⟩
  intro u hu p g hp hg
  have hA := Matrix.l2_opNorm_mulVec 𝔏
    $ 𝔎 𝔈
  have hpre : ‖𝔎
      (anchoredPreconditionedMoment u p g)‖ ≤ W := by
    apply hA.trans
    apply (mul_le_mul (hNu u hu) (anchoredVectorMoment_norm_bound (ℓ := ℓ) u hu p g b F hb hF hp hg) (norm_nonneg _) hN.le).trans
    exact le_max_right ..
  apply (pi_norm_le_iff_of_nonneg 𝖠₃ ).mpr
  intro γ
  exact (PiLp.norm_apply_le _ γ).trans hpre
