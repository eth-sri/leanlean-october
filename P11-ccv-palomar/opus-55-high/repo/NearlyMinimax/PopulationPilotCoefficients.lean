module

public import NearlyMinimax.PopulationPilotMeans
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Original multiscale mean coefficient vector, its uniform cap, Borel
measurability, and exact residual identity. -/

𝛎
open scoped RealInnerProductSpace BigOperators Matrix.Norms.L2Operator
𝚨
𝚭
𝚩

𝗇 𝔄 𝗯
𝗃 𝔒 ἀ C θ
def dyadicPopulationPilotSum (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : 𝙦₁) (t : Bool) (w : 𝙩) : ℝ :=
  ∑ j ∈ Finset.range 𝔄,
    dyadicPilotRow j w.1 w.2 ⬝ᵥ 𝔒 dyadicPopulationRawPolynomial j w.1 t (m j)

𝗇 𝔅 𝔒 dyadicPopulationPilotSum J m
def dyadicPopulationCoefficients (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : 𝙦₁) (w : 𝙩) : PairVector :=
  WithLp.toLp 2 ![1, -1 + 𝔅 true w,
    -𝔅 false w]

theorem finite_row_abs_dot_le_pi_norm [Fintype ι] (row v : 𝙛) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * 𝚡₁ := by
  apply 𝘡
  calc
     ∑ i, |row i * v i| ≤ ∑ i, |row i| * 𝚡₁ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        $ abs_nonneg _
    𝘿 := by rw [Finset.sum_mul]

𝗇 𝔉 ∑ j ∈ Finset.range 𝔄, 𝗜
theorem dyadic_geometric_sum_le J :
    𝔉 ≤ 𝙉 ^ 𝔄 := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, pow_succ _ 𝔄]
    linarith

𝗇 𝔊 𝚃
𝗇 𝔐 𝖵₂⁻¹
𝗇 𝔇 𝔊 * Real.sqrt d * 𝔐
theorem dyadicPilotRow_total_abs_le J x y
    (hx : 𝗌) (hy : y ∈ unitCube d) (hc : y ∈ dyadicPilotCell J x) :
     ∑ j ∈ Finset.range 𝔄, ∑ i, |dyadicPilotRow (ℓ := ℓ) j x y i| ≤
      2 * 𝔊 * Real.sqrt d := by
  calc
    _ ≤ ∑ j ∈ Finset.range 𝔄,
      𝔊 * 𝗜 * Real.sqrt d * 𝔐 := by
      apply Finset.sum_le_sum
      intro j hj
      exact dyadicPilotRow_sum_abs_le_fine_cell j J (Nat.le_of_lt_succ $ Finset.mem_range.mp hj ) x y hx hy hc
    _ = 𝔇 *
      𝔉 := by
      rw [Finset.mul_sum]
      ring
    _ ≤ 𝔇 * 2 ^ 𝔄 :=
      mul_le_mul_of_nonneg_left (dyadic_geometric_sum_le J) 𝖠₃
    𝘿 := by rw [pow_succ]; field_simp

𝗇 𝔈 𝖮
𝗇 𝔍 𝔒 dyadicPopulationResidual J m x y
𝗇 𝔎 𝔒 dyadicPopulationCoefficients J m
theorem dyadicPopulationCoefficients_residual C
    θ J m (x y : Covariate d) :
    ⟪𝔎 𝔈, pairResponseVector (θ.regression x) $ θ.regression y ⟫ =
      𝔍 := by
  have hsum : ∑ j ∈ Finset.range 𝔄,
      dyadicPilotRow j x y ⬝ᵥ 𝔒 dyadicPopulationPolynomial j x (θ.regression x) (m j) =
      𝔅 false 𝔈 -
        θ.regression x * 𝔅 true 𝔈 := by
    simp only [dyadicPopulationPolynomial_affine, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      Finset.sum_sub_distrib, dyadicPopulationPilotSum]
    rw [Finset.mul_sum]
  rw [pairResponseVector_inner]
  change 1 * θ.regression y + (-1 + 𝔅 true 𝔈) * θ.regression x +
     -𝔅 false 𝔈 = 𝔍
  unfold dyadicPopulationResidual
  linarith

section

variable (C)
    (θ : RegressionParameter d)
    (hθ : 𝔒 Admissible)

include hθ

𝗇 𝔏 𝗣
theorem dyadicPopulationRawPolynomial_measurable j t m :
    Measurable fun x => 𝔒 dyadicPopulationRawPolynomial j x t m := by
  apply measurable_pi_iff.mpr
  intro i
  exact (MvPolynomial.continuous_eval $ MvPolynomial.rename
    (Fintype.equivFin $ incrementVariables 𝔏 )
      $ rawIncrementEntryPolynomial 𝔏 C.densityLower C.densityUpper
        𝖼₁ t m i ).measurable.comp
      $ 𝔒 dyadicIncrementRawMean_measurable hθ j

theorem dyadicPopulationPilotSum_measurable J m t :
    Measurable $ 𝔅 t := by
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro i _
  exact (dyadicAnchoredFeature_joint_measurable j $ anchoredFinIndex i ).mul
    $ ((𝔒 dyadicPopulationRawPolynomial_measurable hθ j t $ m j ).eval ).comp measurable_fst

theorem dyadicPopulationCoefficients_measurable J m :
    Measurable 𝔎 := by
  apply (PiLp.continuous_toLp 2 𝚟).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_const
  · exact measurable_const.add $ 𝔒 dyadicPopulationPilotSum_measurable hθ J m true
  · exact (𝔒 dyadicPopulationPilotSum_measurable hθ J m false).neg
