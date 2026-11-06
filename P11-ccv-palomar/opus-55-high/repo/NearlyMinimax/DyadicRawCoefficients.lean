module

public import NearlyMinimax.PilotCommonBounds
public import NearlyMinimax.PopulationPilotCoefficients
public import NearlyMinimax.TwoScalarPilotVector
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual coefficient estimator is Borel and independent of the
unknown regression, density, and variance. Its exact population-plus-noise
decomposition is proved by polynomial algebra. -/
open MeasureTheory Matrix
𝚪
𝚨
𝚭
𝚩

𝗇 𝔅 Fin n → Ω → 𝗓
def polynomialLiftLinearMap
    (X : 𝔅) (z : Ω) : 𝙩₁ →ₗ[ℝ] ℝ where
  toFun P := Finsupp.linearCombination ℝ (fun α =>
    RoughRegime.Upper.monomialLift (RoughRegime.Upper.exponentCoordinates α) X z) P.coeff
  map_add' P Q := by simp only [AddMonoidAlgebra.coeff_add, map_add]
  map_smul' a P := by simp only [AddMonoidAlgebra.coeff_smul, map_smul, RingHom.id_apply]

theorem polynomialLiftLinearMap_apply
    (X : 𝔅) z P :
    polynomialLiftLinearMap X z P = RoughRegime.Upper.polynomialLift P X z := by
  rfl

theorem polynomialLift_joint_measurable [MeasurableSpace Ω]
    (P : 𝙩₁) (X : 𝔅)
    (hX : 𝘫₁) :
    Measurable $ RoughRegime.Upper.polynomialLift P X := by
  classical
  apply Finset.measurable_sum
  intro α _
  apply Measurable.const_mul
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e _
  exact Finset.measurable_prod Finset.univ fun i _ => (hX $ e i ).eval

theorem rowIncrementPolynomial_lift
    a b T y m
    (row : 𝗢)
    (X : Fin n → Ω → 𝚕 → ℝ) z :
    RoughRegime.Upper.polynomialLift (rowIncrementPolynomial r a b T y m row) X z =
      ∑ i, row i * RoughRegime.Upper.polynomialLift (incrementFinPolynomial r a b T y m i) X z := by
  simp only [← polynomialLiftLinearMap_apply, rowIncrementPolynomial, ← MvPolynomial.smul_eq_C_mul,
    map_sum, map_smul, smul_eq_mul]

attribute [local irreducible] dyadicIncrementRawVector

𝗇 𝔍 𝙌
𝗇 𝔒 𝙩
𝗇 𝔄 𝔍 × 𝔒
𝗃 𝔔 ἀ (d := d) (ℓ := C.order) j
𝗇 𝔇 𝔔 dyadicIncrementRawVector t.2.1 $ t.1 i
𝗇 𝔈 𝗣
𝗇 𝔉 𝔒
𝗇 𝔊 dyadicPolynomialPilot C n j t.2.1 y m (row t.2) t.1
𝗇 𝔎 fun t : 𝔄 => 𝔊
𝗇 𝔑 Fintype.card $ incrementVariables 𝔈
set_option backward.isDefEq.respectTransparency true in
theorem dyadicPolynomialPilot_raw_joint_measurable (C : ModelConstants d)
    (n j : ℕ) (y : ℝ) (m : ℕ)
    (row : 𝔉 → Fin 𝔈 → ℝ)
    (hrow : Measurable row) :
    Measurable 𝔎 := by
  have hX (i : Fin n) : Measurable fun t : 𝔄 =>
      𝔇 := by
    have hmarg : Measurable fun t : 𝔄 =>
        (t.2.1, t.1 i) :=
       (measurable_fst.comp measurable_snd).prodMk $ 𝘜 measurable_fst
    exact (𝔔 dyadicIncrementRawVector_joint_measurable).comp hmarg
  let X : Fin n → 𝔄 →
      Fin 𝔑 → ℝ :=
    fun i t => 𝔇
  have heq : 𝔎 =
       fun t => ∑ i, row t.2 i * RoughRegime.Upper.polynomialLift
        (incrementFinPolynomial 𝔈 C.densityLower C.densityUpper
          𝖼₁ y m i) X t := by
    funext t
    simp only [dyadicPolynomialPilot, rowIncrementPolynomial_lift]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact ((hrow.eval (a := i)).comp measurable_snd).mul
    $ polynomialLift_joint_measurable (n := n)
      (p := 𝔑) _ X hX

def dyadicRawPilotSum (C : ModelConstants d) (n J : ℕ) (m : 𝙦₁)
    (y : ℝ) (z : 𝔍) (w : 𝔉) : ℝ :=
  ∑ j : Fin 𝗯, dyadicPolynomialPilot C n j.val w.1 y (m j.val)
    (dyadicPilotRow j.val w.1 w.2) z

𝗃 𝔓 ἀ C n J m
𝗇 𝔏 𝔓 dyadicRawPilotSum
def dyadicRawCoefficients (C : ModelConstants d) (n J : ℕ) (m : 𝙦₁)
    (z : 𝔍) (w : 𝔉) : PairVector :=
  WithLp.toLp 2 ![1, -1 + (𝔏 0 z w - 𝔏 1 z w),
    -𝔏 0 z w]

𝗇 𝔐 dyadicMultilevelErrorField C θ n J
def dyadicNoiseCoefficients (C : ModelConstants d) (θ : RegressionParameter d)
    (n J : ℕ) (m : 𝙦₁) (z : 𝔍) (w : 𝔉) : PairVector :=
  twoScalarPilotVector (𝔐 0 m z w)
    $ 𝔐 1 m z w

theorem dyadicRawPilotSum_joint_measurable C
    n J m y :
    Measurable fun t : 𝔄 =>
      𝔏 y t.1 t.2 :=
  Finset.measurable_sum Finset.univ fun j _ =>
    dyadicPolynomialPilot_raw_joint_measurable C n j.val y (m j.val)
      (fun w => dyadicPilotRow j.val w.1 w.2) $ dyadicPilotRow_field_measurable j.val

theorem dyadicRawCoefficients_joint_measurable C
    n J m :
    Measurable fun t : 𝔄 =>
      𝔓 dyadicRawCoefficients t.1 t.2 := by
  have h0 := 𝔓 dyadicRawPilotSum_joint_measurable 0
  apply (PiLp.continuous_toLp 2 𝚟).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_const
  · exact measurable_const.add $ h0.sub $ 𝔓 dyadicRawPilotSum_joint_measurable 1
  · exact h0.neg

theorem dyadicMultilevelErrorField_eq_raw_sub_population C
    (θ : RegressionParameter d) n J m y
    z w :
    𝔐 y m z w = 𝔏 y z w -
      (dyadicPopulationPilotSum C θ J m false w - y * dyadicPopulationPilotSum C θ J m true w) := by
  unfold dyadicMultilevelErrorField dyadicPilotErrorField dyadicRawPilotSum
  rw [Finset.sum_sub_distrib]
  congr 1
  unfold dyadicPopulationPilotSum
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [incrementFinScalar, incrementFinVector_affine]
  aesop

theorem dyadicRawCoefficients_eq_population_add_noise C
    (θ : RegressionParameter d) n J m
    z w :
    𝔓 dyadicRawCoefficients z w = 𝘺₁ w +
      dyadicNoiseCoefficients C θ n J m z w := by
  ext i
  fin_cases i <;>
    simp [dyadicRawCoefficients, dyadicPopulationCoefficients, dyadicNoiseCoefficients,
      twoScalarPilotVector_coordinates, dyadicMultilevelErrorField_eq_raw_sub_population] <;> ring
