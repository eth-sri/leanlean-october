module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.AliasTailSummation
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual count-two and exterior factorial blocks of the complete source
geometry. Every constant is fixed before the degrees and count cutoff. -/
𝚫
𝚪
𝚨
𝚩
𝚭
𝚬

𝗇 𝔒 𝙉^d
def completeGeometryExteriorConstant (d : ℕ) (Cs Chi : ℝ) : ℝ :=
  max 1 $ Cs * (3*𝔒*Chi^2)

𝗇 𝔇 completeGeometryExteriorConstant d Cs Chi
theorem completeGeometryExteriorConstant_ge_one d Cs Chi :
    1 ≤ 𝔇 := le_max_left ..

theorem completeGeometryExteriorConstant_pos d Cs Chi :
    0 < 𝔇 :=
  zero_lt_one.trans_le $ completeGeometryExteriorConstant_ge_one d Cs Chi

𝗃 𝔔 ἀ D M R q aD bD c0 ell N mu C a rho eta Chi Bl
𝗇 𝔅 𝔔 completeSourceGeometryEnvelope
𝗇 𝔉 (Bl+1)^2
𝗇 𝔐 𝗸
theorem completeSourceGeometryEnvelope_exterior_integral_of_three_le
    D M R q n (h3 : 𝖬₂) (hn : D < n)
    aD bD c0 ell N mu C a rho eta Chi Bl :
     ∫ U, 𝔅 n U
      ∂𝖮₁ = (3*𝖥*Chi^2)^n*𝔐*𝔉 := by
  rcases n with _|_|_|n
  · omega
  · omega
  · omega
  · exact completeSourceGeometryEnvelope_exterior_integral D M R q n
      aD bD c0 ell N mu C a rho eta Chi Bl hn

𝗇 𝔄 D+1+j
𝗇 𝔊 Cs*B*mu
𝗇 𝔍 𝖫₂
𝗇 𝔎 D+1
𝗇 𝔏 ∫ U, 𝔅 𝔄 U ∂fullSpatialPatchDesign d 𝔄
𝗇 𝔓 B^𝔄*P
/-- The true exterior integrals, including response and spatial volume,
give the source factorial tail with its fixed exponential constant. -/
theorem completeSourceGeometryEnvelope_exterior_factorial_le
    D M R q J (hD : 2 ≤ D) aD bD c0 ell N mu C a rho eta Chi Bl Cs
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : 𝗦₁) :
     ∑ j ∈ Finset.range J, poissonCountWeight 𝔍 𝔄 *
      𝔏 ≤
      Real.exp 𝔇 * 𝔐*𝔉 *
        poissonCountWeight (𝔇*mu) 𝔎 := by
  let B := 3*𝗝*Chi^2
  let P := 𝔐*𝔉
  let ch := 𝔇
  have hP : 𝚏 := 𝖠₃
  have hbase : Cs*B ≤ ch := le_max_right ..
  have heq (j : ℕ) :
      𝔏 =
      𝔓 := by
    have h := completeSourceGeometryEnvelope_exterior_integral_of_three_le (d := d) D M R q 𝔄
       𝖡₃   𝖡₃  aD bD c0 ell N mu C a rho eta Chi Bl
    linarith
  simp_rw [heq]
  have hterm (j : ℕ) : poissonCountWeight 𝔍 𝔄 * 𝔓 =
      P * poissonCountWeight 𝔊 𝔄 := by
    unfold poissonCountWeight
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have ht := finite_poissonCountWeight_tail_le (by positivity : 0 ≤ 𝔊) 𝔎 J
  have hexp : Real.exp 𝔊 ≤ Real.exp ch := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_of_le_one_right (mul_nonneg hCs 𝖠₃ ) hmu1).trans hbase
  have hweight := poissonCountWeight_mono  𝖠₃ 
    (mul_le_mul_of_nonneg_right hbase hmu) 𝔎
  have h := mul_le_mul hexp hweight (poissonCountWeight_nonneg  𝖠₃  _)
    (Real.exp_pos ch).le
  nlinarith

𝗇 𝔈 ((2*rho+a)/𝗅)^4
def completeGeometryRadialConstant (d : ℕ) (B a rho Cs : ℝ) : ℝ :=
  27*Cs^2*B^4*𝔈*𝔒*spatialExponentialConstant d

𝗇 𝔑 bD-𝖧⁻¹
/-- The actual pair envelope integrates the genuine radial defect. Its
count-two Poisson factor yields `η⁴ μ² N⁻ᵈ` with a fixed density-upper cap. -/
theorem completeSourceGeometryEnvelope_pair_factorial_le
    (D M R q : ℕ) aD bD c0 ell N mu C a rho eta Chi Bl Cs B
    (hd : 𝗆) (hN : 𝘹) (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu)
    (hbd : 0 ≤ 𝔑) (hbdB : 𝔑 ≤ B) :
    poissonCountWeight 𝔍 2 *
       ∫ U, 𝔅 2 U ∂𝗿₂ ≤
      completeGeometryRadialConstant d B a rho Cs * 𝔐*𝙺₁*N^(-𝙊) := by
  have hi := 𝔔 completeSourceGeometryEnvelope_pair_integral_le hd hN
  apply (mul_le_mul_of_nonneg_left hi $ poissonCountWeight_nonneg (mul_nonneg hCs hmu) 2 ).trans
  let K := 27*Cs^2*𝔈*𝖥*spatialExponentialConstant d *
    𝔐*𝙺₁/𝚝₂
  have hK : 𝖭₂ := by
    have := spatialExponentialConstant_nonneg d
    positivity
  rw [Real.rpow_neg hN.le, Real.rpow_natCast]
  convert mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbd hbdB 4) hK using 1 <;> simp only [poissonCountWeight, finePairCountTwoSpatialBudget, completeGeometryRadialConstant]
    <;> dsimp [K] <;> norm_num only [Nat.factorial, Nat.cast_ofNat] <;> ring
