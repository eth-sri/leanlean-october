module

public import NearlyMinimax.HighRawScoreEnergy
public import NearlyMinimax.HighMarkedMeasurable
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine conditional finite-response energies determine square
integrability and Fisher energy in the actual normalized sample kernel.
No joint-score integrability assumption is supplied. -/
𝚵
𝚳
𝚨
𝚩
𝚱

𝗇 𝔇 𝚅₁
𝗇 𝔉 S 𝖮
𝗇 𝔊 𝙈
def finiteResponseSquareEnergy [MeasurableSpace α] (n : ℕ)
    (a V : ℝ) (F : 𝘬) (S : 𝔇 × 𝔊 → ℝ)
    (x : 𝔇) : ℝ :=
  ∑ y : 𝔊, (∏ i, ternaryMass a (F $ x i ) V (y i)) * 𝔉 ^ 2

𝗃 𝔍 ἀ n a V F
𝗇 𝔄 𝔍 responseSampleIndexKernel hF
𝗇 𝔅 𝔍 finiteResponseSquareEnergy S
𝗇 𝔈 fun z => 𝖩₂
theorem response_sample_square_integrable_integral [MeasurableSpace α]
    (n : ℕ) (μ : Measure 𝔇) [SFinite μ] a V (ha : 𝙞)
    F hF (hq : 𝗨)
    S (hS : Measurable S)
    (hE : Integrable 𝔅 μ) :
    Integrable 𝔈 (μ.compProd 𝔄) ∧
     ∫ z, 𝖩₂ ∂μ.compProd 𝔄 =
      ∫ x, 𝔅 x ∂μ := by
  let _ := 𝔍 responseSampleIndexKernel_markov hF ha hq
  have he x : ∫ y, ‖𝔉 ^ 2‖ ∂𝔄 x =
      𝔅 x := by
    simp_rw [Real.norm_eq_abs, abs_sq]
    exact 𝔍 responseSampleIndexKernel_integral hF x (fun i y => hq (x i) y) _
  have hi : Integrable 𝔈 $ μ.compProd 𝔄 := by
    apply (Measure.integrable_compProd_iff (hS.pow_const 2).aestronglyMeasurable).mpr
    simp_all
  rw [Measure.integral_compProd hi]
  simp_all
