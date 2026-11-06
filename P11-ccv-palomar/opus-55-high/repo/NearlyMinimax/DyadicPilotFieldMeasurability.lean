module

public import NearlyMinimax.IncrementKernelMeasurability
public import NearlyMinimax.DyadicPilotRows
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Joint Borel measurability of the actual centered polynomial pilot,
obtained from its exact finite factorial-kernel expansion. -/
𝚯
𝚪
𝚨
𝚭
𝚩

𝗇 𝔅 𝗙₁
𝗇 𝔈 𝗓
theorem centeredKernelExpansion_field_measurable
    [MeasurableSpace Ω] [MeasurableSpace W]
    (H : W → (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ : Fin 𝔅 => 𝔈) ℝ)
    (hH : ∀ r, Measurable fun w => H w r )
    (X : Fin n → Ω → 𝔈) (hX : 𝘫₁) :
    Measurable fun t : 𝗶₁ => LiftL2.centeredKernelExpansion 0 (H t.2) X t.1 := by
  classical
  unfold LiftL2.centeredKernelExpansion LiftL2.kernelStatistic LiftL2.kernelSum
  simp
  apply Finset.measurable_sum
  intro r _
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e _
  have hmH : Measurable fun t : 𝗶₁ => H t.2 r := (hH r).comp measurable_snd
  have heval : Continuous fun t :
      ContinuousMultilinearMap ℝ (fun _ => 𝔈) ℝ ×
        (Fin 𝔅 → 𝔈) => t.1 t.2 := continuous_eval
  exact heval.measurable.comp $ hmH.prodMk $ measurable_pi_iff.mpr fun i => (hX $ e i ).comp measurable_fst

𝗃 𝔍 ἀ d C.order
𝗇 𝔄 dyadicPolynomialPilot C n j t.2.1 y m (row t.2) t.1 - incrementFinScalar 𝔍 anchoredDimension C.densityLower C.densityUpper 𝔍 anchoredFinTransport y m (row t.2) (dyadicIncrementRawMean θ j t.2.1)
𝗇 𝔊 𝙌
𝗇 𝔇 𝔊 × 𝙩
𝗇 𝔉 m + 𝔍 anchoredDimension + 1
theorem dyadicPolynomialPilot_centered_field_measurable (C : ModelConstants d)
    [Nonempty 𝔍 AnchoredIndex] θ (hθ : 𝙟)
    n j y m
    row
    (hrow : Measurable row) (hdegree : 𝔉 ≤ n) :
    Measurable fun t : 𝔇 =>
      𝔄 := by
  let R := 𝔉
  let H w (r : Fin R) :=
    𝖳₂ w.1 y m (row w) 𝔅
  have hH (r : Fin R) :=
    dyadicIncrementKernel_field_measurable C θ hθ j y m 𝔅 row hrow
  have hX i : Measurable fun z : 𝔊 =>
      incrementGlobalVector (ℓ := C.order) j (z i) - 𝚆₁ :=
    ((incrementGlobalVector_measurable j).comp $ measurable_pi_apply i ).sub measurable_const
  have h := centeredKernelExpansion_field_measurable H hH _ hX
  have heq : (fun t : 𝔇 =>
      LiftL2.centeredKernelExpansion 0 (H t.2)
        (fun i z => 𝗤₁ - 𝚆₁) t.1) =
       fun t => 𝔄 := by
    funext t
    exact dyadicPolynomialPilot_centered_global C θ hθ n j t.2.1 y m (row t.2) hdegree t.1
  simp_all
