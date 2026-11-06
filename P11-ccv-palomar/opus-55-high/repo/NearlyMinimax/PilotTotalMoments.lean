module

public import NearlyMinimax.PilotSectionMoments
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The full coefficient pilot uses only the centered pilot second moment. -/
𝚯
namespace NearlyMinimax.PilotFields
𝚩

𝗇 𝔄 2 * 𝘌₂ ^ 2
theorem norm_add_sq_le_twice {H } [NormedAddCommGroup H] (u v : H) :
    ‖u + v‖ ^ 2 ≤ 𝔄 + 2 * 𝚡₁ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg $ u + v ) (norm_add_le u v) 2
  nlinarith [sq_nonneg $ 𝘌₂ - 𝚡₁ ]

theorem pilot_coefficient_memLp_two {Ω H } [MeasurableSpace Ω]
    [NormedAddCommGroup H] {μ : Measure Ω} [IsProbabilityMeasure μ]
    u {η : Ω → H} (hη : MemLp η 2 μ) :
    MemLp (fun x => u + η x) 2 μ := (memLp_const u).add hη

𝗇 𝔅 ∫ x, ‖η x‖ ^ 2 ∂μ
theorem pilot_coefficient_second_moment_le {Ω H } [MeasurableSpace Ω]
    [NormedAddCommGroup H] {μ : Measure Ω} [IsProbabilityMeasure μ]
    u {η : Ω → H} (hη : MemLp η 2 μ) {C R }
    (hC : 𝖺₁) (hu : 𝘌₂ ≤ C) (hE : 𝔅 ≤ R) :
     ∫ x, ‖u + η x‖ ^ 2 ∂μ ≤ 𝘖 + 2 * R := by
  have hηi := hη.norm.integrable_sq
  calc
    _ ≤ ∫ x, 𝔄 + 2 * ‖η x‖ ^ 2 ∂μ := integral_mono (pilot_coefficient_memLp_two u hη).norm.integrable_sq ((integrable_const _).add $ hηi.const_mul 2 )
         fun x => norm_add_sq_le_twice u $ η x
    _ = 𝔄 + 2 * 𝔅 := by
      rw [𝖻₁ $ hηi.const_mul 2 ]
      rw [integral_const, integral_const_mul]
      simp
    𝖦 := by
      bound
