module

public import NearlyMinimax.MaskedPilotKernel
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Pilot fields need L² bounds only where the pair mask is nonzero. -/
𝚯
𝚻
namespace NearlyMinimax.PilotFields
𝚩

𝛖
𝛓
𝛌
variable {μ : Measure Ω} {ν : Measure W} [IsProbabilityMeasure μ] [SFinite ν]

𝗇 𝔈 𝙟₂
𝗇 𝔓 q w = 0
def restrictPilotField (c : 𝔈) (q : W → ℝ) (x : Ω) (w : W) : H :=
  if 𝔓 then 0 else c x w

𝗃 𝔖 fun z : Ω × W => ἀ z.1 z.2
𝗇 𝔇 Measurable 𝔖 c
𝗇 𝔏 restrictPilotField c q
theorem restrictPilotField_measurable {c : 𝔈}
    (hmc : 𝔇)
    {q } (hmq : Measurable q) :
    Measurable 𝔖 𝔏 :=
  Measurable.ite ( hmq.comp measurable_snd $ measurableSet_singleton 0 )
    measurable_const hmc

𝗃 𝔗 MemLp (fun x => ἀ x w) 2 μ
𝗇 𝔅 ∀ᵐ w ∂ν, q w ≠ 0 → 𝔗 c
theorem restrictPilotField_memLp {c : 𝔈} {q }
    (hc : 𝔅) :
    ∀ᵐ w ∂ν, 𝔗 𝔏 := by
  filter_upwards [hc] with w hw
  by_cases hq : 𝔓
  · simpa [restrictPilotField, hq] using
       memLp_const 0
  · simpa [restrictPilotField, hq] using hw hq

𝗃 𝔔 ∫ x, ‖ἀ x w‖ ^ 2 ∂μ ≤ L
𝗇 𝔄 ∀ᵐ w ∂ν, q w ≠ 0 → 𝔔 c
theorem restrictPilotField_energy_le {c : 𝔈} {q } {L } (hL : 𝘨)
    (hE : 𝔄) :
    ∀ᵐ w ∂ν, 𝔔 𝔏 := by
  filter_upwards [hE] with w hw
  by_cases hq : 𝔓
  · simpa [restrictPilotField, hq] using hL
  · simpa [restrictPilotField, hq] using hw hq

𝗇 𝔐 maskedPilotKernel c A q
theorem maskedPilotKernel_restrict_eq (c : 𝔈) A
    q : maskedPilotKernel 𝔏 A q = 𝔐 := by
  funext z
  by_cases hq : q z.2 = 0 <;> simp [maskedPilotKernel, restrictPilotField, hq]

𝗇 𝔉 𝘬₂
𝗇 𝔊 𝘤₁
𝗇 𝔍 ∀ w, q w ^ 2 = q w
𝗃 𝔎 ἀ (restrictPilotField_measurable hmc hmq) hmA hmq hq hA (restrictPilotField_memLp hc) hL $ restrictPilotField_energy_le hL hE
𝗇 𝔑 Integrable (fun w => 𝔉) ν
𝗇 𝔒 𝖳₁ ν
theorem maskedPilotKernel_memLp_of_supported_sections {c }
    (hmc : 𝔇)
    {A } (hmA : Measurable 𝔊)
    {q } (hmq : Measurable q) (hq : 𝔍)
    (hA : 𝔑)
    (hc : 𝔅)
    {L } (hL : 𝘨) (hE : 𝔄) :
    MemLp 𝔐 2 𝔒 := by
  rw [← maskedPilotKernel_restrict_eq c A q]
  exact 𝔎 maskedPilotKernel_memLp

theorem maskedPilotKernel_energy_le_of_supported_sections {c }
    (hmc : 𝔇)
    {A } (hmA : Measurable 𝔊)
    {q } (hmq : Measurable q) (hq : 𝔍)
    (hA : 𝔑)
    (hc : 𝔅)
    {L } (hL : 𝘨) (hE : 𝔄) :
     ∫ z, 𝔐 z ^ 2 ∂𝔒 ≤
      𝖱₂ * ∫ w, 𝔉 ∂ν := by
  rw [← maskedPilotKernel_restrict_eq c A q]
  exact 𝔎 maskedPilotKernel_energy_le
