module

public import NearlyMinimax.PilotMean


@[expose] public section

/-! Centered independent pilot fields give the exact deterministic population
mean, as well as genuine L² integrability of the bilinear pilot mean. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

variable {m : W → H} (hmm : Measurable m) (hm : MemLp m 2 M) {η : Ω → W → H}
    (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M)) (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2)) {C lam : ℝ} (hC : 0 ≤ C)
    (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C) (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    (htest : ∀ v : W → H, MemLp v 2 M → (∫ x, test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
include hmη hη hmB hbound

include hcenter hC hlam htest in
theorem fluctuation_mean_zero
    {v₁ v₂ : W → H} (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
    (∫ z, fluctuation (M := M) η B v₁ v₂ z ∂μ.prod μ) = 0 := by
  have h₁ := (test_memLp_two hη hv₁).integrable (by norm_num)
  have h₂ := (test_memLp_two hη hv₂).integrable (by norm_num)
  have ha := integral_add ((h₁.comp_fst μ).add (h₂.comp_snd μ)) ((bilinear_memLp_two hmη hη hmB hC hlam hbound htest).integrable (by norm_num))
  have hb := integral_add (h₁.comp_fst μ) (h₂.comp_snd μ)
  simp at ha hb
  change (∫ z, test η v₁ z.1 + test η v₂ z.2 +
    bilinear η B z ∂μ.prod μ) = 0
  rw [ha, hb, integral_fun_fst, integral_fun_snd,
    test_mean_zero hη hcenter hv₁, test_mean_zero hη hcenter hv₂,
    bilinear_mean_zero hmη hη hcenter hmB hC hlam hbound htest]
  simp

include hmm hm hsym in
theorem pilotMean_eq_fluctuation_ae :
    pilotMean (M := M) m η B =ᵐ[μ.prod μ]
      (fun z => fluctuation (M := M) η B (fun w => B w (m w))
        (fun w => B w (m w)) z + ∫ w, ⟪m w, B w (m w)⟫ ∂M) := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (memLp_sections hη),
    (Measure.quasiMeasurePreserving_snd).ae (memLp_sections hη)] with z hx hy
  linarith [pilotMean_sub_eq hmm hm hmη hmB hbound hsym hx hy]

include hmm hm hC hlam hsym htest in
theorem pilotMean_memLp_two :
    MemLp (pilotMean (M := M) m η B) 2 (μ.prod μ) := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  exact ((fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hBm hBm).add
    (memLp_const (∫ w, ⟪m w, B w (m w)⟫ ∂M))).ae_eq
      (pilotMean_eq_fluctuation_ae hmm hm hmη hη hmB hbound hsym).symm

include hmm hm hcenter hC hlam hsym htest in
theorem pilotMean_mean_eq :
    (∫ z, pilotMean (M := M) m η B z ∂μ.prod μ) = ∫ w, ⟪m w, B w (m w)⟫ ∂M := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  rw [integral_congr_ae (pilotMean_eq_fluctuation_ae hmm hm hmη hη hmB hbound hsym), integral_add ((fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hBm hBm).integrable
    (by norm_num)) (integrable_const _),
    fluctuation_mean_zero hmη hη hcenter hmB hC hlam hbound htest hBm hBm]
  simp

end NearlyMinimax.PilotFields
