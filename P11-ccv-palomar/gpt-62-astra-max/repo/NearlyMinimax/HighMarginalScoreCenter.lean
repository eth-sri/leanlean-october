module

public import NearlyMinimax.HighMarginalScoreDerivative


@[expose] public section

/-! Genuine observed-data score centering follows from the proved derivative
identity and actual probability normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hlabels : DegreeAtMost dependent Δ) {T Ba : ℝ} (hBa : 0 ≤ Ba) {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {π : Measure E} [IsProbabilityMeasure π] {activation : E → ℝ}
    (hactivation : Measurable activation) (hcenter : ∫ e, activation e ∂π = 0)
    (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ historyActivityRadius Δ) {d : ℕ} (n : ℕ)
    {a v η aRaw bRaw : ℝ} (ha : 0 < a) (haRaw : 0 < aRaw)
    {p F : HistoryMarked dependent E → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T, (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) = (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
include hBa ha haRaw habound hactivation hcenter hlabels hmass hq hraw hsmall hΔ

theorem historyMarkedPrior_dataScore_centered
    {t : ℝ} (ht : 0 < t) (htT : t < T) :
    (∫ z, highMarginalRealScore
      (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
      ∂(highRealSampleKernel n a (v - η^2*t) hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n)) = 0 := by
  have hd := historyMarkedPrior_dataMean_score_hasDerivAt hΔ hlabels hBa hactivation hcenter habound hsmall (n := n) ha haRaw hp hF
    hraw hq hmass (H := (fun _ => 1)) measurable_const 1 (by norm_num) (fun _ => by norm_num) ht htT
  have he : (fun u => ∫ z, (1 : ℝ) ∂(highRealSampleKernel n a (v - η^2*u) hp hF) ∘ₘ
      (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
        (fun ω => highRawDensityMass (p ω)) n)) =ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [Ioo_mem_nhds ht htT] with u hu
    have hs  :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    let _ := historyMarkedPrior_probability hΔ hlabels hu.1.le hBa (by
      apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
      solve_by_elim [Eventually.of_forall]) hcenter habound hs
    have hb (ω)  :=
      highRawDensityMass_mem_Icc hp.of_uncurry_left haRaw
        (Eventually.of_forall (hraw ω))
    let _ := massPowerTilt_isProbability (historyMarkedPrior dependent Δ u π activation) (highRawDensityMass_joint_measurable hp) n haRaw hb
    let _ := highRealSampleKernel_markov n a (v - η^2*u) hp hF haRaw hraw ha.ne'
      (fun ω x y => (hq u ⟨hu.1.le,hu.2.le⟩ ω x y).le)
    simp
  simpa using hd.unique ((hasDerivAt_const t 1).congr_of_eventuallyEq he)

theorem historyMarkedPrior_dataScore_centered_ae
    : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      (∫ z, highMarginalRealScore
        (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
        ∂(highRealSampleKernel n a (v - η^2*t) hp hF) ∘ₘ
          (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
            (fun ω => highRawDensityMass (p ω)) n)) = 0 := by
  have h0 : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by simp [ae_iff]
  have hT : ∀ᵐ t ∂volume, t ≠ T := by simp [ae_iff]
  filter_upwards [h0, hT] with t ht0 htT
  intro ht
  exact historyMarkedPrior_dataScore_centered hΔ hlabels hBa hactivation hcenter habound hsmall n ha haRaw hp hF
    hraw hq hmass (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htT)

end NearlyMinimax
