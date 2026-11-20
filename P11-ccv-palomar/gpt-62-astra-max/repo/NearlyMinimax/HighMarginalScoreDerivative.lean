module

public import NearlyMinimax.HighTiltedDataMean


@[expose] public section

/-! Genuine observed-data score derivative for the actual high experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hlabels : DegreeAtMost dependent Δ) {T Ba : ℝ} (hBa : 0 ≤ Ba) {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {π : Measure E} [IsProbabilityMeasure π] {activation : E → ℝ}
    (hactivation : Measurable activation) (hcenter : ∫ e, activation e ∂π = 0)
    (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ historyActivityRadius Δ) {d n : ℕ} {a v η aRaw bRaw : ℝ}
    (ha : 0 < a) (haRaw : 0 < aRaw) {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T, (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) = (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H)
include hΔ hlabels hBa hactivation hcenter habound hsmall

include ha haRaw hraw hq hmass hH in
theorem historyMarkedPrior_dataMean_score_hasDerivAt
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    {t : ℝ} (ht : 0 < t) (htT : t < T) :
    let prior := historyMarkedPrior dependent Δ t π activation
    HasDerivAt (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) hp hF) ∘ₘ
      (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
        (fun ω => highRawDensityMass (p ω)) n))
      (∫ z, H z * highMarginalRealScore
        (prior) π activation n a (v - η^2*t) η p F z
        ∂(highRealSampleKernel n a (v - η^2*t) hp hF) ∘ₘ
          (massPowerTilt (prior)
            (fun ω => highRawDensityMass (p ω)) n)) t := by
  intro prior
  have hq0 u hu ω x y :=
    (hq u hu ω x y).le
  have hprob u (hu : u ∈ Icc 0 T) :
      IsProbabilityMeasure (historyMarkedPrior dependent Δ u π activation) := by
    have hs  :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    exact historyMarkedPrior_probability hΔ hlabels hu.1 hBa (by
      apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
      solve_by_elim [Eventually.of_forall]) hcenter habound hs
  let _ := hprob t ⟨ht.le, htT.le⟩
  have hd := historyMarkedPrior_tiltedObservable_hasDerivAt hΔ hlabels hBa hactivation hcenter habound hsmall ha haRaw hp hF
    hraw hq0 hmass hH hB hHb ht htT
  have hpb ω x : |p ω x| ≤ |bRaw| := by
    grind
  have he := highMarginalRealScore_integral
    (prior) π hactivation hBa habound η aRaw bRaw B ha haRaw hB hp hF hraw
    (hq t ⟨ht.le,htT.le⟩) hH hHb
  have hi := highHistoryLikelihoodDerivative_observable π
    (prior) hactivation hBa habound η |bRaw| B (abs_nonneg _) hB ha hp hF hpb
    (hq0 t ⟨ht.le,htT.le⟩) hH hHb
  rw [hi, massPowerNormalizer_eq_of_massLaw (highRawDensityMass_joint_measurable hp)
    n (hmass t ⟨ht.le,htT.le⟩)] at he
  rw [he]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  let _ := hprob u ⟨hu.1.le,hu.2.le⟩
  exact (highTiltedObservableMean_eq_dataMean (historyMarkedPrior dependent Δ u π activation) ha.ne' haRaw hB hp hF hraw
    (hq0 u ⟨hu.1.le,hu.2.le⟩) hH hHb).symm

theorem historyMarkedPrior_dataMean_absolutelyContinuous (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H)
    {B : ℝ} (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval
      (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n)) 0 T := by
  obtain ⟨K, hK⟩ := historyMarkedPrior_tiltedObservable_exists_lipschitz hΔ hlabels hBa hactivation hcenter habound hsmall ha haRaw hp hF hraw hq hmass hH hB hHb
  have hint : Integrable activation π := by
    apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
    solve_by_elim [Eventually.of_forall]
  have he u (hu : u ∈ Icc 0 T) :
      highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation) a (v - η^2*u) hp hF H =
      ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (highRawDensityMass ∘ p) n) := by
    have hs  :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    let _ := historyMarkedPrior_probability hΔ hlabels hu.1 hBa hint hcenter habound hs
    exact highTiltedObservableMean_eq_dataMean (historyMarkedPrior dependent Δ u π activation) ha.ne' haRaw hB hp hF hraw (hq u hu) hH hHb
  have hKd : LipschitzOnWith K
      (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (highRawDensityMass ∘ p) n)) (Icc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu w hw
    rw [← he u hu, ← he w hw]
    exact hK.dist_le_mul u hu w hw
  rw [← uIcc_of_le hT] at hKd
  exact hKd.absolutelyContinuousOnInterval

include ha haRaw hraw hq hmass hH in
theorem historyMarkedPrior_dataMean_score_hasDerivAt_ae
    {B : ℝ} (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n))
        (∫ z, H z * highMarginalRealScore
          (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
          ∂(highRealSampleKernel n a (v - η^2*t) hp hF) ∘ₘ
            (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
              (fun ω => highRawDensityMass (p ω)) n)) t := by
  have h0 : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by simp [ae_iff]
  have hT : ∀ᵐ t ∂volume, t ≠ T := by simp [ae_iff]
  filter_upwards [h0, hT] with t ht0 htT
  intro ht
  exact historyMarkedPrior_dataMean_score_hasDerivAt hΔ hlabels hBa hactivation hcenter habound hsmall ha haRaw hp hF
    hraw hq hmass hH B hB hHb (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htT)

end NearlyMinimax
