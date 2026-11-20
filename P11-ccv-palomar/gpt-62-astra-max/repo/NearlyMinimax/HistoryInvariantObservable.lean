module

public import NearlyMinimax.HistoryExpectationRegularity


@[expose] public section

/-!
# Invariant observable laws derived from genuine conditional local annihilation
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hlabels : DegreeAtMost dependent Δ) {T t B : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*}
    [MeasurableSpace E] [StandardBorelSpace E] {π : Measure E} [IsProbabilityMeasure π] {a : E → ℝ}
    (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
include hΔ hlabels hB ha habound

include ht in
/-- Conditional signed-mark annihilation kills the true append generator by Fubini. -/
theorem historyMarkedGeneratorExpectation_eq_zero
    (hsmall : t * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    {F : HistoryMarked dependent E → ℝ} (hF : Measurable F)
    {M : ℝ} (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M)
    (hkill : ∀ j h, ∫ e, F (historyMarkedAppend j (h, e)) * a e ∂π = 0) :
    historyMarkedGeneratorExpectation (historyReferenceRho Δ) t
      (historyMarkedReference dependent Δ π) π a F = 0 := by
  let  := historyMarkedReference_probability hΔ hlabels π
  apply Finset.sum_eq_zero
  intro j hj
  let G := fun p =>
    F (historyMarkedAppend j p) * a p.2 *
      historyMarkedDensity (historyReferenceRho Δ) t a p.1
  have hG : Measurable G :=
    ((hF.comp (historyMarkedAppend_measurable j)).mul (ha.comp measurable_snd)).mul
      ((historyMarkedDensity_measurable dependent _ t ha).comp measurable_fst)
  have hInt : Integrable G ((historyMarkedReference dependent Δ π).prod π) := by
    apply Integrable.of_bound hG.aestronglyMeasurable (M * B * (3 / 2) ^ Fintype.card J)
    apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hb := historyMarkedDensity_bounds hlabels (historyReferenceRho_pos Δ) ht hB habound hsmall p.1
    have hp  :=
      (by positivity : 0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hp]
    exact mul_le_mul (mul_le_mul (hFbound _) (habound _) (abs_nonneg _) hM) hb.2 hp (mul_nonneg hM hB)
  rw [integral_prod G hInt]
  have hin : ∀ h, ∫ e, G (h, e) ∂π = 0 := by
    intro h
    dsimp [G]
    rw [integral_mul_const, hkill j h, zero_mul]
  simp_rw [hin]
  simp

include hT in
/-- An annihilated bounded observable has the same expectation throughout the closed source interval. -/
theorem historyMarkedPrior_invariant_observable
    (hsmall : T * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    {F : HistoryMarked dependent E → ℝ} (hF : Measurable F)
    {M : ℝ} (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M)
    (hkill : ∀ j h, ∫ e, F (historyMarkedAppend j (h, e)) * a e ∂π = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) = ∫ h, F h ∂historyMarkedReference dependent Δ π := by
  let μ := historyMarkedReference dependent Δ π
  let  := historyMarkedReference_probability hΔ hlabels π
  let f := historyMarkedExpectation (historyReferenceRho Δ) μ a F
  have hs : ∀ u ∈ Icc 0 T, u * B / historyReferenceRho Δ ≤ historyActivityRadius Δ := fun u hu => (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB)
      (historyReferenceRho_pos Δ).le).trans hsmall
  have hAC  :=
    historyMarkedExpectation_absolutelyContinuous hlabels (historyReferenceRho_pos Δ) hT hB μ ha habound hsmall hF hM hFbound
  have hn0 : ∀ᵐ u : ℝ, u ≠ 0 := by rw [ae_iff]; simp
  have hnT : ∀ᵐ u, u ≠ T := by rw [ae_iff]; simp
  have hzero : ∀ᵐ u, u ∈ uIcc 0 T → HasDerivAt f 0 u := by
    filter_upwards [hn0, hnT] with u hu0 huT hu
    rw [uIcc_of_le hT] at hu
    have hd := historyMarkedExpectation_weak_transport hΔ hlabels (lt_of_le_of_ne hu.1 (Ne.symm hu0)) (lt_of_le_of_ne hu.2 huT) hB
      π ha habound hsmall hF hM hFbound
    rw [historyMarkedGeneratorExpectation_eq_zero hΔ hlabels hu.1 hB ha habound (hs u hu) hF hM hFbound hkill] at hd
    exact hd
  obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hzero
  have hft  := (hC t (by simpa only [uIcc_of_le hT] using ht)).trans
    (hC 0 (by simp)).symm
  rw [historyMarkedPrior_integral_eq_expectation hlabels ht.1 hB π ha habound (hs t ht) F, hft]
  simp [f, μ, historyMarkedExpectation, historyMarkedDensity_zero]

end NearlyMinimax
