module

public import NearlyMinimax.HistoryLabelDerivative


@[expose] public section

/-!
# Actual weak transport of the positive marked-history prior
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

section
variable {dependent : J → J → Prop}

/-- The actual generator before folding the history into raw fields: append a fresh local mark. -/
def historyMarkedGeneratorExpectation
    [Std.Symm dependent] (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) (π : Measure E)
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p,
    F (historyMarkedAppend j p) * a p.2 *
      historyMarkedDensity ρ t a p.1 ∂μ.prod π

/-- Exact signed integral change of variables, proved for the actual normalized reference law. -/
theorem historyMarkedLabelTerm_integral
    [Std.Refl dependent] [Std.Symm dependent]
    (Δ : ℕ) (t : ℝ) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {a : E → ℝ} (ha : Measurable a)
    {F : HistoryMarked dependent E → ℝ} (hF : Measurable F) (j : J) :
    (∫ h, F h * historyMarkedLabelTerm (historyReferenceRho Δ) t a j h
      ∂historyMarkedReference dependent Δ π) =
    historyReferenceRho Δ * ∫ p,
      F (historyMarkedAppend j p) * a p.2 *
        historyMarkedDensity (historyReferenceRho Δ) t a p.1
        ∂(historyMarkedReference dependent Δ π).prod π := by
  let G := fun h =>
    F h * historyMarkedLabelTerm (historyReferenceRho Δ) t a j h
  have hG : Measurable G := hF.mul (historyMarkedLabelTerm_measurable dependent _ t ha j)
  have he := congrArg (fun ν => ∫ h, G h ∂ν) (historyMarkedReference_append_restrict (dependent := dependent) Δ j π)
  rw [integral_smul_measure, integral_map (historyMarkedAppend_measurable j).aemeasurable
    hG.aestronglyMeasurable] at he
  have hi : (historyMarkedTerminalSet dependent j).indicator G = G := by
    funext h
    by_cases ht : h ∈ historyMarkedTerminalSet dependent j
    · simp [ht]
    · simp [ht, G, historyMarkedLabelTerm_eq_zero _ t a h ht]
  rw [← integral_indicator (historyMarkedTerminalSet_measurable dependent j), hi] at he
  rw [ENNReal.toReal_ofReal (historyReferenceRho_pos Δ).le] at he
  have hp : ∀ p,
      G (historyMarkedAppend j p) =
        F (historyMarkedAppend j p) * a p.2 *
          historyMarkedDensity (historyReferenceRho Δ) t a p.1 := by
    intro p
    dsimp [G]
    rw [historyMarkedLabelTerm_append]
    ring
  simp_rw [hp] at he
  exact he.symm

end

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hlabels : DegreeAtMost dependent Δ) {ρ T t B : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*}
    [MeasurableSpace E]
include hlabels

include hρ ht hB in
/-- Bounded observables times true maximal-label terms are integrable over every finite law. -/
theorem historyMarkedLabelTerm_integrable (μ : Measure (HistoryMarked dependent E)) [IsFiniteMeasure μ]
    {a : E → ℝ} (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ historyActivityRadius Δ)
    {F : HistoryMarked dependent E → ℝ} (hF : Measurable F)
    {M : ℝ} (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) (j : J) :
    Integrable (fun h => F h * historyMarkedLabelTerm ρ t a j h) μ := by
  apply Integrable.of_bound (hF.mul (historyMarkedLabelTerm_measurable dependent ρ t ha j)).aestronglyMeasurable
    (M * (B * (3 / 2) ^ Fintype.card J))
  apply Eventually.of_forall
  intro h
  change ‖F h * historyMarkedLabelTerm ρ t a j h‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  bound [historyMarkedLabelTerm_bound hlabels hρ ht hB habound hsmall j h]

include hΔ ht hB in
/-- The integral of the actual density derivative is exactly the source signed append generator. -/
theorem historyMarkedDensityDerivative_integral_eq_generator [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {a : E → ℝ} (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    {F : HistoryMarked dependent E → ℝ} (hF : Measurable F)
    {M : ℝ} (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    (∫ h, F h * historyMarkedDensityDerivative (historyReferenceRho Δ) t a h
      ∂historyMarkedReference dependent Δ π) =
      historyMarkedGeneratorExpectation (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F := by
  let  := historyMarkedReference_probability hΔ hlabels π
  have hi  :=
    fun j => historyMarkedLabelTerm_integrable hlabels
      (historyReferenceRho_pos Δ) ht hB (historyMarkedReference dependent Δ π) ha habound hsmall hF hM hFbound j
  have hp : ∀ h,
      F h * historyMarkedDensityDerivative (historyReferenceRho Δ) t a h =
        (historyReferenceRho Δ)⁻¹ * ∑ j, F h * historyMarkedLabelTerm (historyReferenceRho Δ) t a j h := by
    intro h
    rw [historyMarkedDensityDerivative_eq_labelSum]
    calc
      _ = (historyReferenceRho Δ)⁻¹ *
          (F h * ∑ j, historyMarkedLabelTerm (historyReferenceRho Δ) t a j h) := by ring
      _ = _ := by rw [Finset.mul_sum]
  simp_rw [hp]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hi j)]
  simp_rw [historyMarkedLabelTerm_integral Δ t π ha hF]
  unfold historyMarkedGeneratorExpectation
  rw [← Finset.mul_sum]
  grind [ne_of_gt (historyReferenceRho_pos Δ)]

include hΔ in
/-- Genuine interior weak evolution of the positive marked-history density law. -/
theorem historyMarkedExpectation_weak_transport {t : ℝ} (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {a : E → ℝ} (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    {F : HistoryMarked dependent E → ℝ} (hF : Measurable F)
    {M : ℝ} (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    HasDerivAt (historyMarkedExpectation (historyReferenceRho Δ)
      (historyMarkedReference dependent Δ π) a F)
      (historyMarkedGeneratorExpectation (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F) t := by
  let := historyMarkedReference_probability hΔ hlabels π
  have hs  :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htT.le hB) (historyReferenceRho_pos Δ).le).trans hsmall
  have hd := (((historyDensityPath hlabels (historyReferenceRho_pos Δ) hB ha habound hsmall Subset.rfl).weight hF hFbound).integral_deriv (historyMarkedReference dependent Δ π) (Icc_mem_nhds ht htT)).2
  rw [historyMarkedDensityDerivative_integral_eq_generator hΔ hlabels ht.le hB π ha habound hs hF hM hFbound] at hd
  exact hd

end NearlyMinimax
