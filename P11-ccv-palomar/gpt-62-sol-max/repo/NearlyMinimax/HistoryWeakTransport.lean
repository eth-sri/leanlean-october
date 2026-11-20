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

/-- The actual generator before folding the history into raw fields: append a fresh local mark. -/
def historyMarkedGeneratorExpectation (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) (π : Measure E)
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2 *
      historyMarkedDensity dependent ρ t a p.1 ∂μ.prod π

/-- Exact signed integral change of variables, proved for the actual normalized reference law. -/
theorem historyMarkedLabelTerm_integral (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (t : ℝ) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F) (j : J) :
    (∫ h, F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h
      ∂historyMarkedReference dependent Δ π) =
    historyReferenceRho Δ * ∫ p : HistoryMarked dependent E × E,
      F (historyMarkedAppend dependent hsymm j p) * a p.2 *
        historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1
        ∂(historyMarkedReference dependent Δ π).prod π := by
  let μ := historyMarkedReference dependent Δ π
  let G := fun h : HistoryMarked dependent E =>
    F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h
  have hG : Measurable G := hF.mul (historyMarkedLabelTerm_measurable dependent _ t a ha j)
  have hm := historyMarkedReference_append_restrict dependent hrefl hsymm Δ j π
  have he := congrArg (fun ν : Measure (HistoryMarked dependent E) => ∫ h, G h ∂ν) hm
  rw [integral_smul_measure, integral_map (historyMarkedAppend_measurable dependent hsymm j).aemeasurable
    hG.aestronglyMeasurable] at he
  have hi : (historyMarkedTerminalSet dependent j).indicator G = G := by
    funext h
    by_cases ht : h ∈ historyMarkedTerminalSet dependent j
    · simp [ht]
    · simp [ht, G, historyMarkedLabelTerm_eq_zero dependent hsymm _ t a j h ht]
  rw [← integral_indicator (historyMarkedTerminalSet_measurable dependent j), hi] at he
  rw [ENNReal.toReal_ofReal (historyReferenceRho_pos Δ).le] at he
  change historyReferenceRho Δ *
      (∫ p : HistoryMarked dependent E × E, G (historyMarkedAppend dependent hsymm j p) ∂μ.prod π) =
        ∫ h, G h ∂μ at he
  have hp : ∀ p : HistoryMarked dependent E × E,
      G (historyMarkedAppend dependent hsymm j p) =
        F (historyMarkedAppend dependent hsymm j p) * a p.2 *
          historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1 := by
    intro p
    dsimp only [G]
    rw [historyMarkedLabelTerm_append dependent hrefl hsymm]
    ring
  simpa [hp] using he.symm
/-- The integral of the actual density derivative is exactly the source signed append generator. -/
theorem historyMarkedDensityDerivative_integral_eq_generator {dependent : J → J → Prop} {Δ : ℕ} {T B : ℝ}
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (P : HistoryPriorBounds dependent Δ π a T B)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    (∫ h, F h * historyMarkedDensityDerivative dependent (historyReferenceRho Δ) t a h
      ∂historyMarkedReference dependent Δ π) =
      historyMarkedGeneratorExpectation dependent P.symm (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F := by
  let μ := historyMarkedReference dependent Δ π
  let : IsProbabilityMeasure μ := P.reference_probability
  have hi (j : J) : Integrable (fun h => F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h) μ :=
    Integrable.of_bound (hF.mul (historyMarkedLabelTerm_measurable dependent _ t a P.measurable j)).aestronglyMeasurable
      (M * (B * (3 / 2 : ℝ) ^ Fintype.card J)) (.of_forall fun h => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hFbound h) (P.labelTerm_abs_le ht j h) (abs_nonneg _) hM)
  have hp : ∀ h : HistoryMarked dependent E,
      F h * historyMarkedDensityDerivative dependent (historyReferenceRho Δ) t a h =
        (historyReferenceRho Δ)⁻¹ * ∑ j, F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h := by
    intro h
    rw [historyMarkedDensityDerivative_eq_labelSum]
    calc
      _ = (historyReferenceRho Δ)⁻¹ *
          (F h * ∑ j, historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h) := by ring
      _ = _ := by rw [Finset.mul_sum]
  simp_rw [hp]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hi j)]
  change (historyReferenceRho Δ)⁻¹ *
    (∑ j, ∫ h, F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h
      ∂historyMarkedReference dependent Δ π) = _
  simp_rw [historyMarkedLabelTerm_integral dependent P.refl P.symm Δ t π a P.measurable F hF]
  unfold historyMarkedGeneratorExpectation
  rw [← Finset.mul_sum]
  have hn := ne_of_gt (historyReferenceRho_pos Δ)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end NearlyMinimax
