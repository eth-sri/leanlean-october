module

public import NearlyMinimax.HistoryWeakTransport

@[expose] public section

/-!
# Weak evolution under the actual positive history prior, rather than only its polynomial
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- A source-positive history prior expectation is exactly its actual polynomial integral. -/
theorem historyMarkedPrior_integral_eq_expectation (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) =
      historyMarkedExpectation dependent (historyReferenceRho Δ) (historyMarkedReference dependent Δ π) a F t := by
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π a ha,
    integral_withDensity_eq_integral_toReal_smul
      (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  unfold historyMarkedExpectation
  apply integral_congr_ae
  apply Eventually.of_forall
  intro h
  have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
    (historyReferenceRho Δ) t B (historyReferenceRho_pos Δ) ht hB a habound hsmall h
  have hp : 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a h :=
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
  ring

/-- The signed local append expression evaluated under the actual positive prior. -/
def historyMarkedPriorGenerator (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2
      ∂(historyMarkedPrior dependent Δ t π a).prod π

/-- The genuine prior generator equals the source reference polynomial generator. -/
theorem historyMarkedPriorGenerator_eq_reference (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) :
    historyMarkedPriorGenerator dependent hsymm Δ t π a F =
      historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F := by
  unfold historyMarkedPriorGenerator historyMarkedGeneratorExpectation
  apply Finset.sum_congr rfl
  intro j hj
  have hm : Measurable (fun p : HistoryMarked dependent E × E =>
      ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1)) :=
    (historyMarkedDensity_measurable dependent (historyReferenceRho Δ) t a ha).ennreal_ofReal.comp measurable_fst
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π a ha,
    prod_withDensity_left (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
    (historyReferenceRho Δ) t B (historyReferenceRho_pos Δ) ht hB a habound hsmall p.1
  have hp : 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1 :=
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
  ring

end NearlyMinimax
