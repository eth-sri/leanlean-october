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

variable {dependent : J → J → Prop}

/-- A source-positive history prior expectation is exactly its actual polynomial integral. -/
theorem historyMarkedPrior_integral_eq_expectation
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hlabels : DegreeAtMost dependent Δ)
    {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) {a : E → ℝ} (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    (F : HistoryMarked dependent E → ℝ) :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) =
      historyMarkedExpectation (historyReferenceRho Δ) (historyMarkedReference dependent Δ π) a F t := by
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π ha,
    integral_withDensity_eq_integral_toReal_smul
      (historyMarkedDensity_measurable dependent _ t ha).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro h
  have hb := historyMarkedDensity_bounds hlabels (historyReferenceRho_pos Δ) ht hB habound hsmall h
  have hp  :=
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  simp [ENNReal.toReal_ofReal hp, smul_eq_mul]
  ring

/-- The signed local append expression evaluated under the actual positive prior. -/
def historyMarkedPriorGenerator
    [Std.Symm dependent] (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p,
    F (historyMarkedAppend j p) * a p.2
      ∂(historyMarkedPrior dependent Δ t π a).prod π

/-- The genuine prior generator equals the source reference polynomial generator. -/
theorem historyMarkedPriorGenerator_eq_reference
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hlabels : DegreeAtMost dependent Δ)
    {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {a : E → ℝ} (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    (F : HistoryMarked dependent E → ℝ) :
    historyMarkedPriorGenerator Δ t π a F =
      historyMarkedGeneratorExpectation (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F := by
  apply Finset.sum_congr rfl
  intro j hj
  have hm : Measurable (fun p : HistoryMarked dependent E × E =>
      ENNReal.ofReal (historyMarkedDensity (historyReferenceRho Δ) t a p.1)) :=
    (historyMarkedDensity_measurable dependent (historyReferenceRho Δ) t ha).ennreal_ofReal.comp measurable_fst
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π ha,
    prod_withDensity_left (historyMarkedDensity_measurable dependent _ t ha).ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  have hb := historyMarkedDensity_bounds hlabels (historyReferenceRho_pos Δ) ht hB habound hsmall p.1
  have hp  :=
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  simp [ENNReal.toReal_ofReal hp, smul_eq_mul]
  ring

end NearlyMinimax
