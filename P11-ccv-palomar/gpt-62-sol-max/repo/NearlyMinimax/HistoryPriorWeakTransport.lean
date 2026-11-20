module

public import NearlyMinimax.HistoryWeakTransport
public import NearlyMinimax.RealDensity

@[expose] public section

/-!
# Weak evolution under the actual positive history prior, rather than only its polynomial
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Integrate under the positive prior using its actual real density. -/
theorem HistoryPriorBounds.integral_eq_density {dependent : J → J → Prop} {Δ : ℕ} {T B : ℝ}
    {E : Type*} [MeasurableSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (P : HistoryPriorBounds dependent Δ π a T B)
    {t : ℝ} (ht : t ∈ Icc 0 T) (F : HistoryMarked dependent E → ℝ) :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) =
      ∫ h, F h * historyMarkedDensity dependent (historyReferenceRho Δ) t a h
        ∂historyMarkedReference dependent Δ π := by
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π a P.measurable,
    integral_realDensity (historyMarkedDensity_measurable dependent _ t a P.measurable) (P.density_nonneg ht)]
  simp only [mul_comm]

/-- The signed local append expression evaluated under the actual positive prior. -/
def historyMarkedPriorGenerator (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2
      ∂(historyMarkedPrior dependent Δ t π a).prod π

/-- The genuine prior generator equals the source reference polynomial generator. -/
theorem historyMarkedPriorGenerator_eq_reference {dependent : J → J → Prop} {Δ : ℕ} {T B : ℝ}
    {E : Type*} [MeasurableSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (P : HistoryPriorBounds dependent Δ π a T B)
    {t : ℝ} (ht : t ∈ Icc 0 T) (F : HistoryMarked dependent E → ℝ) :
    historyMarkedPriorGenerator dependent P.symm Δ t π a F =
      historyMarkedGeneratorExpectation dependent P.symm (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F := by
  unfold historyMarkedPriorGenerator historyMarkedGeneratorExpectation
  apply Finset.sum_congr rfl
  intro j _
  have hm := historyMarkedDensity_measurable dependent (historyReferenceRho Δ) t a P.measurable
  have hm' : Measurable (fun z : HistoryMarked dependent E × E =>
      historyMarkedDensity dependent (historyReferenceRho Δ) t a z.1) := hm.comp measurable_fst
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π a P.measurable,
    prod_withDensity_left hm.ennreal_ofReal, integral_realDensity hm' (fun p => P.density_nonneg ht p.1)]
  simp only [mul_left_comm, mul_comm]

end NearlyMinimax
