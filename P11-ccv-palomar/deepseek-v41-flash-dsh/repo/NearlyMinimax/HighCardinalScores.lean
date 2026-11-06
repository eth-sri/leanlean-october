module

public import NearlyMinimax.HighSeparatedScoreBounds
public import NearlyMinimax.CardinalSeparatedKernel

@[expose] public section

/-! The singleton ordinary row, instantiated with the genuine positive
separated representation of the spatial cardinal covariance. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable

def highCardinalDensityReset {d n : ℕ} (ad bd lam : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (ζ : CardinalSeparatedMark d n) (z : ℝ) (ε : Fin n → ℝ) (i : Fin n) : ℝ :=
  localDensityReset ad bd n z ε p (fun i l => cardinalSeparatedFactor lam ζ l (U i)) i

variable {d n F : ℕ}

theorem cardinalSeparatedSubsetMatrix_univ (lam : ℝ) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2) :
    separatedSubsetMatrix (cardinalSeparatedMeasure d n T) n
      (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
      (cardinalSeparatedAmplitude (D := F) lam) Finset.univ =
        integratedCardinalMatrix lam T U := by
  funext β β'
  unfold separatedSubsetMatrix
  simp_rw [cardinal_density_separated_sym_eq]
  exact (integrated_cardinal_symmetric_separated_exact lam hlam hT U hU β β').symm

/-- Exact selector for the genuine cardinal ordinary packet at its selected
count. Both the density selector and the matrix representation are evaluated. -/
theorem high_cardinal_packet_action_exact 
    (ad bd lam : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D)
    (C : ℝ) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    highSeparatedPacketAction (cardinalSeparatedMeasure d n T) ad bd m n D q C
      (cardinalSeparatedAmplitude lam) c
      (fun ζ z ε => ∏ i, highCardinalDensityReset ad bd lam U p ζ z ε i) Φ =
        (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam T U) c Φ := by
  have h := highSeparatedPacketAction_count_selector (cardinalSeparatedMeasure d n T) ad bd ha hab
    m n D q hn (hn.trans hnD) (Finset.univ : Finset (Fin n)) (by simpa using hnD)
    (by simpa using hnm) (by simp) p
    (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
    (fun i l => cardinal_separated_factor_measurable lam l (U i))
    (fun ζ i l => cardinal_separated_factor_abs_le_one lam ζ l (U i) (hU i)) C
    (cardinalSeparatedAmplitude lam) (cardinal_separated_amplitude_measurable lam)
    (cardinal_separated_cost_integrable lam hT) c Φ
  simp only [highCardinalDensityReset] at ⊢
  rw [h]
  have hpow : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  simp only [Finset.card_univ, Fintype.card_fin, ite_true, hpow,
    Finset.sum_singleton, cardinalSeparatedSubsetMatrix_univ lam hlam hT U hU]

end NearlyMinimax
