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
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def highCardinalDensityReset {d n : ℕ} (ad bd lam : ℝ)
    (U : DesignSample d n) (p : Fin n → ℝ)
    (ζ : CardinalSeparatedMark d n) (z : ℝ) (ε : Fin n → ℝ) (i : Fin n) : ℝ :=
  localDensityReset ad bd z ε p (fun i l => cardinalSeparatedFactor lam ζ l (U i)) i

variable {d n F : ℕ} {ad bd lam : ℝ} (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) {T : ℝ} (hT : 1 ≤ T)
include hlam hT

theorem cardinalSeparatedSubsetMatrix_univ {U : DesignSample d n} (hU : ∀ i l, |U i l| ≤ 2) :
    separatedSubsetMatrix (cardinalSeparatedMeasure d n T) n
      (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
      (cardinalSeparatedAmplitude (D := F) lam) Finset.univ =
        integratedCardinalMatrix lam T U := by
  funext β β'
  unfold separatedSubsetMatrix
  simp_rw [cardinal_density_separated_sym_eq]
  exact (integrated_cardinal_symmetric_separated_exact hlam hT hU β β').symm

include ha hab in
/-- Exact selector for the genuine cardinal ordinary packet at its selected
count. Both the density selector and the matrix representation are evaluated. -/
theorem high_cardinal_packet_action_exact (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D)
    (C : ℝ) {U : DesignSample d n} (hU : ∀ i l, |U i l| ≤ 2)
    (p : Fin n → ℝ) (c : HighFrameVector d F) (Φ : (HighFrameVector d F) → ℝ) :
    highSeparatedPacketAction (cardinalSeparatedMeasure d n T) ad bd m n D q C
      (cardinalSeparatedAmplitude lam) c
      (fun ζ z ε => ∏ i, highCardinalDensityReset ad bd lam U p ζ z ε i) Φ =
        (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam T U) c Φ := by
  have h := highSeparatedPacketAction_count_selector ha hab m n D q hn (hn.trans hnD) Finset.univ (by simpa using hnD) (by simpa using hnm) (by simp) p _ (fun i l => cardinal_separated_factor_measurable lam l (U i)) (fun ζ i l => cardinal_separated_factor_abs_le_one lam ζ l (hU i)) C (cardinal_separated_amplitude_measurable lam) (cardinal_separated_cost_integrable lam hT) c Φ
  simp [highCardinalDensityReset] at ⊢
  rw [h]
  simp [Finset.card_univ, Fintype.card_fin, ite_true, (by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))),
    Finset.sum_singleton, cardinalSeparatedSubsetMatrix_univ hlam hT hU]

end NearlyMinimax
