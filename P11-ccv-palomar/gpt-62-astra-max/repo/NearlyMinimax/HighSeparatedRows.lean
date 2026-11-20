module

public import NearlyMinimax.HighDensityUpdates
public import NearlyMinimax.HighResponseUpdates

@[expose] public section

/-! The local row identity for arbitrary finite positive separated
representations, derived from the genuine density and response marks. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section ResponseIntegral
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section
variable (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ)

/-- Fixed coefficients of the response action as a linear map of A. -/
def responseMatrixEntryCoefficient (i j : ι) : ℝ :=
  ∑ s, ∑ t, (C ^ 2 / 2 * fairSign s * fairSign t) *
    ∑ h : Fin (2 * q + 2), responseWeight h *
      Φ (coefficientReset c (covarianceAtom C i j s t) (responseNode h))

theorem responseMatrixAction_entry_sum :
    responseMatrixAction q C A c Φ =
      ∑ i, ∑ j, A i j * responseMatrixEntryCoefficient q C c Φ i j := by
  simp only [responseMatrixAction, covarianceAction, covarianceWeight,
    responseMatrixEntryCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  grind

theorem responseMatrixAction_scalar_matrix (t : ℝ)
    (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => t * A i j) c Φ =
      t * responseMatrixAction q C A c Φ := by
  simp [responseMatrixAction_entry_sum, Finset.mul_sum, mul_assoc]

end

variable {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)

variable (q : ℕ) (C : ℝ) {A : Z → ι → ι → ℝ} (hA : ∀ i j, Integrable (fun ζ => A ζ i j) σ) (c : ι → ℝ)
    (Φ : (ι → ℝ) → ℝ)
include hA

theorem responseMatrixAction_integrable :
    Integrable (fun ζ => responseMatrixAction q C (A ζ) c Φ) σ := by
  simp [responseMatrixAction_entry_sum]
  fun_prop

/-- The actual fixed-atom response rule commutes with the positive
representation integral by its proved matrix linearity. -/
theorem responseMatrixAction_integral :
    responseMatrixAction q C (fun i j => ∫ ζ, A ζ i j ∂σ) c Φ =
      ∫ ζ, responseMatrixAction q C (A ζ) c Φ ∂σ := by
  simp [responseMatrixAction_entry_sum]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum _
    (fun j _ => (hA i j).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => (hA i j).mul_const _)]
  simp [integral_mul_const]

end ResponseIntegral

section Separated
variable {Z α : Type*} [MeasurableSpace Z] [DecidableEq α]

theorem densitySeparatedSym_measurable {r : ℕ} {B : Z → α → Fin r → ℝ}
    (hB : ∀ i l, Measurable (fun ζ => B ζ i l)) {S : Finset α} (hS : S.card = r) :
    Measurable (fun ζ => densitySeparatedSym r (B ζ) S) := by
  classical
  have he : (fun ζ => densitySeparatedSym r (B ζ) S) =
      (fun ζ => (∑ τ : Equiv.Perm (Fin r), ∏ i, B ζ (((Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa using hS)).symm) i) (τ i)) / r.factorial) := by
    funext ζ
    apply densitySeparatedSym_eq_permutation_average
  rw [he]
  fun_prop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section
variable (A : Z → ι → ι → ℝ) (ζ : Z)

def separatedMatrixCost : ℝ := ∑ i, ∑ j, |A ζ i j|

theorem separatedMatrixCost_entry_le (i j : ι) :
    |A ζ i j| ≤ separatedMatrixCost A ζ := by
  apply (Finset.single_le_sum (fun k _ => by positivity) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (A ζ k l)))
    (Finset.mem_univ i)

end

section
variable {σ : Measure Z} {r : ℕ} {B : Z → α → Fin r → ℝ} (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) {A : Z → ι → ι → ℝ} (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) {S : Finset α} (hS : S.card = r) (q : ℕ) (C : ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) (a b : ℝ)

include hA hcost in
theorem separatedMatrix_entry_integrable (i j : ι) :
    Integrable (fun ζ => A ζ i j) σ := by
  apply hcost.mono' (hA i j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ζ => separatedMatrixCost_entry_le A ζ i j)

/-- Actual separated representation of the symmetric matrix kernel on a
cardinality-r observation subset. -/
def separatedSubsetMatrix (σ : Measure Z) (r : ℕ) (B : Z → α → Fin r → ℝ)
    (A : Z → ι → ι → ℝ) (S : Finset α) : ι → ι → ℝ :=
  fun i j => ∫ ζ, densitySeparatedSym r (B ζ) S * A ζ i j ∂σ

include hB hBbound hA hcost hS in
theorem separated_subset_entry_integrable (i j : ι) :
    Integrable (fun ζ => densitySeparatedSym r (B ζ) S * A ζ i j) σ := by
  apply hcost.mono' ((densitySeparatedSym_measurable hB hS).mul (hA i j)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ζ
  change ‖densitySeparatedSym r (B ζ) S * A ζ i j‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  exact le_trans (mul_le_mul_of_nonneg_right (densitySeparatedSym_abs_le_one (B ζ) hS (fun i _ l => hBbound ..)) (abs_nonneg _)) (by simpa using separatedMatrixCost_entry_le A ζ i j)

include hB hBbound hA hcost hS in
theorem separatedSubsetMatrix_response :
    responseMatrixAction q C (separatedSubsetMatrix σ r B A S) c Φ =
      ∫ ζ, densitySeparatedSym r (B ζ) S * responseMatrixAction q C (A ζ) c Φ ∂σ := by
  unfold separatedSubsetMatrix
  rw [responseMatrixAction_integral σ q C
    (separated_subset_entry_integrable hB hBbound hA hcost hS)]
  simp [responseMatrixAction_scalar_matrix]

theorem densityPacketAction_mul_right (m r D : ℕ)
    (f : ℝ → (Fin r → ℝ) → ℝ) (t : ℝ) :
    densityPacketAction a b m r D (fun z ε => f z ε * t) = densityPacketAction a b m r D f * t := by
  simp only [densityPacketAction, densityDerivativeAction, Finset.sum_mul, mul_assoc, Finset.sum_mul, mul_assoc]

/-- The genuine iterated action of the density packet, representation
measure, and finite response covariance rule. -/
def highSeparatedPacketAction (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∫ ζ, densityPacketAction a b m r D
    (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) ∂σ

include hB hBbound hA hcost hS in
theorem separated_subset_response_integrable :
    Integrable (fun ζ => densitySeparatedSym r (B ζ) S * responseMatrixAction q C (A ζ) c Φ) σ := by
  simpa only [responseMatrixAction_scalar_matrix] using responseMatrixAction_integrable σ q C (separated_subset_entry_integrable hB hBbound hA hcost hS) c Φ

end

variable {σ : Measure Z} {a b : ℝ} (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (S : Finset α) (hSD : S.card ≤ D)
include hD hSD ha hab hr

/-- The paper's local row formula for arbitrary positive separated
representations. All integrability needed to commute sums and integrals
is derived from the finite representation cost. -/
theorem highSeparatedPacketAction_row (p : α → ℝ)
    {B : Z → α → Fin r → ℝ} (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b z ε p (B ζ) i) Φ =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ := by
  have hInt U (hU : U ∈ S.powersetCard r) :
      Integrable (fun ζ => (∏ i ∈ U, p i) *
        (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ)) σ :=
    (separated_subset_response_integrable hB hBbound hA hcost
      (Finset.mem_powersetCard.mp hU).2 q C c Φ).const_mul _
  have he ζ : densityPacketAction a b m r D
      (fun z ε => (∏ i ∈ S, localDensityReset a b z ε p (B ζ) i) *
        responseMatrixAction q C (A ζ) c Φ) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ) := by
    rw [densityPacketAction_mul_right,
      density_packet_product_exact ha hab m hr hD hSD p (B ζ)]
    simp [Finset.sum_mul, mul_assoc]
  unfold highSeparatedPacketAction
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ hInt]
  apply congrArg (fun t => densityCountCoefficient a b m r S.card * t)
  apply Finset.sum_congr rfl
  intro U hU
  rw [integral_const_mul, ← separatedSubsetMatrix_response hB hBbound hA hcost
    (Finset.mem_powersetCard.mp hU).2 q C c Φ]

theorem highSeparatedPacketAction_count_selector (hSm : S.card ≤ m) (hrS : r ≤ S.card) (p : α → ℝ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b z ε p (B ζ) i) Φ =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ else 0 := by
  rw [highSeparatedPacketAction_row ha hab m r D q hr hD S hSD p hB hBbound C hA hcost c Φ,
    densityCountCoefficient_exact a b ha hab m r S.card hr hrS hSm]
  split_ifs <;> simp

end Separated
end NearlyMinimax
