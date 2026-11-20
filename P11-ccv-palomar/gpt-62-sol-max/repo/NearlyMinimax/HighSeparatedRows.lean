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

/-- Fixed coefficients of the response action as a linear map of A. -/
def responseMatrixEntryCoefficient (q : ℕ) (C : ℝ) (c : ι → ℝ)
    (Φ : (ι → ℝ) → ℝ) (i j : ι) : ℝ :=
  ∑ s : Bool, ∑ t : Bool, (C ^ 2 / 2 * fairSign s * fairSign t) *
    ∑ h : Fin (2 * q + 2), responseWeight q h *
      Φ (coefficientReset c (covarianceAtom C i j s t) (responseNode q h))

section
variable (q : ℕ)

theorem responseMatrixAction_entry_sum (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C A c Φ =
      ∑ i, ∑ j, A i j * responseMatrixEntryCoefficient q C c Φ i j := by
  simp only [responseMatrixAction, covarianceAction, covarianceWeight,
    responseMatrixEntryCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  grind

theorem responseMatrixAction_scalar_matrix (C t : ℝ)
    (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => t * A i j) c Φ =
      t * responseMatrixAction q C A c Φ := by
  simp only [responseMatrixAction_entry_sum, Finset.mul_sum, mul_assoc]

end

variable {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)

section
variable (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Integrable (fun ζ => A ζ i j) σ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ)
include hA

theorem responseMatrixAction_integrable :
    Integrable (fun ζ => responseMatrixAction q C (A ζ) c Φ) σ := by
  simp only [responseMatrixAction_entry_sum]
  apply integrable_finset_sum <;> fun_prop

/-- The actual fixed-atom response rule commutes with the positive
representation integral by its proved matrix linearity. -/
theorem responseMatrixAction_integral :
    responseMatrixAction q C (fun i j => ∫ ζ, A ζ i j ∂σ) c Φ =
      ∫ ζ, responseMatrixAction q C (A ζ) c Φ ∂σ := by
  simp only [responseMatrixAction_entry_sum]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum _
    (fun j _ => (hA i j).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => (hA i j).mul_const _)]
  simp only [integral_mul_const]

end

end ResponseIntegral

section Separated
variable {Z α : Type*} [MeasurableSpace Z] [DecidableEq α]

theorem densitySeparatedSym_measurable (r : ℕ) (B : Z → α → Fin r → ℝ)
    (hB : ∀ i l, Measurable (fun ζ => B ζ i l)) (S : Finset α) (hS : S.card = r) :
    Measurable (fun ζ => densitySeparatedSym r (B ζ) S) := by
  classical
  let e : Fin r ≃ S := (Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa using hS)).symm
  have he : (fun ζ => densitySeparatedSym r (B ζ) S) =
      (fun ζ => (∑ τ : Equiv.Perm (Fin r), ∏ i, B ζ (e i) (τ i)) / (r.factorial : ℝ)) := by
    funext ζ
    apply densitySeparatedSym_eq_permutation_average
  rw [he]
  exact (Finset.measurable_fun_sum _ (fun τ _ => Finset.measurable_fun_prod _
    (fun i _ => hB (e i) (τ i)))).div_const _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def separatedMatrixCost (A : Z → ι → ι → ℝ) (ζ : Z) : ℝ := ∑ i, ∑ j, |A ζ i j|

section
variable (A : Z → ι → ι → ℝ) (ζ : Z)

theorem separatedMatrixCost_entry_le (i j : ι) :
    |A ζ i j| ≤ separatedMatrixCost A ζ := by
  apply (Finset.single_le_sum (fun k _ => abs_nonneg (A ζ i k)) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (A ζ k l)))
    (Finset.mem_univ i)

theorem separatedMatrixCost_nonneg : 0 ≤ separatedMatrixCost A ζ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

end

theorem separatedMatrixCost_measurable {A : Z → ι → ι → ℝ}
    (hm : ∀ i j, Measurable (fun ζ => A ζ i j)) : Measurable (separatedMatrixCost A) :=
  Finset.measurable_fun_sum _ fun i _ => Finset.measurable_fun_sum _ fun j _ => (hm i j).abs

/-- A measurable separated amplitude with finite entrywise absolute cost. -/
structure SeparatedMatrixIntegrable (σ : Measure Z) (A : Z → ι → ι → ℝ) : Prop where
  meas : ∀ i j, Measurable (fun ζ => A ζ i j)
  cost : Integrable (separatedMatrixCost A) σ

theorem SeparatedMatrixIntegrable.of_cost_le {σ : Measure Z} {A : Z → ι → ι → ℝ} {g : Z → ℝ}
    (hm : ∀ i j, Measurable (fun ζ => A ζ i j)) (hi : Integrable g σ)
    (hle : ∀ ζ, separatedMatrixCost A ζ ≤ g ζ) : SeparatedMatrixIntegrable σ A :=
  ⟨hm, hi.mono_nonneg (separatedMatrixCost_measurable hm).aestronglyMeasurable
    (.of_forall (separatedMatrixCost_nonneg A)) (.of_forall hle)⟩

theorem SeparatedMatrixIntegrable.entry {σ : Measure Z} {A : Z → ι → ι → ℝ}
    (hA : SeparatedMatrixIntegrable σ A) (i j : ι) : Integrable (fun ζ => A ζ i j) σ :=
  hA.cost.mono' (hA.meas i j).aestronglyMeasurable
    (.of_forall fun ζ => by simpa using separatedMatrixCost_entry_le A ζ i j)

theorem SeparatedMatrixIntegrable.of_entries {σ : Measure Z} {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hi : ∀ i j, Integrable (fun ζ => A ζ i j) σ) :
    SeparatedMatrixIntegrable σ A :=
  ⟨hA, integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hi i j).abs⟩

theorem SeparatedMatrixIntegrable.const (σ : Measure Z) [IsFiniteMeasure σ] (A : ι → ι → ℝ) :
    SeparatedMatrixIntegrable σ (fun _ => A) :=
  ⟨fun _ _ => measurable_const, integrable_const _⟩

/-- Actual separated representation of the symmetric matrix kernel on a
cardinality-r observation subset. -/
def separatedSubsetMatrix (σ : Measure Z) (r : ℕ) (B : Z → α → Fin r → ℝ)
    (A : Z → ι → ι → ℝ) (S : Finset α) : ι → ι → ℝ :=
  fun i j => ∫ ζ, densitySeparatedSym r (B ζ) S * A ζ i j ∂σ

section
variable (σ : Measure Z) (r : ℕ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A)
    (S : Finset α) (hS : S.card = r)
include hB hBbound hA hS

theorem separated_subset_entry_integrable (i j : ι) :
    Integrable (fun ζ => densitySeparatedSym r (B ζ) S * A ζ i j) σ := by
  exact (hA.entry i j).bdd_mul (densitySeparatedSym_measurable r B hB S hS).aestronglyMeasurable
    (.of_forall fun ζ => by
      simpa using densitySeparatedSym_abs_le_one r (B ζ) S hS (fun i _ l => hBbound ζ i l))

theorem separatedSubsetMatrix_response
    (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (separatedSubsetMatrix σ r B A S) c Φ =
      ∫ ζ, densitySeparatedSym r (B ζ) S * responseMatrixAction q C (A ζ) c Φ ∂σ := by
  unfold separatedSubsetMatrix
  rw [responseMatrixAction_integral σ q C _
    (separated_subset_entry_integrable σ r B hB hBbound A hA S hS)]
  simp only [responseMatrixAction_scalar_matrix]

end

/-- The genuine iterated action of the density packet, representation
measure, and finite response covariance rule. -/
def highSeparatedPacketAction (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∫ ζ, densityPacketAction a b m r D (G ζ) * responseMatrixAction q C (A ζ) c Φ ∂σ

section
variable (σ : Measure Z)

theorem separated_subset_response_integrable (r : ℕ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A) (S : Finset α) (hS : S.card = r)
    (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    Integrable (fun ζ => densitySeparatedSym r (B ζ) S * responseMatrixAction q C (A ζ) c Φ) σ := by
  have h := responseMatrixAction_integrable σ q C
    (fun ζ i j => densitySeparatedSym r (B ζ) S * A ζ i j)
    (separated_subset_entry_integrable σ r B hB hBbound A hA S hS) c Φ
  simpa only [responseMatrixAction_scalar_matrix] using h

section
variable (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (S : Finset α) (hSD : S.card ≤ D)
include ha hab hr hD hSD

/-- The paper's local row formula for arbitrary positive separated
representations. All integrability needed to commute sums and integrals
is derived from the finite representation cost. -/
theorem highSeparatedPacketAction_row (p : α → ℝ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) Φ =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ := by
  have hInt (U : Finset α) (hU : U ∈ S.powersetCard r) :
      Integrable (fun ζ => (∏ i ∈ U, p i) *
        (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ)) σ :=
    (separated_subset_response_integrable σ r B hB hBbound A hA U
      (Finset.mem_powersetCard.mp hU).2 q C c Φ).const_mul _
  have he (ζ : Z) : densityPacketAction a b m r D
      (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) *
        responseMatrixAction q C (A ζ) c Φ =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ) := by
    rw [density_packet_product_exact S a b ha hab m r D hr hD hSD p (B ζ)]
    simp only [Finset.sum_mul, mul_assoc]
  unfold highSeparatedPacketAction
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ hInt]
  apply congrArg (fun t => densityCountCoefficient a b m r S.card * t)
  apply Finset.sum_congr rfl
  intro U hU
  rw [integral_const_mul, ← separatedSubsetMatrix_response σ r B hB hBbound A hA U
    (Finset.mem_powersetCard.mp hU).2 q C c Φ]

theorem highSeparatedPacketAction_count_selector (hSm : S.card ≤ m) (hrS : r ≤ S.card) (p : α → ℝ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) Φ =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ else 0 := by
  simp [highSeparatedPacketAction_row σ a b ha hab m r D q hr hD S hSD p B hB hBbound C A hA c Φ, densityCountCoefficient_exact a b ha hab m r S.card hr hrS hSm]

end

end

end Separated
end NearlyMinimax
