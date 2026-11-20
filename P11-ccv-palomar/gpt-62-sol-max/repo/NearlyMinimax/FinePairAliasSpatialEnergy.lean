module

public import NearlyMinimax.FinePairSpatialEnergy
public import NearlyMinimax.SpatialFineAliasPairL2

@[expose] public section

/-! The actual card-two fine-field alias is the Laplace kernel Wfi.
Its selected-subset spatial energy includes the exact unused-volume factor. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 theorem fullSpatialPatchDesign_ae_hyperplaneCube {d n : ℕ} :
    ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, U i ∈ hyperplaneCube d := by
  filter_upwards [ae_pi_forall (ι := Fin n)
    (ae_restrict_mem (μ := volume) (s := spatialPatchBox d) measurableSet_Icc)] with U hU i
  exact spatialPatchBox_coord_abs_le (hU i)

 theorem finePairTimeSubsetMoment_univ_pair {d : ℕ} [NeZero d] {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : lo ≤ hi) (U : Fin 2 → Covariate d)
    (hU : ∀ i, U i ∈ hyperplaneCube d) :
    finePairTimeSubsetMoment lo hi U Finset.univ =
      fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) := by
  unfold finePairTimeSubsetMoment
  simp only [Fin.prod_univ_two]
  rw [finePairTimeFieldValue_weighted_covariance d lo hi hlo _ _ (hU 0) (hU 1)]
  rw [exactEuclideanDistance_eq_euclideanNorm]
  unfold fineAliasLaplaceKernel
  simp [intervalIntegral.integral_of_le hhi, ← integral_Icc_eq_integral_Ioc]

 theorem finePairTimeSubsetMoment_pair_square_integrable_and_le {d j : ℕ} [NeZero d]
    (hd : 4 < d) {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi) (hj : j = 2) :
    Integrable (fun U : Fin j → Covariate d => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2)
      (fullSpatialPatchDesign d j) ∧
    (∫ U : Fin j → Covariate d, finePairTimeSubsetMoment lo hi U Finset.univ ^ 2
      ∂fullSpatialPatchDesign d j) ≤ 6 * (2 : ℝ)^d * spatialInverseFourConstant d / lo^(d-4) := by
  subst j
  have he : (fun U : Fin 2 → Covariate d => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2) =ᵐ[fullSpatialPatchDesign d 2]
      (fun U => fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) ^ 2) := by
    filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube] with U hU
    rw [finePairTimeSubsetMoment_univ_pair hlo.le hhi U hU]
  have h := fineAlias_fullSpatialPatchDesign_squared_integrable_and_integral_le hd hlo hhi
  refine ⟨h.1.congr he.symm, ?_⟩
  exact (integral_congr_ae he).trans_le h.2

 theorem finePairTimeSubsetMoment_two_subset_square_integrable_and_le {d n : ℕ} [NeZero d]
    (hd : 4 < d) {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi)
    (S : Finset (Fin n)) (hS : S.card = 2) :
    Integrable (fun U : Fin n → Covariate d => finePairTimeSubsetMoment lo hi U S ^ 2)
      (fullSpatialPatchDesign d n) ∧
    (∫ U : Fin n → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d n) ≤
      (2 : ℝ)^(d*(n-2)) * (6*(2 : ℝ)^d*spatialInverseFourConstant d / lo^(d-4)) := by
  have h := finePairTimeSubsetMoment_pair_square_integrable_and_le hd hlo hhi hS
  refine ⟨?_, ?_⟩
  · simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
    exact spatial_subset_square_integrable_enumerated S _ h.1
  · rw [finePairTimeSubsetMoment_square_integral_reindex]
    have hb := mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (2 : ℝ)^(d*(n-S.card)))
    simpa only [hS] using hb

 def finePairAliasActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairActionCap d n M q ad bd C a ρ η)^2 *
      (n.choose 2 : ℝ)^2 * (2 : ℝ)^(d*(n-2)) *
        (6*(2 : ℝ)^d*spatialInverseFourConstant d / T0^(d-4))

end NearlyMinimax
