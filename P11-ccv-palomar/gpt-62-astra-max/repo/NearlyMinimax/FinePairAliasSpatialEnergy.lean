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
  have hU : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, U i ∈ spatialPatchBox d := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae).eventually (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hU] with U hU i r
  exact abs_le.mpr ⟨(hU i).1 r, (hU i).2 r⟩

 section
variable {d j n : ℕ} [NeZero d] (hd : 4 < d) {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi)

theorem finePairTimeSubsetMoment_univ_pair
    (hlo : 0 ≤ lo) (hhi : lo ≤ hi) {U : DesignSample d 2}
    (hU : ∀ i, U i ∈ hyperplaneCube d) :
    finePairTimeSubsetMoment lo hi U Finset.univ =
      fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) := by
  unfold finePairTimeSubsetMoment
  simp
  rw [finePairTimeFieldValue_weighted_covariance lo hi hlo (hU 0) (hU 1), exactEuclideanDistance_eq_euclideanNorm]
  unfold fineAliasLaplaceKernel
  rw [intervalIntegral.integral_of_le hhi, ← integral_Icc_eq_integral_Ioc]
  simp

 include hd hlo hhi in
theorem finePairTimeSubsetMoment_pair_square_integrable_and_le (hj : j = 2) :
    Integrable (fun U => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2)
      (fullSpatialPatchDesign d j) ∧
    (∫ U, finePairTimeSubsetMoment lo hi U Finset.univ ^ 2
      ∂fullSpatialPatchDesign d j) ≤ 6 * 2^d * spatialInverseFourConstant d / lo^(d-4) := by
  subst j
  have he : (fun U => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2) =ᵐ[fullSpatialPatchDesign d 2]
      (fun U => fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) ^ 2) := by
    filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube] with U hU
    rw [finePairTimeSubsetMoment_univ_pair hlo.le hhi hU]
  have h := fineAlias_fullSpatialPatchDesign_squared_integrable_and_integral_le hd hlo hhi
  refine ⟨h.1.congr he.symm, ?_⟩
  exact (integral_congr_ae he).trans_le h.2

 include hd hlo hhi in
theorem finePairTimeSubsetMoment_two_subset_square_integrable_and_le
    {S : Finset (Fin n)} (hS : S.card = 2) :
    Integrable (fun U => finePairTimeSubsetMoment lo hi U S ^ 2)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d n) ≤
      2^(d*(n-2)) * (6*2^d*spatialInverseFourConstant d / lo^(d-4)) := by
  have h := finePairTimeSubsetMoment_pair_square_integrable_and_le hd hlo hhi hS
  refine ⟨?_, ?_⟩
  · simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
    exact spatial_subset_square_integrable_enumerated h.1
  · rw [finePairTimeSubsetMoment_square_integral_reindex]
    simp_all

end

 def finePairAliasActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * n^2 * η^2))^2 *
      (n.choose 2)^2 * 2^(d*(n-2)) *
        (6*2^d*spatialInverseFourConstant d / T0^(d-4))

end NearlyMinimax
