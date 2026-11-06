module

public import NearlyMinimax.FineFieldTimeL2


@[expose] public section

/-! Exact subset reindexing and genuine full-design energies of fine-field
moments, including all unused spatial coordinates. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem spatial_subset_product_reindex {d k } (S : Finset (Fin k))
    U (f : Covariate d → ℝ) :
    (∏ i ∈ S, f (U i)) = ∏ j : Fin S.card, f (spatialSubsetConfiguration S U j) := by
  classical
  let e  := (Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))
  rw [← Finset.prod_coe_sort S (fun i => f (U i))]
  exact (e.symm.prod_comp (fun i : S => f (U i.val))).symm

theorem finePairTimeSubsetMoment_reindex {d k } lo hi
    (U : Fin k → Covariate d) S :
    finePairTimeSubsetMoment lo hi U S =
      finePairTimeSubsetMoment lo hi (spatialSubsetConfiguration S U) Finset.univ := by
  unfold finePairTimeSubsetMoment
  solve_by_elim [integral_congr_ae, Filter.Eventually.of_forall, spatial_subset_product_reindex]

theorem finePairTimeSubsetMoment_univ_measurable {d j } [NeZero d] lo hi :
    Measurable (fun U : Fin j → Covariate d => finePairTimeSubsetMoment lo hi U Finset.univ) := by
  have hm  :=
    measurable_fst.mul (boundedHyperplaneSpatialMoment_joint_measurable d j)
  have h : Measurable (fun U : Fin j → Covariate d =>
      ∫ T in Icc lo hi, T * boundedHyperplaneSpatialMoment d T j U) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  exact h

section
variable {d k : ℕ}

theorem finePairTimeSubsetMoment_measurable  [NeZero d] lo hi
    S :
    Measurable (fun U : Fin k → Covariate d => finePairTimeSubsetMoment lo hi U S) := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact (finePairTimeSubsetMoment_univ_measurable lo hi).comp (spatialSubsetConfiguration_measurable S)

theorem finePairTimeSubsetMoment_square_integrable  [NeZero d]
    (hd : 3 ≤ d) {lo hi } (hlo : 0 < lo) S (hS : 4 ≤ S.card) :
    Integrable (fun U  => finePairTimeSubsetMoment lo hi U S ^ 2)
      (fullSpatialPatchDesign d k) := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact spatial_subset_square_integrable_enumerated S
    (fun V => finePairTimeSubsetMoment lo hi V Finset.univ)
    (finePairTimeSubsetMoment_univ_square_integrable hd hS hlo)

theorem finePairTimeSubsetMoment_square_integral_reindex 
    lo hi S :
    (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) = 2 ^ (d * (k - S.card)) *
        ∫ V : Fin S.card → Covariate d, finePairTimeSubsetMoment lo hi V Finset.univ ^ 2
          ∂fullSpatialPatchDesign d S.card := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact spatial_subset_square_integral_enumerated (d := d) S
    (fun V => finePairTimeSubsetMoment lo hi V Finset.univ)

theorem finePairTimeSubsetMoment_square_integral_le  [NeZero d]
    (hd : 3 ≤ d) {lo hi } (hlo : 0 < lo) S (hS : 4 ≤ S.card) :
    (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      2 ^ (d * (k - S.card)) *
        (hyperplaneSpatialMomentConstant d ^ S.card * S.card ^ 4 * lo ^ (2 - (d : ℝ))) ^ 2 := by
  rw [finePairTimeSubsetMoment_square_integral_reindex]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb := finePairTimeSubsetMoment_univ_L2_le (d := d) hd hS (hi := hi) hlo
  have hn : 0 ≤ ∫ V : Fin S.card → Covariate d,
      finePairTimeSubsetMoment lo hi V Finset.univ ^ 2 ∂fullSpatialPatchDesign d S.card :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity [hyperplaneSpatialMomentConstant_positive d])).mpr hb
  simpa only [Real.sq_sqrt hn] using hs
end


end NearlyMinimax
