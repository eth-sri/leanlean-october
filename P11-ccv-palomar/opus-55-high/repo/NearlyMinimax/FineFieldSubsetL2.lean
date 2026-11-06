module

public import NearlyMinimax.FineFieldTimeL2
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Exact subset reindexing and genuine full-design energies of fine-field
moments, including all unused spatial coordinates. -/
𝚫
𝚪
𝚨
𝚩

𝗃 𝔑 Fin ἀ → Covariate d
𝗇 𝔇 𝔑 k
𝗇 𝔏 𝖹₂ j
𝗃 𝔐 fun i => f $ U ἀ
theorem spatial_subset_product_reindex S
    (U : 𝔇) (f : 𝙀) :
     ∏ i ∈ S, f (U i) = ∏ j : Fin S.card, f 𝔏 := by
  classical
  let e := (Fintype.equivFin S).trans $ finCongr $ Fintype.card_coe S
  rw [← Finset.prod_coe_sort S 𝔐 i]
  exact (e.symm.prod_comp 𝔐 i.val).symm

𝗇 𝔈 finePairTimeSubsetMoment lo hi
theorem finePairTimeSubsetMoment_reindex lo hi
    (U : 𝔇) S :
    𝔈 U S =
      𝔈 𝖹₂ Finset.univ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun e => by
    change e.1 * ∏ i ∈ S, finePairTimeFieldValue e (U i) =
      e.1 * ∏ j : Fin S.card, finePairTimeFieldValue e 𝔏
    rw [spatial_subset_product_reindex S U $ finePairTimeFieldValue e ]

theorem finePairTimeSubsetMoment_univ_measurable [NeZero d] (lo hi : ℝ) :
    Measurable fun U : 𝔑 j => 𝔈 U Finset.univ := by
  have hm :=
    measurable_fst.mul $ boundedHyperplaneSpatialMoment_joint_measurable d j
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

𝗇 𝔉 𝘓₂
𝗇 𝔍 finePairTimeSubsetMoment_reindex (S := S)
theorem finePairTimeSubsetMoment_measurable [NeZero d] (lo hi : ℝ)
    (S : 𝔉) :
    Measurable fun U : 𝔇 => 𝔈 U S := by
  simp_rw [𝔍]
  exact (finePairTimeSubsetMoment_univ_measurable lo hi).comp $ spatialSubsetConfiguration_measurable S

𝗇 𝔎 fun V => 𝔈 V Finset.univ
theorem finePairTimeSubsetMoment_square_integrable [NeZero d]
    (hd : 3 ≤ d) (hlo : 𝙫₁) (S : 𝔉) (hS : 4 ≤ S.card) :
    Integrable (fun U : 𝔇 => 𝔈 U S ^ 2)
      $ fullSpatialPatchDesign d k := by
  simp_rw [𝔍]
  exact spatial_subset_square_integrable_enumerated S
    𝔎
    $ finePairTimeSubsetMoment_univ_square_integrable hd hS hlo

𝗇 𝔄 ∫ U : 𝔑 k, finePairTimeSubsetMoment lo hi U S ^ 2 ∂fullSpatialPatchDesign d k
𝗇 𝔅 ∫ V : 𝔑 S.card, finePairTimeSubsetMoment lo hi V Finset.univ ^ 2 ∂fullSpatialPatchDesign d S.card
𝗇 𝔊 2 ^ (d * (k - S.card))
theorem finePairTimeSubsetMoment_square_integral_reindex
    lo hi (S : 𝔉) :
    𝔄 = 𝔊 *
        𝔅 := by
  simp_rw [𝔍]
  exact spatial_subset_square_integral_enumerated S
    𝔎

theorem finePairTimeSubsetMoment_square_integral_le [NeZero d]
    (hd : 3 ≤ d) (hlo : 𝙫₁) (S : 𝔉) (hS : 4 ≤ S.card) :
    𝔄 ≤
      𝔊 *
        (hyperplaneSpatialMomentConstant d ^ S.card * S.card ^ 4 * lo ^ (2 - 𝙊)) ^ 2 := by
  rw [finePairTimeSubsetMoment_square_integral_reindex]
  have hn : 0 ≤ 𝔅 :=
    integral_nonneg 𝖸
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) $ by positivity [hyperplaneSpatialMomentConstant_positive d] ).mpr $ finePairTimeSubsetMoment_univ_L2_le hd hS (hi := hi) hlo
  simp_all
