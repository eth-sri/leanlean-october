module

public import NearlyMinimax.FinePairSpatialEnergy
public import NearlyMinimax.SpatialFineAliasPairL2
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual card-two fine-field alias is the Laplace kernel Wfi.
Its selected-subset spatial energy includes the exact unused-volume factor. -/
𝚫
𝚪
𝚨
𝚩
𝚭
𝚬

 𝗇 𝔊 𝖮₁
𝗇 𝔍 𝖾₁
theorem fullSpatialPatchDesign_ae_hyperplaneCube :
    ∀ᵐ U ∂𝔊, 𝔍 := by
  have hU : ∀ᵐ U ∂𝔊, ∀ i, U i ∈ spatialPatchBox d := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae
      ).eventually $ ae_restrict_mem measurableSet_Icc
  filter_upwards [hU] with U hU i r
  exact abs_le.mpr ⟨(hU i).1 r, (hU i).2 r⟩

 set_option hygiene false
𝗇 𝔄 finePairTimeSubsetMoment lo hi U
𝗇 𝔅 fineAliasLaplaceKernel lo hi 𝙹
theorem finePairTimeSubsetMoment_univ_pair [NeZero d]
    (hlo : 0 ≤ lo) (hhi : lo ≤ hi) (U : 𝖿₁)
    (hU : 𝔍) :
    𝔄 Finset.univ =
      𝔅 := by
  unfold finePairTimeSubsetMoment
  simp
  rw [finePairTimeFieldValue_weighted_covariance d lo hi hlo _ _ (hU 0) $ hU 1 ]
  rw [exactEuclideanDistance_eq_euclideanNorm]
  unfold fineAliasLaplaceKernel
  rw [intervalIntegral.integral_of_le hhi, ← integral_Icc_eq_integral_Ioc]
  simp

 set_option hygiene false
𝗇 𝔇 6 * 𝙉^d * spatialInverseFourConstant d
𝗇 𝔈 𝗗₁
𝗇 𝔎 𝔄 Finset.univ ^ 2
theorem finePairTimeSubsetMoment_pair_square_integrable_and_le [NeZero d]
    (hd : 4 < d) (hlo : 𝙫₁) (hhi : lo ≤ hi) (hj : j = 2) :
    Integrable (fun U : 𝗲₂ => 𝔎)
      (fullSpatialPatchDesign d j) ∧
     ∫ U : 𝗲₂, 𝔎
      ∂fullSpatialPatchDesign d j ≤ 𝔇 / lo^𝔈 := by
  subst j
  have he : (fun U => 𝔎) =ᵐ[𝗿₂]
       fun U => 𝔅 ^ 2 := by
    filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube] with U hU
    rw [finePairTimeSubsetMoment_univ_pair hlo.le hhi U hU]
  have h := fineAlias_fullSpatialPatchDesign_squared_integrable_and_integral_le hd hlo hhi
  refine ⟨h.1.congr he.symm, ?_⟩
  exact (integral_congr_ae he).trans_le h.2

 set_option hygiene false
𝗇 𝔉 d*𝗥
theorem finePairTimeSubsetMoment_two_subset_square_integrable_and_le [NeZero d]
    (hd : 4 < d) (hlo : 𝙫₁) (hhi : lo ≤ hi)
    (S : 𝙍) (hS : S.card = 2) :
    Integrable (fun U => 𝔄 S ^ 2)
      𝔊 ∧
     ∫ U : 𝙇, 𝔄 S ^ 2
      ∂𝔊 ≤
       2 ^𝔉 * (6*𝖥*spatialInverseFourConstant d / lo^𝔈) := by
  have h := finePairTimeSubsetMoment_pair_square_integrable_and_le hd hlo hhi hS
  refine ⟨?_, ?_⟩
  · simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
    exact spatial_subset_square_integrable_enumerated S _ h.1
  · rw [finePairTimeSubsetMoment_square_integral_reindex]
    simp_all

 def finePairAliasActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (𝗺₁ *
    (𝘁 * 𝙒^2 * 𝙎))^2 *
      (n.choose 2 : ℝ)^2 * 𝙉^𝔉 *
        (𝔇 / T0^𝔈)
