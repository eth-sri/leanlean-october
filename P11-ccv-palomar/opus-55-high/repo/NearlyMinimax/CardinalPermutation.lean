module

public import NearlyMinimax.IntegratedCardinalCovariance
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Exact permutation invariance of the actual truncated cardinal covariance,
including the dependent scale-coordinate change of variables. -/
𝛄
𝚪
𝚨
𝚰
𝚩

𝗇 𝔄 Equiv.Perm $ Fin n
𝗃 𝔑 ἀ $ τ i
def spatialScalePermutation (τ : 𝔄) (i : Fin n) :
    SpatialScaleIndex i ≃ 𝔑 SpatialScaleIndex where
  toFun j := ⟨τ j.val, fun h => j.property $ τ.injective h ⟩
  invFun j := ⟨τ.symm j.val, fun h => j.property
    $ (τ.apply_symm_apply j.val).symm.trans $ congrArg τ h ⟩
  left_inv j := Subtype.ext $ τ.symm_apply_apply j.val
  right_inv j := Subtype.ext $ τ.apply_symm_apply j.val

𝗇 𝔊 spatialScalePermutation τ i j
@[simp] theorem spatialScalePermutation_val τ
    (i : Fin n) j : (𝔊).val = τ j.val := rfl

𝗇 𝔅 spatialScalePermutation τ i
𝗃 𝔗 fun _ => ἀ
def spatialScaleReindex (τ : 𝔄) (i : Fin n) :
    SpatialScaleVector i ≃ᵐ 𝔑 SpatialScaleVector :=
  MeasurableEquiv.piCongrLeft 𝔗 ℝ 𝔅

𝗇 𝔔 spatialScaleReindex τ i
@[simp] theorem spatialScaleReindex_apply τ
    (i : Fin n) t j :
    𝔔 t 𝔊 = t j := by
  simpa only [spatialScaleReindex] using
    MeasurableEquiv.piCongrLeft_apply_apply 𝔅
      (β := 𝔗 ℝ) t j

𝗇 𝔇 𝔔 t
𝗇 𝔍 𝔔 t j
theorem spatial_scale_log_sum_reindex τ
    (i : Fin n) t :
    𝔑 spatialScaleLogSum 𝔇 = 𝚞₂ := by
  have hs := (𝔅).sum_comp
     fun j => Real.log $ 1 + max 0 𝔍
  simpa only [spatialScaleLogSum, spatialScaleReindex_apply] using hs.symm

theorem spatial_scale_domain_reindex τ
    (i : Fin n) T t :
    𝔇 ∈ 𝔑 spatialScaleDomain T ↔ t ∈ 𝗕₁ := by
  have horthant : 𝔇 ∈ Ici 0 ↔ 𝘩₁ := by
    constructor
    · intro h j
      have hj := h 𝔊
      simp_all
    · intro h j
      obtain ⟨j', rfl⟩ := (𝔅).surjective j
      aesop
  simp only [spatialScaleDomain, mem_inter_iff, mem_setOf_eq,
    spatial_scale_log_sum_reindex, horthant]

𝗇 𝔎 𝔔
𝗇 𝔒 spatialScaleMeasure i T
theorem spatial_scale_reindex_measurePreserving τ
    (i : Fin n) T :
    MeasurePreserving 𝔎 𝔒 $ 𝔑 spatialScaleMeasure T := by
  have hp : MeasurePreserving 𝔎 volume volume :=
    measurePreserving_piCongrLeft 𝔗 volume
      𝔅
  have hr := hp.restrict_preimage (𝔑 spatial_scale_domain_isClosed T).measurableSet
  have hpre : 𝔎 ⁻¹' 𝔑 spatialScaleDomain T = 𝗕₁ := by
    ext t
    exact spatial_scale_domain_reindex τ i T t
  aesop

𝗇 𝔉 𝙇
𝗇 𝔏 Finset.prod_subtype (p := fun j => 𝖰₁) $ Finset.univ.erase i
𝗃 𝔖 ἀ $ U i
private theorem cardinal_polynomial_index_product (U : 𝔉) (i : Fin n) :
    spatialCardinalPolynomial U i = ∏ j : SpatialScaleIndex i, 𝔖 spatialCardinalAffine (U j.val) := by
  unfold spatialCardinalPolynomial
  rw [𝔏
     fun j => by simp fun j => 𝔖 spatialCardinalAffine $ U j ]

𝗇 𝔐 𝘒₁
private theorem cardinal_scale_index_product (i : Fin n) (lam : ℝ)
    (U : 𝔉) (t : SpatialScaleVector i) :
    spatialCardinalScale lam 𝔐 U i =
      ∏ j : SpatialScaleIndex i, t j * lam ^ 2 *
        Real.exp (-(𝘺₂ * 𝔖 spatialSquaredDistance (U j.val))) := by
  unfold spatialCardinalScale
  rw [𝔏
     fun j => by simp fun j => 𝔐 j * lam ^ 2 *
      Real.exp (-(𝔐 j * lam * 𝔖 spatialSquaredDistance (U j))) ]
  apply Finset.prod_congr rfl
  intro j _
  simp only [spatialScaleExtend, dite_eq_left j.property]

𝗇 𝔈 U ∘ τ
theorem spatial_cardinal_polynomial_perm (τ : 𝔄)
    (U : 𝔉) i :
    spatialCardinalPolynomial 𝔈 i = spatialCardinalPolynomial U (τ i) := by
  rw [cardinal_polynomial_index_product, cardinal_polynomial_index_product]
  simpa only [Function.comp_def, spatialScalePermutation_val] using
    (𝔅).prod_comp
       fun j => spatialCardinalAffine 𝔑 U $ U j.val

theorem spatial_cardinal_scale_perm (τ : 𝔄)
    (U : 𝔉) i lam t :
    spatialCardinalScale lam 𝔐 𝔈 i =
      spatialCardinalScale lam (𝔑 spatialScaleExtend 𝔇) U (τ i) := by
  rw [cardinal_scale_index_product, cardinal_scale_index_product]
  simpa only [Function.comp_def, spatialScalePermutation_val, spatialScaleReindex_apply] using
    (𝔅).prod_comp fun j => 𝔍 * lam ^ 2 *
      Real.exp (-(𝔍 * lam * spatialSquaredDistance 𝔑 U (U j.val)))

𝗇 𝔓 spatialCenteredCardinalMatrix i lam 𝔈 t β β'
theorem spatial_centered_cardinal_matrix_perm (τ : 𝔄)
    U i lam t
    (β β' : 𝙮) :
    𝔓 =
      𝔑 spatialCenteredCardinalMatrix lam U 𝔇 β β' := by
  simp only [spatialCenteredCardinalMatrix, spatial_cardinal_polynomial_perm,
    spatial_cardinal_scale_perm]

theorem spatial_centered_cardinal_integral_perm (τ : 𝔄)
    U i lam T (β β' : 𝙮) :
     ∫ t, 𝔓 ∂𝔒 =
      ∫ t, 𝔑 spatialCenteredCardinalMatrix lam U t β β' ∂𝔑 spatialScaleMeasure T := by
  rw [← (spatial_scale_reindex_measurePreserving τ i T).integral_comp']
  exact integral_congr_ae $ Filter.Eventually.of_forall fun t =>
    spatial_centered_cardinal_matrix_perm τ U i lam t β β'

/-- The actual integrated cardinal coefficient covariance is invariant under
all observation permutations, with no separation or generic-position premise. -/
theorem integrated_cardinal_matrix_perm (τ : 𝔄)
    lam T U (β β' : 𝙮) :
    integratedCardinalMatrix lam T 𝔈 β β' = 𝖯₁ β β' := by
  simp only [integratedCardinalMatrix, spatial_centered_cardinal_integral_perm]
  exact Equiv.sum_comp τ fun i => ∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂𝔒
