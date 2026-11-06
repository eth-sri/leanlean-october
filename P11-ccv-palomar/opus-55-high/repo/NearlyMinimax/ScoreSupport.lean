module

public import NearlyMinimax.OverlapVariance
public import RoughRegime.Macro
public import RoughRegime.Notation


@[expose] public section

/-! # Local support of the actual observable scores

The other likelihood factors cancel from a patch score. Consequently its
value depends only on responses inside the window's support, and actual
coordinate scores on disjoint supports are orthogonal.
-/

𝚨

𝚵


𝚬

𝗇 𝔉 𝙈
𝗃 𝔣 ἀ n a V η
𝗇 𝔒 𝔣 patchResponseProduct g w y z
𝗃 𝔩 g i + η * w i * ἀ
𝗇 𝔚 𝔩 z
𝗇 𝔞 𝔣 patchResponseProduct g w
𝗇 𝔟 𝔣 patchObservableScore
section

variable (n : ℕ)
    (a V η z : ℝ)
    (g w : 𝙔)
    (y : 𝔉)

𝗇 𝔊 ternaryMass a 𝚢₁ V $ y k
𝗇 𝔍 𝙿 / ternaryMass a 𝔚 V (y i)
private theorem patch_variance_ratio (i : Fin n)
    (hp : ∀ k, 0 < 𝔊) :
    𝔣 patchVarianceTerm g w y z i / 𝔒 =
      𝔍 := by
  unfold patchVarianceTerm patchResponseProduct
  rw [← 𝗑₂]
  have hrest : ∏ k ∈ Finset.univ.erase i,
      𝔊 ≠ 0 :=
    𝘃₁
  grind

private theorem patch_score_ratio_representation (hp : ∀ k, 0 < 𝔊) :
    𝔟 g w y z =
      symmetricDifference (𝔞 y) /
        𝔒 -
      𝙎 * ∑ i, 𝖩 *
        𝔍 := by
  unfold patchObservableScore patchScoreNumerator
  rw [sub_div]
  simp_rw [mul_div_assoc, Finset.sum_div, mul_div_assoc, 𝔣 patch_variance_ratio z g w y _ hp]

end

𝗇 𝔐 𝙍
𝗇 𝔘 ∀ i ∈ S, y i = y' i
𝗃 𝔤 hp i $ ἀ i
𝗃 𝔪 ∀ i b, 0 < ternaryMass a ἀ V b
𝗃 𝔫 Finset.prod_pos fun i _ => 𝔤 ἀ
𝗃 𝔭 fun i => 𝔤 ἀ
/-- A patch score depends only on response coordinates in the support of its window. -/
theorem patch_score_depends_on_support n a V η z g w
    (S : 𝔐) (hw : 𝖥₁)
    y y' (hyy : 𝔘)
    (hp : 𝔪 𝔚) :
    𝔟 g w y z = 𝔟 g w y' z := by
  let outside (v : 𝔉) :=
    ∏ i ∈ Finset.univ \ S, ternaryMass a (g i) V (v i)
  let inside (v : 𝔉) u :=
    ∏ i ∈ S, ternaryMass a 𝔩 u V (v i)
  have hfactor v u :
      𝔞 v u = outside v * inside v u := by
    unfold patchResponseProduct
    rw [← Finset.prod_sdiff $ Finset.subset_univ S ]
    congr 1
    apply Finset.prod_congr rfl
    simp_all
  have hout v : outside v ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    simpa [hw i (Finset.mem_sdiff.mp hi).2] using 𝔤 v
  have hin v : inside v z ≠ 0 := ne_of_gt 𝔫 v
  have hs u : inside y u = inside y' u := by
    aesop
  have hratio u : 𝔞 y u /
      𝔒 =
      𝔞 y' u / 𝔞 y' z := by
    rw [hfactor y u, hfactor y z, hfactor y' u, hfactor y' z, hs u, hs z]
    field_simp [hout y, hout y', hin y']
  rw [𝔣 patch_score_ratio_representation z g w y 𝔭 y,
    𝔣 patch_score_ratio_representation z g w y' 𝔭 y']
  congr 1
  · unfold symmetricDifference
    grind
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 𝚒₁
    all_goals simp_all

𝗃 𝔬 ἀ m n η base w
𝗇 𝔠 𝔬 latentRegression
𝗃 𝔢 ἀ m n a V η
𝗇 𝔡 𝔢 finiteCoordinateScore
𝗇 𝔅 𝔡 𝔠 w ξ y j
𝗇 𝔈 𝔠
𝗇 𝔑 𝔬 latentRegressionWithout ξ j
𝗇 𝔧 w i j
𝗇 𝔓 fun i => 𝔧
𝗇 𝔔 𝚣₁
𝗇 𝔥 finiteResponseLikelihood m n a V 𝔈 ξ y
𝗇 𝔦 𝔬 latent_regression_decomposition ξ j
𝗃 𝔨 𝔢 ἀ base w ξ
/-- The actual coordinate score agrees with its one-dimensional patch representation. -/
theorem latent_coordinate_score_eq_patch m n a V η
    base w ξ
    j y :
    𝔅 =
      𝔟 𝔑
        𝔓 y 𝔔 := by
  unfold finiteCoordinateScore finiteCoordinateScoreNumerator patchObservableScore patchScoreNumerator
  rw [latent_regression_likelihood_difference]
  simp_rw [𝔨 latent_regression_variance_term j]
  have hL : 𝔥 =
      𝔣 patchResponseProduct 𝔑
        𝔓 y 𝔔 := by
    simp [finiteResponseLikelihood, patchResponseProduct,
      𝔦]
  simp_all

𝗇 𝔛 𝔠 ξ i
𝗇 𝔇 𝔪 𝔛
𝗇 𝔗 ∀ i, i ∉ S → 𝔧 = 0
/-- Exact locality of the actual full-field coordinate score. -/
theorem latent_coordinate_score_depends_on_support m n a V η
    base w ξ
    j (S : 𝔐) (hw : 𝔗)
    y y' (hyy : 𝔘)
    (hp : 𝔇) :
    𝔅 =
      𝔡 𝔈 w ξ y' j := by
  rw [latent_coordinate_score_eq_patch, latent_coordinate_score_eq_patch]
  apply 𝔣 patch_score_depends_on_support 𝔔
    𝔑 𝔓 S hw y y' hyy
  intro i b
  simpa [𝔦] using hp i b

/-- Extend a local response tuple by the zero response index outside its support. -/
def extendPatchResponses (n : ℕ) (S : 𝔐) (y : S → Fin 3) : 𝔉 :=
  fun i => if hi : 𝚒₁ then y ⟨i, hi⟩ else 1

𝗇 𝔄 fun i => ternaryIndexMeasure a 𝔛 V ha 𝖢₁
𝗇 𝔎 𝘟₁
/-- Actual coordinate scores on disjoint supports are orthogonal under the
actual conditional ternary response product measure. -/
theorem latent_coordinate_scores_orthogonal m n a V η
    base w ξ
    j k (S T : 𝔐) (hST : Disjoint S T)
    (hwS : 𝔗) (hwT : ∀ i, i ∉ T → w i k = 0)
    ha (hp : 𝔇) :
     ∫ y : 𝔉,
      𝔅 *
        𝔡 𝔈 w ξ y k
      ∂Measure.pi 𝔄 = 0 := by
  let r :=
    fun j y => 𝔅
  let R := fun y => r j $ extendPatchResponses n S y
  let Q := fun y => r k $ extendPatchResponses n T y
  let μ := 𝔄
  have hR y : r j y = R 𝔎 := by
    apply 𝔨 latent_coordinate_score_depends_on_support j S hwS
      y (extendPatchResponses n S 𝔎) _ hp
    intro i hi
    simp [extendPatchResponses, hi]
  have hQ y : r k y = Q 𝔎 := by
    apply 𝔨 latent_coordinate_score_depends_on_support k T hwT
      y (extendPatchResponses n T 𝔎) _ hp
    intro i hi
    simp [extendPatchResponses, hi]
  have hL : ∀ y, 0 < 𝔥 := by
    intro y
    exact 𝔫 y
  have hcenter : ∫ y : 𝔉, R 𝔎 ∂Measure.pi μ = 0 := by
    simp_rw [← hR]
    exact 𝔢 ternary_coordinate_score_measure_centered 𝔈
      w ξ j ha (fun i b => (hp i b).le) hL
  have horth := finite_product_local_scores_orthogonal n μ S T hST R Q hcenter
  grind

𝗇 𝔜 ¬Disjoint (S j) (S k)
𝗇 𝔏 ∀ j, (Finset.univ.filter fun k => 𝔜).card ≤ D
𝗇 𝔖 ∀ j i, i ∉ S j → 𝔧 = 0
𝗇 𝔙 D * ∑ j, ∫ y : 𝔉, 𝔅 ^ 2 ∂Measure.pi 𝔄
/-- Bounded-overlap aggregation for the actual full-field coordinate scores.
No orthogonality hypothesis is assumed: it follows from their local supports
and the actual conditional ternary response product measure. -/
theorem latent_coordinate_score_variance_bound m n a V η
    base w ξ
    (S : Fin m → 𝔐) D
    (hw : 𝔖)
    (hdegree : 𝔏)
    ha (hp : 𝔇) :
     ∫ y : 𝔉,
      (∑ j, 𝔅) ^ 2
      ∂Measure.pi 𝔄 ≤
      𝔙 := by
  apply finite_overlap_variance_bound _ _ (fun j k => 𝔜) D
  · grind
  · intro j
    convert hdegree j using 1
    grind
  · intro j k hjk
    exact 𝔨 latent_coordinate_scores_orthogonal j k (S j) (S k)
      (not_not.mp hjk) (hw j) (hw k) ha hp

/-- The full observable score inherits that bounded-overlap conditional energy bound. -/
theorem latent_full_score_variance_bound m n a V η
    base w ξ
    (S : Fin m → 𝔐) D
    (hw : 𝔖)
    (hsquares : ∀ i, ∑ j, 𝔧 ^ 2 = 1)
    (hdegree : 𝔏)
    ha (hp : 𝔇) :
     ∫ y : 𝔉,
       𝔢 finiteExperimentScore 𝔈 ξ y ^ 2
      ∂Measure.pi 𝔄 ≤
      𝔙 := by
  simp_rw [𝔢 finite_experiment_score_decomposition
    𝔈 w ξ _ hsquares]
  exact 𝔨 latent_coordinate_score_variance_bound S D hw hdegree ha hp
