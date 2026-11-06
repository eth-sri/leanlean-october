module

public import NearlyMinimax.LowSmoothnessRestriction
public import NearlyMinimax.LowSmoothnessWindows
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual grid prior's design-dependent conditional score energies. -/

𝚴

𝚨

𝚬

𝗇 𝕷 𝘆
def gridWindowCount (d k : ℕ) : ℕ := 𝕷 ^ d

𝗇 𝔄 gridWindowCount d k
def gridWindowIndexEquiv (d k : ℕ) : Fin 𝔄 ≃ (Fin d → Fin 𝕷) :=
  (Fintype.equivFinOfCardEq $ by simp [gridWindowCount] ).symm

𝗇 𝔎 gridWindowIndexEquiv d k j
def indexedGridWindow (d k : ℕ) (j : Fin 𝔄) : 𝙀 :=
  gridTensorWindow d k 𝔎

def indexedGridPatch (d k : ℕ) (j : Fin 𝔄) : 𝘶 :=
  gridPatch d k 𝔎

𝗇 𝔚 𝚣₁
𝗇 𝔱 Fin 𝔄 → Fin 3
def indexedGridField (d k : ℕ) (η : ℝ) (ξ : 𝔱)
    (x : Covariate d) : ℝ := η * ∑ j, indexedGridWindow d k j x * 𝔚

𝗇 𝕻 indexedGridField d k η ξ
𝗇 𝔠 𝕻
𝗇 𝔡 gridWindowIndexEquiv d k
theorem indexedGridField_eq d k η ξ :
    𝔠 =
      gridPriorField d k η fun j => ξ $ (𝔡).symm j := by
  funext x
  unfold indexedGridField gridPriorField
  congr 1
  exact Fintype.sum_equiv 𝔡 _ _ fun j => 𝖨₄

theorem indexedGridField_continuous d k η ξ :
    Continuous 𝔠 := by
  rw [indexedGridField_eq]
  exact gridPriorField_continuous ..

𝗇 𝔜 𝗼
𝗇 𝔶 𝖥
theorem indexedGridField_abs_bound d k η (hη : 𝔜)
    ξ x :
    |𝕻 x| ≤ 𝔶 * η := by
  rw [indexedGridField_eq]
  exact gridPriorField_abs_bound _ _ _ hη _ x

𝗇 𝔒 𝙇
𝗇 𝕳 indexedGridWindow d k j $ x i
def gridSampleWeights (d k n : ℕ) (x : 𝔒) :
    Fin n → Fin 𝔄 → ℝ := fun i j => 𝕳

𝗇 𝔅 gridSampleWeights d k n x
𝗇 𝔈 𝖾
𝗇 𝔓 𝕻 $ x i
𝗃 𝖃 ἀ 𝔄 n η 𝔈 𝔅
𝗇 𝔮 𝖃 latentRegression
theorem grid_latent_regression_eq d k n η x
    ξ i :
    𝔮 ξ i =
      𝔓 := by
  simp [latentRegression, indexedGridField, gridSampleWeights]

𝗇 𝔊 gridSampleWeights d k n x i j
theorem grid_sample_squared_partition d k n x i :
     ∑ j, 𝔊 ^ 2 = 1 := by
  have h := Fintype.sum_equiv 𝔡
    (fun j => 𝕳 ^ 2) (fun j => gridTensorWindow d k j (x i) ^ 2)
    𝘦
  exact h.trans $ gridTensorWindow_square_partition d k $ x i

𝗇 𝔉 (𝔶 + 2) * η
𝗇 𝔢 ternaryValue_one_abs_le $ ξ j
𝗇 𝔧 𝙼₂ $ x i
𝗇 𝔫 𝖃 latentRegressionWithout ξ j
𝗇 𝔰 gridTensorWindow d k 𝔎 $ x i
𝗇 𝕭 u - z
𝗇 𝕴 𝔫 i + η * 𝔊 * u
theorem grid_modified_regression_abs_bound d k n η u (hη : 𝔜)
    x ξ
    j i (hu : u ∈ Icc (-1) 1) :
    |𝕴| ≤ 𝔉 := by
  let z := 𝔚
  have hz := 𝔢
  have hw : |𝔊| ≤ 1 := by
    change |𝔰| ≤ 1
    rw [abs_of_nonneg $ gridTensorWindow_nonneg d k 𝔎 $ x i ]
    exact gridTensorWindow_le_one ..
  have hdiff : |𝕭| ≤ 2 := by
    grind
  have heq : 𝕴 =
        𝔓 + η * 𝔊 * 𝕭 := by
    rw [← grid_latent_regression_eq, latent_regression_decomposition]
    ring
  rw [heq]
  have hterm : |η * 𝔊 * 𝕭| ≤ 2 * η := by
    rw [abs_mul, abs_mul, abs_of_nonneg hη]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hw hη) hdiff (abs_nonneg _) 𝖠₃
    linarith
  exact 𝘝₂ $ by nlinarith [𝔧]

def gridCoordinateEnergy (d k n : ℕ) (a V η : ℝ)
    (ξ : 𝔱) (j : Fin 𝔄)
    (x : 𝔒) : ℝ :=
  patchExpectedScoreEnergy n a V η
    𝔫
    (fun i => 𝔊) 𝔚

𝗃 𝖄 fun x => ἀ
theorem grid_sample_weight_measurable d k n j i :
    Measurable 𝖄 𝔊 :=
  ((gridTensorWindow_continuous d k 𝔎).comp
    $ continuous_apply i ).measurable

theorem grid_excluded_field_measurable d k n η
    ξ j i :
    Measurable fun x =>
      𝔫 i := measurable_const.add $ (Finset.measurable_sum _
     fun l _ => (grid_sample_weight_measurable d k n l i).mul_const _ ).const_mul _

𝗇 𝔵 ternaryScoreExponentialConstant P.a P.ρ P.c
𝗇 𝕼 𝗄
𝗇 𝔷 (n * 𝕼) ^ 2
𝗇 𝔇 𝔵 ^ 2 * Real.exp 𝔵 * 𝗩 * 𝔷
𝗇 𝔍 P.variancePath η t
𝗃 𝖂 ἀ x u hu i
𝗇 𝔏 ⟨(𝖂 hp y).le, ternary_mass_le_one P.a _ _ P.a_pos.ne' (fun b => (𝖂 hp b).le) y⟩
𝗇 𝔑 t ∈ 𝗃
𝗇 𝔔 n * (2 / 𝙦) ^ d ≤ 1
𝗇 𝔗 Measure.pi 𝙮₁
𝗇 𝕽 𝙎
𝗇 𝔘 𝕽 ≤ P.ρ
𝗇 𝕾 𝖂 hreg
𝗇 𝔙 P.path_legality η t (g x i + η * w x i * u) ht hvariance 𝕾
𝗇 𝔞 (grid_modified_regression_abs_bound d k n η u hη x ξ j i hu).trans hfield
𝗇 𝔣 (𝖂 hlegal).2.2.1 y
𝗇 𝔦 grid_excluded_field_measurable d k n η ξ j
𝗇 𝔭 gridCoordinateEnergy d k n P.a 𝔍 η ξ j
𝗇 𝔲 𝔉 ≤ P.ρ
𝗇 𝕰 grid_sample_weight_measurable d k n j
𝗇 𝕱 (hlegal x z hz i).2.2.1 y
𝗇 𝕵 gridTensorWindow_nonneg d k ..
𝗃 𝖁 ∫ x : 𝔒, ἀ x ∂ 𝔗
/-- Actual coordinate score energy integrated over the complete uniform-design
sample. The observations outside the patch have already been cancelled. -/
theorem grid_coordinate_design_energy_bound (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) η t
    ξ j
    (hk : 𝖰) (hη : 𝔜) (ht : 𝔑)
    (hfield : 𝔲) (hvariance : 𝔘)
    (hmean : 𝔔) :
    𝖁 𝔭 ≤
      𝔇 := by
  let _ := cubeVolume_isProbability d
  let g := 𝖄 𝔫
  let w := fun x i => 𝔊
  let A := indexedGridPatch d k j
  let z := 𝔚
  have hz := abs_le.mp 𝔢
  have hreg x u hu i :=
    𝔞
  have hlegal x u hu i :=
    𝔙
  have hp x u hu i y :=
    P.c_pos.trans_le 𝔣
  have hvol : 𝘣₂ A ≤ 𝕼 := gridPatch_cube_probability_bound d k _ hk
  have hbound := iid_design_full_patch_score_energy_bound (cubeVolume d) n A
    (gridPatch_measurable d k _) P.a 𝔍 η z P.ρ P.c g w
    𝔦 𝕰
    P.a_pos P.ρ_pos.le P.c_pos hz ((mul_le_mul_of_nonneg_left hvol $ Nat.cast_nonneg n ).trans hmean)
    (fun x i hi => gridTensorWindow_zero_outside_patch d k 𝔎 (x i) hi)
     fun x i _ => by
      change |𝔰| ≤ 1
      rw [abs_of_nonneg 𝕵]; exact gridTensorWindow_le_one d k ..
    (fun x u hu i _ => 𝕾)
    (fun x u hu i _ y => 𝔏)
    (fun x i _ y => 𝕱) fun x i y => hp x z hz i y
  apply hbound.trans
  gcongr

𝗃 𝕯 ἀ 𝔄 n a V
def gridFullScoreEnergy (d k n : ℕ) (a V η : ℝ) (ξ : 𝔱)
    (x : 𝔒) : ℝ :=
  ∑ y, 𝕯 finiteResponseLikelihood
    𝔮 ξ y *
     𝕯 finiteExperimentScore η
      𝔮 ξ y ^ 2

𝗇 𝕬 fun i => x i ∈ indexedGridPatch d k j
𝗇 𝔐 Finset.univ.filter fun l => ¬Disjoint (Finset.univ.filter 𝕬) (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k l)
𝗇 𝔛 5 ^ d
theorem indexed_grid_observed_patch_degree d k n (x : 𝔒)
    j :
    (𝔐).card ≤ 𝔛 := by
  have heq := Finset.card_equiv 𝔡 (s := 𝔐)
    (t := Finset.univ.filter fun l =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k 𝔎)
        (Finset.univ.filter fun i => x i ∈ gridPatch d k l))
     fun _ => by
      aesop
  rw [heq]
  exact grid_observed_patch_degree d k n x _

𝗇 𝔨 gridCoordinateEnergy d k n a V η ξ j x
𝗇 𝔬 ∑ y, 𝕯 finiteResponseLikelihood f ξ y * 𝕯 finiteCoordinateScore η f 𝔅 ξ y j ^ 2
𝗇 𝕿 gridFullScoreEnergy d k n
𝗇 𝔯 𝕿 a V η ξ
theorem grid_full_score_conditional_energy_bound d k n a V η
    ξ x
    (ha : 𝙞) (hp : ∀ i y, 0 < ternaryMass a 𝔓 V y) :
    𝔯 x ≤ 5 ^ d *
      ∑ j, 𝔨 := by
  let f := 𝔮
  let S :=
    fun j => Finset.univ.filter 𝕬
  have hpos : ∀ i y, 0 < ternaryMass a (f ξ i) V y := by
    intro i y
    simpa [f, grid_latent_regression_eq] using hp i y
  have h := 𝕯 latent_full_score_variance_bound η 𝔈
    𝔅 ξ S 𝔛
     fun j i hi => gridTensorWindow_zero_outside_patch d k _ (x i) $ by
      aesop
    (grid_sample_squared_partition d k n x)
    (indexed_grid_observed_patch_degree d k n x) ha hpos
  simp_rw [ternary_index_product_integral] at h
  change 𝔯 x ≤ (𝔛 : ℕ) *
    ∑ j, 𝔬 at h
  have hcoord j :
      𝔬 =
        𝔨 := by
    apply Finset.sum_congr rfl
    intro y _
    rw [latent_coordinate_score_eq_patch]
    simp only [finiteResponseLikelihood, patchResponseProduct, f]
    simp_rw [𝖃 latent_regression_decomposition ξ j]
  simp_all

𝗇 𝕸 𝙖
theorem grid_full_score_energy_measurable d k n a V η
    ξ :
    Measurable 𝔯 := by
  let f :=
    𝖄 𝔮
  have hq ξ' i y :
      Measurable fun x => ternaryMass a (f x ξ' i) V y := by
    apply ternaryMass_measurable_comp
    simpa only [f, grid_latent_regression_eq, Function.comp_def] using
      ((indexedGridField_continuous d k η ξ').comp $ continuous_apply i ).measurable
  have hL ξ' y :
      Measurable fun x => 𝕯 finiteResponseLikelihood (f x) ξ' y :=
    Finset.measurable_prod _ fun i _ => hq ξ' i $ y i
  have hU y i :
      Measurable fun x => 𝕯 finiteResponseVarianceTerm (f x) ξ y i :=
    𝗄₂
  have hD y j :=
    (((hL (Function.update ξ j 2) y).const_mul 𝕸).add
      $ (hL (Function.update ξ j 0) y).const_mul 𝕸 ).sub $ hL (Function.update ξ j 1) y
  have hR y :
      Measurable fun x => 𝕯 finiteExperimentScore η (f x) ξ y :=
    ((Finset.measurable_sum _ fun j _ => hD y j ).sub
      $ (Finset.measurable_sum _ fun i _ => hU y i ).const_mul 𝕽 ).div $ hL ξ y
  exact 𝘭₁

𝗇 𝔥 𝘂
𝗃 𝕮 ἀ C P k n η t ξ
section

variable (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C)

theorem grid_coordinate_energy_integrable k n η t
    ξ j
    (hη : 𝔜) (ht : 𝔑)
    (hfield : 𝔲) (hvariance : 𝔘) :
    Integrable 𝔭
      𝔗 := by
  let _ := cubeVolume_isProbability d
  let g := 𝖄 𝔫
  let w := fun x i => 𝔊
  let z := 𝔚
  have hz := abs_le.mp 𝔢
  have hreg x u hu i :=
    𝔞
  have hlegal x u hu i :=
    𝔙
  have hp x u hu i y :=
    P.c_pos.trans_le 𝔣
  exact patch_expected_score_energy_integrable _ n P.a 𝔍 η z P.ρ P.c g w
    𝔦 𝕰
    P.a_pos P.ρ_pos.le P.c_pos hz
     fun x i => by
      change |𝔰| ≤ 1
      rw [abs_of_nonneg 𝕵]; exact gridTensorWindow_le_one d k ..
    hreg (fun x u hu i y => 𝔏)
     fun x i y => 𝕱

theorem grid_response_positive k n η t
    ξ (x : 𝔒)
    (hη : 𝔜) (ht : 𝔑)
    (hfield : 𝔲) (hvariance : 𝔘) :
    ∀ i y, 0 < ternaryMass P.a 𝔓 𝔍 y := by
  intro i y
  exact P.c_pos.trans_le $ (P.path_legality η t _ ht hvariance $ (𝔧).trans 𝖥₃ ).2.2.1 y

𝗇 𝔟 𝕮 grid_response_positive x hη ht hfield hvariance
𝗇 𝔤 𝕮 grid_coordinate_energy_integrable j hη ht hfield hvariance
𝗇 𝔳 𝕿 P.a 𝔍 η ξ
𝗇 𝔴 grid_full_score_conditional_energy_bound d k n P.a 𝔍 η ξ x P.a_pos.ne'
theorem grid_full_score_energy_integrable k n η t
    ξ
    (hη : 𝔜) (ht : 𝔑)
    (hfield : 𝔲) (hvariance : 𝔘) :
    Integrable 𝔳
      𝔗 := by
  have hI := (integrable_finsetSum Finset.univ fun j _ =>
    𝔤 ).const_mul 𝔛
  apply hI.mono' (grid_full_score_energy_measurable d k n P.a 𝔍 η ξ).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hp := 𝔟
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact 𝔴 hp
  · exact Finset.sum_nonneg fun y _ => mul_nonneg
      (Finset.prod_nonneg fun i _ => by simpa [grid_latent_regression_eq] using (𝚗₁).le )
      $ sq_nonneg _

𝗇 𝔩 fun j _ => hcoords j
theorem grid_full_score_design_energy_bound
    (k n : ℕ) η t
    ξ (hk : 𝖰)
    (hη : 𝔜) (ht : 𝔑)
    (hfield : 𝔲) (hvariance : 𝔘)
    (hmean : 𝔔) :
    𝖁 𝔳 ≤
       5 ^ d * 𝔄 *
        𝔇 := by
  let μ := Measure.pi 𝔥
  have hcoords j :=
    𝔤
  calc
    _ ≤ ∫ x, 𝔛 * ∑ j, 𝔭 x ∂μ :=
      integral_mono (𝕮 grid_full_score_energy_integrable hη ht hfield hvariance)
        ((integrable_finsetSum _ 𝔩).const_mul _)
         fun x => 𝔴 𝔟
    _ = 𝔛 * ∑ j, ∫ x, 𝔭 x ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ 𝔩]
    𝖦 := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ 𝖠₃
      calc
        _ ≤ ∑ _j : Fin 𝔄,
            𝔇 := Finset.sum_le_sum fun j _ =>
          𝕮 grid_coordinate_design_energy_bound j hk hη ht hfield hvariance hmean
        𝘿 := 𝖢₄

end

/-- The actual latent-prior, design, and response score energy. -/
def gridPriorScoreEnergy (d k n : ℕ) (a v η t : ℝ) : ℝ :=
  ∑ ξ, activationProductPrior 𝔄 t ξ *
    ∫ x : 𝔒, 𝕿 a (v - 𝕽 * t) η ξ x
      ∂Measure.pi 𝔥

𝗇 𝔖 K ^ 2 * Real.exp K * 𝗩 * 𝔷
𝗇 𝕲 𝙉 ^ d
𝗇 𝕶 gridPriorScoreEnergy d k n P.a P.v η t
𝗇 𝕹 (2 * k) ^ d
/-- Uniform full score budget for the actual prior and the actual IID design.
Every energy bound is derived from the ternary likelihood, count law, and
window support geometry. -/
theorem grid_prior_score_energy_bound (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) η t (hk : 𝗽₁)
    (hη : 𝔜) (ht : 𝔑)
    (hfield : 𝔲) (hvariance : 𝔘)
    (hmean : 𝔔) :
    𝕶 ≤
       40 ^ d * 𝔵 ^ 2 *
        Real.exp 𝔵 * 𝚍 * 𝗩 / 𝗋 := by
  let K := 𝔵
  let B := 𝔛 * 𝔄 *
    𝔖
  have hkp : 𝖰 := 𝖡₃
  have hbudget : 𝕶 ≤ B := by
    calc
      _ ≤ ∑ ξ, activationProductPrior 𝔄 t ξ * B := by
        apply Finset.sum_le_sum
        intro ξ _
        exact mul_le_mul_of_nonneg_left
          (𝕮 grid_full_score_design_energy_bound hkp hη ht hfield hvariance hmean)
          $ Finset.prod_nonneg fun i _ => activation_prior_nonnegative t ht.1 ht.2 $ ξ i
      _ = B := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]
  have hm : (𝔄 : ℝ) ≤ 𝕹 := by
    simpa only [gridWindowCount, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      pow_le_pow_left₀ 𝖠₃ (by exact_mod_cast 𝖡₃ ) d
  calc
    _ ≤ B := hbudget
    _ ≤ 𝔛 * 𝕹 *
        𝔖 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm $ by positivity ) $ by positivity
    𝘿 := by
      rw [show (40 : ℝ) = 5 * 2 ^ 3 by norm_num]
      have htwo : (2 ^ 3) ^ d = 𝕲 ^ 3 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 d]
      simp only [mul_pow, div_pow]
      grind

𝗇 𝔪 (𝙼₂ x).trans
/-- The actual model parameter in each latent state of the indexed grid prior. -/
def gridPathParameter (C : ModelConstants d) (P : LowSmoothnessTernaryConstants C)
    (k : ℕ) (η t : ℝ) (ξ : 𝔱)
    (hη : 𝔜) (ht : t ∈ Icc 𝙋 1)
    (hfield : (𝕲 + 2) * η ≤ P.ρ) (hvariance : 𝔘) :
    RegressionParameter d :=
  P.pathParameter 𝔠 (indexedGridField_continuous d k η ξ) η t ht hvariance
     fun x => 𝔪 𝖥₃

𝗇 𝕺 𝗞₁
theorem gridPathParameter_admissible (C : ModelConstants d)
    P (k : ℕ) η b t
    ξ (hk : 𝗽₁) (hs1 : 𝘒₂)
    (hb : 𝘸) hη ht
    hfield hvariance
    (hscale : η = b / 𝙦 ^ C.smoothness)
    (hholder : (𝔶 + 68 * 𝔶 * 𝕺) * b ≤ C.holderBound) :
    Admissible C $ gridPathParameter C P k η t ξ hη ht hfield hvariance := by
  have horder : C.order = 0 := by
    have ho := C.order_lt.trans_le hs1
    simp_all
  have hηb : η ≤ b := by
    rw [hscale]
    exact div_le_self hb $ Real.one_le_rpow (by exact_mod_cast hk) C.smoothness_pos.le
  apply P.pathParameter_admissible_order_zero _ _ η t ht hvariance _ horder
    (𝗝 * b) ( 68 * 𝗝 * 𝕺 * b)
     𝖠₃ 𝖠₃ 𝖡₄
  · intro x
    exact 𝔪 $ mul_le_mul_of_nonneg_left hηb 𝖠₃
  · intro x y
    rw [hscale, indexedGridField_eq]
    exact gridPriorField_holder_bound d k C.smoothness b hk C.smoothness_pos.le hs1 hb _ x y
