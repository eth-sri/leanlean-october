module

public import NearlyMinimax.LowSmoothnessPrior
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Exact restriction of actual patch scores to their observed support.
The resulting estimates depend on the actual patch count, while regression
values and weights may depend arbitrarily on the observed design tuple. -/

𝚴

𝚨

𝚬

𝗃 𝕱 g i + η * w i * ἀ
𝗇 𝔫 ternaryMass a 𝕱 z V
𝗇 𝔅 𝔫 $ y i
𝗇 𝔑 ∀ k, 0 < ternaryMass a 𝚢₁ V (y k)
𝗃 𝔬 ἀ n a V η
𝗃 𝕮 𝔬 ἀ g w y z
𝗇 𝔘 𝕮 patchResponseProduct
𝗇 𝔣 𝙔
𝗇 𝔧 𝙿 / 𝔅
𝗇 𝔮 𝙈
private theorem patch_variance_ratio' (n : ℕ) (a V η z : ℝ) (g w : 𝔣)
    (y : 𝔮) (i : Fin n)
    (hp : 𝔑) :
    𝕮 patchVarianceTerm i / 𝔘 =
      𝔧 := by
  unfold patchVarianceTerm patchResponseProduct
  rw [← 𝗑₂]
  exact mul_div_mul_right _ _ 𝘃₁

𝗇 𝔎 𝕮 patchObservableScore
𝗇 𝔨 𝔬 patchResponseProduct g w y
𝗃 𝕲 ἀ ^ 2
𝗃 𝕳 𝔬 ἀ z g w
theorem patch_score_ratio_formula n a V η z g w
    y
    (hp : 𝔑) :
    𝔎 =
      symmetricDifference 𝔨 /
        𝔘 -
      𝕲 η * ∑ i, 𝖩 *
        𝔧 := by
  unfold patchObservableScore patchScoreNumerator
  rw [sub_div]
  simp_rw [mul_div_assoc, Finset.sum_div, mul_div_assoc, 𝕳 patch_variance_ratio' y _ hp]

𝗇 𝔍 𝖥₁
𝗃 𝕯 ἀ $ e i
𝗇 𝔏 𝕯 y
𝗃 𝕷 fun i => 𝕯 ἀ
𝗇 𝔔 𝕷 g
𝗇 𝔖 𝕷 w
𝗇 𝔠 𝙍
𝗃 𝕸 fun i => ἀ
𝗇 𝔥 𝕸 𝔏
𝗃 𝔭 fun _ => ἀ
𝗃 𝕺 (ἀ e _ _ 𝔭 rfl).symm
/-- Exact restriction to the patch, under any enumeration of its observation indices. -/
theorem patch_score_restrict n k a V η z g w
    (S : 𝔠) (e : Fin k ≃ S) (hw : 𝔍)
    y
    (hp : ∀ i, 0 < 𝔅) :
    𝔎 =
      patchObservableScore k a V η 𝔔 𝔖
        𝔥 z := by
  let O := ∏ i ∈ Finset.univ \ S, ternaryMass a (g i) V (y i)
  have hO : O ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    grind
  have hfactor u : 𝔨 u =
      O * patchResponseProduct k a V η 𝔔 𝔖
        𝔥 u := by
    unfold patchResponseProduct
    rw [← Finset.prod_sdiff $ Finset.subset_univ S ]
    congr 1
    · apply Finset.prod_congr rfl
      simp_all
    · rw [Finset.prod_subtype S 𝔭 Iff.rfl]
      exact 𝕺 Fintype.prod_equiv
  rw [𝕳 patch_score_ratio_formula y hp,
    patch_score_ratio_formula k a V η z _ _ _ 𝕷 hp]
  congr 1
  · unfold symmetricDifference
    grind
  · congr 1
    rw [← Finset.sum_subset $ Finset.subset_univ S ]
    · rw [Finset.sum_subtype S 𝔭 Iff.rfl]
      exact 𝕺 Fintype.sum_equiv
    simp_all

/-- The full patch score vanishes when its actual observed support has size at most one. -/
theorem patch_score_zero_of_support_count_lt_two n a V η z
    g w (S : 𝔠) (hw : 𝔍)
    y (ha : 𝙞) (hcount : S.card < 2) :
    𝔎 = 0 := by
  have hcases : S.card = 0 ∨ S.card = 1 := 𝖡₃
  rcases hcases with hzero | hone
  · simp [patchObservableScore, 𝕮 patch_score_cancel_zero fun i => hw i 𝖤₄ ]
  · obtain ⟨i, hS⟩ := Finset.card_eq_one.mp hone
    have hnum := 𝕮 patch_score_cancel_singleton ha i
       fun k hki => hw k 𝖤₄
    simp [patchObservableScore, hnum]

𝗇 𝔇 Icc (-1) 1
𝗇 𝔉 𝕱 u
𝗇 𝕬 𝗩
𝗇 𝔗 ternaryScoreExponentialConstant a ρ c ^ S.card * 𝕬
𝗇 𝔙 (e i).property
𝗇 𝔢 𝕲 a
𝗇 𝔩 ternaryMass a 𝔉 V
𝗃 𝕶 ἀ u hu (e i) 𝔙
𝗇 𝔰 𝕶 hq
𝗇 𝔲 𝙆
𝗇 𝔳 𝗛₁
𝗇 𝔴 𝘝
𝗇 𝔵 z ∈ 𝔇
𝗃 𝕴 fun i => ἀ a ha 𝔏
𝗃 𝕹 fun i => 𝕯 ἀ 𝔙
/-- Actual full-response score bound with the size of its observed support.
The field and weights may be any functions of the design tuple. -/
theorem patch_score_square_support_bound n a V η z ρ c
    g w (S : 𝔠) y
    (hcount : 1 ≤ S.card) (ha : 𝔲) (hρ : 𝔳) (hc : 𝔴)
    (hz : 𝔵) (hwzero : 𝔍)
    (hw : ∀ i ∈ S, |w i| ≤ 1)
    (hreg : ∀ u ∈ 𝔇, ∀ i ∈ S, |𝔉| ≤ ρ)
    (hq : ∀ u ∈ 𝔇, ∀ i ∈ S,
      0 ≤ 𝔩 (y i) ∧
        𝔩 (y i) ≤ 1)
    (hlower : ∀ i ∈ S, c ≤ 𝔅)
    (hp : ∀ i, 0 < 𝔅) :
    𝕲 𝔎 ≤
      𝔗 := by
  let e := S.equivFin.symm
  rw [patch_score_restrict n S.card a V η z g w S e hwzero y hp]
  let M := 𝗠 / 𝔢
  let K := 𝕲 M + 3 / 𝔢
  have hs := patch_score_square_bound S.card a V η z M (2 / 𝔢) (1 / 𝔢) c
    𝔔 𝔖 𝔥 hcount hz
     𝖠₃   𝖠₃   𝖠₃  hc
    𝕹 hw
    (fun u hu i => (abs_of_nonneg (𝔰).1).trans_le
      (𝔰).2)
    (fun u hu i => 𝗥₁
      𝕶 hreg 𝔏)
    𝕴 ternary_mean_second_derivative_abs_bound
    𝕴 ternary_variance_derivative_abs_bound
    𝕹 hlower
  have hK : 𝕲 M + 2 / 𝔢 + 1 / 𝔢 = K := 𝖢₃
  rw [hK] at hs
  simpa [ternaryScoreExponentialConstant, K, M] using
    score_bound_exponential_absorption S.card K c η _ hcount hc hs

𝗇 𝔞 𝔫 y
/-- Genuine full conditional response energy has the collision envelope,
with the actual support count rather than an assumed restricted experiment. -/
theorem patch_expected_score_energy_support_bound n a V η z ρ c
    g w (S : 𝔠)
    (ha : 𝔲) (hρ : 𝔳) (hc : 𝔴)
    (hz : 𝔵) (hwzero : 𝔍)
    (hw : ∀ i ∈ S, |w i| ≤ 1)
    (hreg : ∀ u ∈ 𝔇, ∀ i ∈ S, |𝔉| ≤ ρ)
    (hq : ∀ u ∈ 𝔇, ∀ i ∈ S, ∀ y,
      0 ≤ 𝔩 y ∧
        𝔩 y ≤ 1)
    (hlower : ∀ i ∈ S, ∀ y, c ≤ 𝔞)
    (hp : ∀ i y, 0 < 𝔞) :
    𝔬 patchExpectedScoreEnergy g w z ≤
      if 2 ≤ S.card then 𝔗 else 0 := by
  split_ifs with hcount
  · calc
      _ ≤ ∑ y : 𝔮, 𝔘 *
          𝔗 := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left
          (𝔬 patch_score_square_support_bound z ρ c g w S y  𝖡₃ 
            ha hρ hc hz hwzero hw hreg (fun u hu i hi => hq u hu i hi $ y i )
            (fun i hi => hlower i hi $ y i ) 𝕸 𝚗₁)
          $ Finset.prod_nonneg fun i _ => (𝚗₁).le
      𝘿 := by rw [← Finset.sum_mul, 𝔬 patch_response_normalized g w z ha.ne', one_mul]
  · apply le_of_eq
    apply Finset.sum_eq_zero
    intro y _
    rw [𝕳 patch_score_zero_of_support_count_lt_two S hwzero y ha.ne' 𝖡₃ ]
    ring

𝗇 𝔪 w x i
𝗃 𝕵 g x i + η * 𝔪 * ἀ
𝗇 𝔄 𝕵 u
𝗃 𝕭 𝔬 ἀ (g x) $ w x
𝗇 𝔈 𝕭 patchExpectedScoreEnergy z
𝗇 𝔒 ∀ i, Measurable fun x => g x i
𝗃 𝕰 fun x => ἀ
𝗇 𝔓 ∀ i, Measurable 𝕰 𝔪
𝗇 𝔛 𝕭 patchVarianceTerm y z i
𝗇 𝔤 ternaryMass a 𝔄 V y
𝗇 𝔦 𝕰 𝔈
𝗇 𝔶 𝙖
theorem patch_expected_score_energy_measurable [MeasurableSpace α]
    n a V η z (g w : α → 𝔣)
    (hg : 𝔒) (hw : 𝔓) :
    Measurable 𝔦 := by
  have hq u i y :
      Measurable 𝕰 𝔤 := by
    apply ternaryMass_measurable_comp
    fun_prop
  have hprod s u (y : 𝔮) :
      Measurable fun x => ∏ i ∈ s, ternaryMass a 𝔄 V (y i) :=
    Finset.measurable_prod _ fun i _ => hq u i $ y i
  have hpatch u y :
      Measurable fun x => 𝕭 patchResponseProduct y u := hprod _ u y
  have hvar i y :
      Measurable 𝕰 𝔛 :=
    (hprod (Finset.univ.erase i) z y).const_mul _
  have hscore y :
      Measurable fun x => 𝕭 patchObservableScore y z := by
    have hcorr : Measurable fun x => ∑ i, 𝕲 𝔪 *
        𝔛 :=
      Finset.measurable_sum _ fun i _ => (hw i).pow_const 2 |>.mul (hvar i y)
    exact (((hpatch 1 y).const_mul 𝔶 |>.add ((hpatch (-1) y).const_mul 𝔶)
      |>.sub (hpatch 0 y)).sub $ hcorr.const_mul 𝕲 η ).div $ hpatch z y
  exact Finset.measurable_sum _ fun y _ => (hpatch z y).mul $ (hscore y).pow_const 2

section

variable [MeasurableSpace α]
    (μ : Measure α)
    (n)

𝗇 𝔚 Measure.pi 𝔭 μ
𝗇 𝔟 𝗉
𝗇 𝔱 designPatchCount n A x
/-- Every function of the actual bounded design count is integrable. -/
theorem iid_design_count_observable_integrable [IsProbabilityMeasure μ] A (hA : MeasurableSet A)
    (e : 𝙜) :
    Integrable (fun x => e 𝔱)
      𝔚 := by
  apply Integrable.of_bound
    ((measurable_of_countable e).comp $ design_patch_count_measurable n A hA ).aestronglyMeasurable
    $ ∑ k ∈ Finset.range 𝔟, |e k|
  apply Filter.Eventually.of_forall
  intro x
  exact Finset.single_le_sum (fun k _ => abs_nonneg $ e k )
    $ Finset.mem_range.mpr $ Nat.lt_succ_iff.mpr $ design_patch_count_le n A x

𝗇 𝔊 ternaryMass a 𝕵 z V y
𝗇 𝔐 (hS i).mp hi
𝗇 𝔜 x i ∈ A
𝗇 𝔡 ternaryScoreExponentialConstant a ρ c
𝗇 𝔯 𝚅₁
𝗇 𝔷 0 ≤ 𝔤 ∧ 𝔤 ≤ 1
/-- The actual full conditional response energy, integrated over a genuine
IID design, satisfies the collision bound even when all fields depend on
the complete observed design tuple. -/
theorem iid_design_full_patch_score_energy_bound [IsProbabilityMeasure μ] A (hA : MeasurableSet A)
    a V η z ρ c (g w : 𝔯 → 𝔣)
    (hg : 𝔒) (hwmeas : 𝔓)
    (ha : 𝔲) (hρ : 𝔳) (hc : 𝔴) (hz : 𝔵)
    (hmean : n * μ.real A ≤ 1)
    (hwzero : ∀ x i, x i ∉ A → 𝔪 = 0)
    (hw : ∀ x i, 𝔜 → |𝔪| ≤ 1)
    (hreg : ∀ x, ∀ u ∈ 𝔇, ∀ i, 𝔜 → |𝔄| ≤ ρ)
    (hq : ∀ x, ∀ u ∈ 𝔇, ∀ i, 𝔜 → ∀ y,
      𝔷)
    (hlower : ∀ x i, 𝔜 → ∀ y, c ≤ 𝔊)
    (hp : ∀ x i y, 0 < 𝔊) :
     ∫ x : 𝔯, 𝔈
      ∂ 𝔚 ≤
      𝕲 𝔡 * Real.exp 𝔡 *
        𝕬 * (n * μ.real A) ^ 2 := by
  let K := 𝔡
  let e := fun k => if 𝚂 then K ^ k * 𝕬 else 0
  have hpoint (x : 𝔯) : 𝔈 ≤
      e 𝔱 := by
    let S := Finset.univ.filter 𝕸 𝔜
    have hS (i : Fin n) : 𝚒₁ ↔ 𝔜 := 𝖤₃
    exact 𝔬 patch_expected_score_energy_support_bound z ρ c (g x) (w x) S ha hρ hc hz
      (fun i hi => hwzero x i fun h => hi $ (hS i).mpr h )
      (fun i hi => hw x i 𝔐)
      (fun u hu i hi => hreg x u hu i 𝔐)
      (fun u hu i hi y => hq x u hu i 𝔐 y)
      (fun i hi y => hlower x i 𝔐 y) $ hp x
  have he := iid_design_count_observable_integrable μ n A hA e
  have henergy : Integrable 𝔦
      𝔚 := by
    apply he.mono' (𝕳 patch_expected_score_energy_measurable hg hwmeas).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint x
    · exact Finset.sum_nonneg fun y _ => mul_nonneg
        (Finset.prod_nonneg fun i _ => (hp x i $ y i ).le ) $ sq_nonneg _
  exact (integral_mono henergy he hpoint).trans
    $ iid_design_collision_energy_bound μ n A hA K η e (by dsimp [K, ternaryScoreExponentialConstant]; positivity) hmean  𝖦₄ 
       𝖦₄  fun k hk => 𝖤₃

/-- Uniform legal fields make their actual conditional response energies
integrable; no energy or integrability conclusion is assumed. -/
theorem patch_expected_score_energy_integrable [IsFiniteMeasure μ] a V η z ρ c (g w : α → 𝔣)
    (hg : 𝔒) (hwmeas : 𝔓)
    (ha : 𝔲) (hρ : 𝔳) (hc : 𝔴) (hz : 𝔵)
    (hw : ∀ x i, |𝔪| ≤ 1)
    (hreg : ∀ x, ∀ u ∈ 𝔇, ∀ i, |𝔄| ≤ ρ)
    (hq : ∀ x, ∀ u ∈ 𝔇, ∀ i y,
      𝔷)
    (hlower : ∀ x i y, c ≤ 𝔊) :
    Integrable 𝔦 μ := by
  cases n with
  | zero =>
    simp_rw [patch_expected_score_energy_zero]
    exact integrable_zero ..
  | succ n =>
    apply Integrable.of_bound
      (patch_expected_score_energy_measurable 𝔟 a V η z g w hg hwmeas).aestronglyMeasurable
      $ 𝔡 ^ 𝔟 * 𝕬
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact patch_expected_score_energy_bound 𝔟 a V η z ρ c (g x) (w x)  𝖡₃ 
        ha hρ hc hz (hw x) (hreg x) (hq x) $ hlower x
    · exact Finset.sum_nonneg fun y _ => mul_nonneg
        (Finset.prod_nonneg fun i _ => (hq x z hz i $ y i ).1 ) $ sq_nonneg _
