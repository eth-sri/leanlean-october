module

public import NearlyMinimax.FinitePartitionMoments
public import NearlyMinimax.ObservationMoments
public import NearlyMinimax.PairUStatistic
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Fourth-moment and row-localization estimates for the actual same-cell
pair-difference score. Responses are allowed to be unbounded. -/
𝛅
𝚨
𝚬
𝚩

section Partition
variable {X B : Type*} [MeasurableSpace X] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableEq B]
  (μ : Measure X) [IsProbabilityMeasure μ] (label : X → B) (hlabel : Measurable label)
include hlabel

𝗇 𝔓 X → ℝ
𝗇 𝔗 𝚌₁
𝗇 𝔙 X × X
def labelLocalizedKernel (g : 𝔓) (z : 𝔙) : ℝ :=
  if 𝔗 then g z.2 else 0

𝗇 𝔘 𝗝₁
𝗇 𝔵 labelLocalizedKernel label g
𝗃 𝔷 Integrable ἀ μ
theorem labelLocalizedKernel_integrable g (hg : 𝔷 g) :
    Integrable 𝔵 $ μ.prod μ := by
  exact (hg.comp_snd μ).indicator
    𝔘

𝗇 𝔉 𝗃₂
𝗇 𝔳 𝖮
omit hlabel in
theorem labelLocalizedKernel_row (g : 𝔓) (x : X) :
     ∫ y, 𝔵 𝔳 ∂μ =
      ∫ y, (𝔉).indicator g y ∂μ := by
  congr 1
  funext y
  simp [labelLocalizedKernel, Set.indicator_apply, eq_comm]

𝗇 𝔄 label ⁻¹' 𝚕₂
𝗇 𝔪 fun x => μ.real 𝔉
𝗇 𝔫 fun c => μ.real 𝔄
theorem partition_mass_integrable :
    𝔷 𝔪 := by
  have hm : Measurable 𝔪 :=
    (measurable_of_countable 𝔫).comp hlabel
  apply (MemLp.of_bound hm.aestronglyMeasurable 1 (p := 1) ?_).integrable 𝖠₄
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

𝗃 𝔨 ἀ μ label hlabel
𝗇 𝔔 𝔨 labelLocalizedKernel_integrable g hg
𝗇 𝔖 ∫ z, 𝔵 z ∂μ.prod μ
𝗇 𝔟 (𝔄).indicator
𝗃 𝔩 ∫ x, 𝔟 ἀ x ∂μ
𝗇 𝔢 𝔩 g
𝗇 𝔬 ∑ c : B, μ.real 𝔄 ^ 2
𝗇 𝔲 labelLocalizedKernel_row μ label g
theorem labelLocalizedKernel_integral_le g (hg : 𝔷 g)
    M (hloc : ∀ c ,
      𝔢 ≤ M * μ.real 𝔄) :
    𝔖 ≤
      M * 𝔬 := by
  rw [integral_prod _ 𝔔]
  simp_rw [𝔲]
  have hi := (𝔔).integral_prod_left
  simp_rw [𝔲] at hi
  calc
    _ ≤ ∫ x, M * μ.real 𝔉 ∂μ := by
      apply integral_mono hi $ (𝔨 partition_mass_integrable).const_mul M
      tauto
    𝘿 := by
      rw [integral_const_mul,
        𝔨 finite_label_integral 𝔫]
      ring

theorem labelLocalizedKernel_integral g (hg : 𝔷 g) :
    𝔖 =
      ∑ c : B, μ.real 𝔄 *
        𝔢 := by
  rw [integral_prod _ 𝔔]
  simp_rw [𝔲]
  exact 𝔨 finite_label_integral
     fun c => 𝔢

𝗇 𝔶 sameLabelKernel label z
𝗇 𝔏 𝔶 * r z.1 * r z.2
omit hlabel in
theorem sameLabelKernel_mul_eq_sum (r : 𝔓) (z : 𝔙) :
    𝔏 =
      ∑ c : B, 𝔟 r z.1 * 𝔟 r z.2 := by
  rw [Finset.sum_eq_single $ label z.1 ]
  · by_cases he : 𝔗
    · simp [sameLabelKernel, Set.indicator_apply, he]
    · simp [sameLabelKernel, Set.indicator_apply, he, Ne.symm he]
  · intro c hc hne
    have hn : label z.1 ≠ c := Ne.symm hne
    simp [Set.indicator_apply, hn]
  · simp

𝗇 𝔴 (measurableSet_singleton _).preimage hlabel
𝗇 𝔍 hr.indicator 𝔴
𝗃 𝕮 Integrable (fun z => ἀ) $ μ.prod μ
theorem sameLabelKernel_mul_integrable r (hr : 𝔷 r) :
    𝕮 𝔏 := by
  simp_rw [sameLabelKernel_mul_eq_sum label r]
  apply integrable_finsetSum
  intro c hc
  exact (𝔍).mul_prod
    𝔍

𝗇 𝔥 𝔩 r ^ 2
𝗃 𝕯 ∫ z, ἀ ∂μ.prod μ
theorem sameLabelKernel_mul_integral r (hr : 𝔷 r) :
    𝕯 𝔏 =
      ∑ c : B, 𝔥 := by
  simp_rw [sameLabelKernel_mul_eq_sum label r]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c hc
    rw [integral_prod_mul]
    ring
  · intro c hc
    exact (𝔍).mul_prod
      𝔍

𝗇 𝔊 (r z.1 - r z.2) ^ 2 / 2
def pairWindowScore (r : 𝔓) (V : ℝ) (z : 𝔙) : ℝ :=
  if 𝔗 then 𝔊 - V else 0

𝗃 𝕬 ἀ label r V
𝗇 𝔦 𝕬 pairWindowScore
𝗇 𝔚 𝔦
theorem pairWindowScore_measurable r (hr : Measurable r) V :
    Measurable 𝔚 := Measurable.ite
    𝔘
    ((((hr.comp measurable_fst).sub $ hr.comp measurable_snd ).pow_const 2
      |>.div_const 2).sub measurable_const) measurable_const

𝗇 𝔅 𝔦 𝔳
omit hlabel in
theorem pairWindowScore_symmetric (r : 𝔓) (V : ℝ) (x y : X) :
    𝔅 = 𝔦 𝘮₂ := by
  unfold pairWindowScore
  simp only [Prod.fst, Prod.snd, eq_comm]
  split_ifs <;> ring

𝗇 𝔑 𝔦 z
omit hlabel in
theorem pairWindowScore_abs_le (r : 𝔓) (V : ℝ) (z : 𝔙) :
    |𝔑| ≤ r z.1 ^ 2 + r z.2 ^ 2 + |V| := by
  unfold pairWindowScore
  split_ifs with h
  · calc
      _ ≤ |𝔊| + |V| := abs_sub _ _
      𝖦 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 𝔊)]
        nlinarith [sq_nonneg $ r z.1 + r z.2 ]
  · simp only [abs_zero]
    positivity

𝗃 𝕭 ἀ ^ 2
𝗇 𝔣 2 * 𝕭 V
𝗇 𝔐 4 * (r z.1 ^ 4 + r z.2 ^ 4) + 𝔣
omit hlabel in
theorem pairWindowScore_sq_le (r : 𝔓) (V : ℝ) (z : 𝔙) :
    𝕭 𝔑 ≤
      𝔐 := by
  unfold pairWindowScore
  split_ifs with h
  · have h1 := add_sq_le (a := 𝔊) (b := -V)
    have h2 := (show Even (4 : ℕ) by decide).add_pow_le
      (a := r z.1) (b := -r z.2)
    norm_num at h2
    nlinarith
  · simp only [zero_pow (by decide : 𝗟 ≠ 0)]
    positivity

𝗇 𝔧 r x ^ 4
𝗇 𝔇 fun x => 𝔧
𝗇 𝔛 pairWindowScore_measurable label hlabel r hr V
theorem pairWindowScore_memLp r (hr : Measurable r) V
    (h4 : 𝔷 𝔇) :
    MemLp 𝔚 2 $ μ.prod μ := by
  apply (memLp_two_iff_integrable_sq
    (𝔛).aestronglyMeasurable).mpr
  have hd : 𝕮 𝔐 :=
    (((h4.comp_fst μ).add $ h4.comp_snd μ ).const_mul 4).add $ integrable_const _
  apply hd.mono'
    ((𝔛).pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, 𝗤]
  exact 𝕬 pairWindowScore_sq_le z

omit hlabel in
theorem pairWindowScore_local_sq_le (r : 𝔓) (V : ℝ) (z : 𝔙) :
    𝕭 𝔑 ≤
      4 * (labelLocalizedKernel label 𝔇 z +
        labelLocalizedKernel label 𝔇 z.swap) +
      𝔣 * 𝔶 := by
  by_cases h : 𝔗
  · have hb := 𝕬 pairWindowScore_sq_le z
    simp only [pairWindowScore, labelLocalizedKernel, sameLabelKernel,
      Prod.fst_swap, Prod.snd_swap, if_pos h, if_pos h.symm] at hb ⊢
    nlinarith
  · simp [pairWindowScore, labelLocalizedKernel, sameLabelKernel, h, Ne.symm h]

𝗇 𝔎 L z + L z.swap
𝗇 𝔒 integral_add (f := L) (g := fun z => L z.swap) hiL hiL.swap
𝗇 𝔜 𝔨 pairWindowScore_memLp r hr V h4
𝗇 𝔰 (hiL.add hiL.swap).const_mul 4
theorem pairWindowScore_energy_le r (hr : Measurable r) V M4
    (h4 : 𝔷 𝔇)
    (hloc : ∀ c , 𝔩 𝔇 ≤
      M4 * μ.real 𝔄) :
     ∫ z, 𝕭 𝔑 ∂μ.prod μ ≤
      (8 * M4 + 𝔣) * 𝔬 := by
  let L := labelLocalizedKernel label 𝔇
  have hiL :=
    𝔨 labelLocalizedKernel_integrable _ h4
  have hiD := (𝔨 sameLabelKernel_memLp).integrable 𝖠₄
  have hd : Integrable (fun z => 4 * 𝔎 +
      𝔣 * 𝔶) $ μ.prod μ :=
    (𝔰).add $ hiD.const_mul _
  have hb := integral_mono (𝔜).integrable_sq
    hd 𝕬 pairWindowScore_local_sq_le
  rw [integral_add
      (f := fun z => 4 * 𝔎)

      𝔰 $ hiD.const_mul _ ,
    integral_const_mul, 𝔒,
    integral_prod_swap L, integral_const_mul, 𝔨 sameLabelKernel_integral] at hb
  have hL := 𝔨 labelLocalizedKernel_integral_le _ h4 M4 hloc
  linarith

𝗇 𝔞 r y ^ 2
𝗇 𝔈 r x ^ 2
𝗇 𝔠 ∫ x, 𝔟 (fun x => 𝔈) x ∂μ
𝗇 𝔡 ∫ y, 𝔅 ∂μ
𝗇 𝔤 fun x => 𝔈
𝗇 𝔭 ∀ c , 𝔠 ≤ M2 * μ.real 𝔄
𝗇 𝔮 ∫ y, e y ∂μ
theorem pairWindowScore_row_abs_le r (hr : Measurable r) V M2
    (h2 : 𝔷 𝔤)
    (hloc : 𝔭) x :
    |𝔡| ≤
      μ.real 𝔉 * (𝔈 + |V| + M2) := by
  let A := 𝔉
  have hA : MeasurableSet A := 𝔴
  let e := fun y => A.indicator (fun y => 𝔈 + 𝔞 + |V|) y
  have hiE :=
    (((integrable_const 𝔈).add h2).add $ integrable_const |V| ).indicator hA
  have hpoint : ∀ y, ‖𝔅‖ ≤ e y := by
    intro y
    by_cases he : label x = label y
    · simpa only [Real.norm_eq_abs, e, A, Set.indicator_of_mem
        $ show y ∈ A from he.symm ] using 𝕬 pairWindowScore_abs_le 𝔳
    · simp [pairWindowScore, e, A, he, Ne.symm he]
  have hiS : Integrable (fun y => 𝔅) μ := by
    apply hiE.mono' ((𝔛).comp
      $ measurable_const.prodMk measurable_id ).aestronglyMeasurable
    exact Eventually.of_forall hpoint
  have hb : |𝔡| ≤ 𝔮 := by
    calc
      _ = ‖𝔡‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ‖𝔅‖ ∂μ := norm_integral_le_integral_norm _
      𝖦 := integral_mono hiS.norm hiE hpoint
  have heq : 𝔮 = μ.real A * (𝔈 + |V|) +
      ∫ y, A.indicator (fun y => 𝔞) y ∂μ := by
    rw [integral_indicator hA]
    have he : (fun y => 𝔈 + 𝔞 + |V|) =
         fun y => 𝔈 + |V| + 𝔞 := 𝖥₄
    rw [he, 𝖻₁ h2.restrict,
      integral_const, ← integral_indicator hA]
    simp
  grind

𝗇 𝔯 2 * 𝕭 cap
theorem pairWindowScore_row_energy_le r (hr : Measurable r)
    V M2 M4 cap (hM2 : 0 ≤ M2) (hcap : 0 ≤ cap)
    (h2 : 𝔷 𝔤)
    (h4 : 𝔷 𝔇)
    (hglobal : ∫ x, 𝔧 ∂μ ≤ M4)
    (hloc : 𝔭)
    (hmass : ∀ c , μ.real 𝔄 ≤ cap) :
     ∫ x, 𝕭 𝔡 ∂μ ≤
      𝔯 * (M4 + (|V| + M2) ^ 2) := by
  have hi := PairUStatistic.rowIntegral_sq_integrable
    𝔜
  have hd : Integrable (fun x => 𝔯 * (𝔧 + (|V| + M2) ^ 2)) μ :=
    (h4.add $ integrable_const _ ).const_mul _
  have hp : ∀ x, 𝕭 𝔡 ≤
      𝔯 * (𝔧 + (|V| + M2) ^ 2) := by
    intro x
    let p := μ.real 𝔉
    have hpc := hmass $ label x
    calc
      _ = |𝔡| ^ 2 := (sq_abs _).symm
      _ ≤ (p * (𝔈 + |V| + M2)) ^ 2 :=
        𝗂 (𝔨 pairWindowScore_row_abs_le r hr V M2 h2 hloc x) 2
      _ = 𝕭 p * (𝔈 + (|V| + M2)) ^ 2 := 𝖢₃
      _ ≤ 𝕭 cap * (𝔈 + (|V| + M2)) ^ 2 := 𝖩₃
      _ ≤ 𝕭 cap * (2 * (𝕭 𝔈 + (|V| + M2) ^ 2)) := mul_le_mul_of_nonneg_left add_sq_le $ sq_nonneg cap
      𝘿 := 𝖢₃
  have hb := integral_mono hi hd hp
  rw [integral_const_mul, integral_add h4 $ integrable_const _ , integral_const] at hb
  simp at hb
  exact hb.trans $ mul_le_mul_of_nonneg_left (add_le_add hglobal le_rfl) 𝖠₃

𝗇 𝔱 (hiL.add hiL.swap).div_const 2
theorem pairWindowScore_integral r (hr : Measurable r) V
    (hr2 : MemLp r 2 μ) :
    𝕯 𝔑 =
      ∑ c : B, (μ.real 𝔄 *
        𝔠 -
        𝔥 -
        V * μ.real 𝔄 ^ 2) := by
  let L := labelLocalizedKernel label 𝔤
  let Q := fun z => 𝔏
  have hiL :=
    𝔨 labelLocalizedKernel_integrable _ hr2.integrable_sq
  have hiQ :=
    𝔨 sameLabelKernel_mul_integrable r $ hr2.integrable 𝖠₄
  have hiD := (𝔨 sameLabelKernel_memLp).integrable 𝖠₄
  have heq : 𝔚 =
       fun z => 𝔎 / 2 - Q z - V * 𝔶 := by
    funext z
    dsimp [pairWindowScore, L, Q, labelLocalizedKernel, sameLabelKernel]
    grind
  rw [heq, integral_sub
      (f := fun z => 𝔎 / 2 - Q z)

      ((𝔱).sub hiQ) $ hiD.const_mul V ,
    integral_sub (f := fun z => 𝔎 / 2)
      𝔱 hiQ,
    integral_div, 𝔒,
    integral_prod_swap L, integral_const_mul]
  rw [𝔨 labelLocalizedKernel_integral _ hr2.integrable_sq,
    𝔨 sameLabelKernel_mul_integral r $ hr2.integrable 𝖠₄ ,
    𝔨 sameLabelKernel_integral]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
