module

public import NearlyMinimax.PairCounting
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Order-two kernel estimates for genuine independent observations. -/
𝚵
open scoped Classical
namespace NearlyMinimax.PairUStatistic
𝚩

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable {ν : Measure Ω} {μ : Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] in
theorem integral_comp_measurePreserving (f : Ω → E)
    (hf : MeasurePreserving f ν μ) (g : 𝙏) (hg : Measurable g) :
     ∫ x, g (f x) ∂ν = ∫ y, g y ∂μ := by
  rw [← hf.map_eq]
  exact (integral_map hf.aemeasurable hg.aestronglyMeasurable).symm

𝗃 𝕳 X ἀ x
𝗇 𝔴 𝕳 i
𝗇 𝔵 𝕳 j
𝗇 𝔄 (𝔴, 𝔵)
𝗇 𝔇 𝗿
𝗇 𝔒 iIndepFun X ν
𝗃 𝕰 (hX ἀ).measurable
𝗇 𝔓 (hX i).measurable.prodMk 𝕰 j
𝗇 𝔘 𝘚₁
𝗃 𝔩 fun x => ἀ
𝗇 𝔫 ι → Ω → E
𝗃 𝕱 (hX ἀ).aemeasurable
omit [IsProbabilityMeasure μ] in
theorem pair_measurePreserving (X : 𝔫)
    (hind : 𝔒) (hX : 𝔇)
    (hij : 𝔘) :
    MeasurePreserving 𝔩 𝔄 ν $ μ.prod μ := by
  refine ⟨ 𝔓, ?_⟩
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map 𝕱 i
    𝕱 j, (hX i).map_eq, (hX j).map_eq]

𝗇 𝔐 𝖳₁ μ
𝗃 𝔨 ἀ X hind hX
𝗇 𝔙 𝔨 pair_measurePreserving hij
𝗇 𝔛 fun i => 𝕰 i
𝗇 𝔜 𝕳 k
theorem triple_measurePreserving (X : 𝔫)
    (hind : 𝔒) (hX : 𝔇)
    (hij : 𝔘) (hik : i ≠ k) (hjk : j ≠ k) :
    MeasurePreserving (fun x => (𝔄, 𝔜)) ν 𝔐 := by
  refine ⟨ (𝔓).prodMk 𝕰 k, ?_⟩
  rw [(hind.indepFun_prodMk 𝔛 i j k hik hjk).map_prod_eq_prod_map_map
      ((hX i).aemeasurable.prodMk 𝕱 j) 𝕱 k,
    (𝔙).map_eq, (hX k).map_eq]

𝗇 𝔈 MemLp K 2 $ μ.prod μ
𝗇 𝔎 ∫ z, K z ∂μ.prod μ
𝗇 𝔶 𝖸₂
𝗇 𝔑 𝔶 → ℝ
𝗇 𝔬 fun x => K 𝔄
section

variable (X)
    (hind : 𝔒)
    (hX : 𝔇)
    {K : 𝔑}
    {i j : ι}

include hind hX

theorem kernel_pair_memLp (hK : 𝔈)
    (hij : 𝔘) : MemLp 𝔬 2 ν :=
  hK.comp_measurePreserving 𝔙

theorem kernel_pair_integral (hK : Measurable K) (hij : 𝔘) :
     ∫ x, K 𝔄 ∂ν = 𝔎 :=
  integral_comp_measurePreserving _ 𝔙 K hK

end

𝗇 𝔭 K z.1 * K (z.1.1, z.2)
theorem shared_product_integrable {K : 𝔑} (hK : 𝔈) :
    Integrable (fun z => 𝔭)
      𝔐 := by
  have h₁ : MemLp (fun z => K z.1) 2 𝔐 :=
    hK.comp_measurePreserving measurePreserving_fst
  have hm : MeasurePreserving (fun z => (z.1.1, z.2))
      𝔐 $ μ.prod μ :=
    measurePreserving_fst.prod $ MeasurePreserving.id μ
  exact h₁.integrable_mul $ hK.comp_measurePreserving hm

def rowIntegral (K : 𝔑) (x : E) : ℝ := ∫ y, K 𝖮 ∂μ

𝗇 𝔧 rowIntegral (μ := μ) K
𝗃 𝕵 (ἀ hK).integral_prod_left
theorem row_product_integrable {K } (hK : 𝔈) :
    Integrable (fun z => K z * 𝔧 z.1) $ μ.prod μ := by
  simpa only [integral_const_mul, rowIntegral] using 𝕵 shared_product_integrable

theorem rowIntegral_sq_integrable (hK : 𝔈) :
    Integrable (fun x => 𝔧 x ^ 2) μ := by
  simpa only [integral_mul_const, rowIntegral, pow_two] using 𝕵 row_product_integrable

𝗇 𝔅 ∫ x, 𝔧 x ^ 2 ∂μ
theorem shared_product_integral {K } (hK : 𝔈) :
     ∫ z : 𝔶 × E, 𝔭 ∂ 𝔐 =
      𝔅 := by
  rw [integral_prod _ $ shared_product_integrable hK ]
  simp only [integral_const_mul]
  change ∫ z : 𝔶, K z * rowIntegral K z.1 ∂μ.prod μ = _
  rw [integral_prod _ $ row_product_integrable hK ]
  simp only [integral_mul_const, rowIntegral, pow_two]

𝗇 𝔦 K 𝔄 * K (𝔴, 𝔜)
𝗃 𝕭 ∫ x, ἀ ∂ν
theorem kernel_shared_product_integral (X : 𝔫)
    (hind : 𝔒) (hX : 𝔇)
    (hmK : Measurable K) (hK : 𝔈)
    (hij : 𝔘) (hik : i ≠ k) (hjk : j ≠ k) :
    𝕭 𝔦 =
      𝔅 := by
  exact (integral_comp_measurePreserving _
    (𝔨 triple_measurePreserving hij hik hjk) _ $ (hmK.comp measurable_fst).mul $ hmK.comp $ measurable_fst.fst.prodMk measurable_snd ).trans
    $ shared_product_integral hK

𝗇 𝔔 K (𝕳 k, 𝕳 l)
𝗇 𝔡 𝔨 kernel_pair_integral hmK
𝗇 𝔥 ∫ x, K 𝔄 * 𝔔 ∂ν
theorem kernel_disjoint_product_integral X
    (hind : 𝔒) (hX : 𝔇)
    {K : 𝔑} (hmK : Measurable K)
    {i j k l : ι} (hij : 𝔘) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    𝔥 =
      𝔎 ^ 2 := by
  have hd := (hind.indepFun_prodMk_prodMk 𝔛
    i j k l hik hil hjk hjl).comp hmK hmK
  have he := hd.integral_fun_mul_eq_mul_integral
    (hmK.comp 𝔓).aestronglyMeasurable
    (hmK.comp $ (hX k).measurable.prodMk 𝕰 l ).aestronglyMeasurable
  simp at he
  rw [he, 𝔡 hij, 𝔡 hkl,
    pow_two]

𝗇 𝔷 𝗈
𝗇 𝔉 (𝔷 : ℕ)
𝗇 𝔚 𝙒
𝗇 𝔣 (𝔚 * 𝔉)⁻¹
/-- Ordered-pair U-statistic with its actual finite sample normalization. -/
def pairAverage (n : ℕ) (K : 𝔑) (x : 𝗚₁) : ℝ :=
  𝔣 * ∑ i, ∑ j with 𝖰₁, K (x i, x j)

𝗇 𝔊 ∫ z, K z ^ 2 ∂μ.prod μ
theorem kernel_pair_sq_integral X
    (hind : 𝔒) (hX : 𝔇)
    {K : 𝔑} (hmK : Measurable K) {i j : ι} (hij : 𝔘) :
     ∫ x, K 𝔄 ^ 2 ∂ν = 𝔊 :=
  𝔨 kernel_pair_integral (hmK.pow_const 2) hij

𝗇 𝔍 ∀ x y, K 𝖮 = K 𝘮₂
𝗇 𝔖 K (𝔵, 𝔴)
𝗇 𝔞 K (𝔵, 𝕳 l)
𝗇 𝔢 𝔨 kernel_shared_product_integral hmK hK
𝗃 𝔪 fun x => K 𝔄 * K (𝔜, 𝕳 ἀ)
𝗇 𝔮 j = l
𝗇 𝔯 j = k
𝗇 𝔰 i = k
𝗇 𝔱 𝚛₁
𝗃 𝕲 fun x => K 𝔄 * ἀ
/-- Exact overlap classification for a symmetric kernel. -/
theorem kernel_pair_product_classification X
    (hind : 𝔒) (hX : 𝔇)
    {K } (hmK : Measurable K) (hK : 𝔈)
    (hsym : 𝔍)
    {i j k l : ι} (hij : 𝔘) (hkl : k ≠ l) :
    𝔥 =
      if 𝔰 ∧ 𝔮 ∨ 𝔱 ∧ 𝔯 then 𝔊
      else if 𝔰 ∨ 𝔱 ∨ 𝔯 ∨ 𝔮 then
        𝔅 else 𝔎 ^ 2 := by
  classical
  by_cases hik : 𝔰
  · subst k
    by_cases hjl : 𝔮
    · subst l
      simpa only [true_and, true_or, or_true, ite_true, pow_two] using
        𝔨 kernel_pair_sq_integral hmK hij
    · simp only [hjl, and_false, Ne.symm hij ]
      exact 𝔢 hij hkl hjl
  · by_cases hil : 𝔱
    · subst l
      by_cases hjk : 𝔯
      · subst k
        have he : 𝕲 𝔖 =
             fun x => K 𝔄 ^ 2 := by
          grind
        rw [he]
        simp
        exact 𝔨 kernel_pair_sq_integral hmK hij
      · simp only [hik, hjk]
        have he : 𝔪 i =
            𝔩 𝔦 := by
          simp_all
        rw [he]
        exact 𝔢 hij hik hjk
    · by_cases hjk : 𝔯
      · subst k
        have he : 𝕲 𝔞 =
             fun x => 𝔖 * 𝔞 := by
          simp_all
        rw [he]
        simp only [hik, hil]
        exact 𝔢 (Ne.symm hij) hkl hil
      · by_cases hjl : 𝔮
        · subst l
          have he : 𝔪 j =
               fun x => 𝔖 * K (𝔵, 𝔜) := by
            simp_all
          rw [he]
          simp only [hik, hil, or_true]
          exact 𝔢 (Ne.symm hij)
            (Ne.symm hkl) hik
        · simp only [hik, hil, hjk, hjl]
          exact 𝔨 kernel_disjoint_product_integral hmK hij hkl hik hil hjk hjl

𝗃 𝕮 if ἀ = i then 1 else 0
𝗃 𝕯 if ἀ = j then 1 else 0
𝗃 𝕴 𝔨 kernel_pair_memLp hK ἀ
theorem kernel_pair_covariance_le [DecidableEq ι] X
    (hind : 𝔒) (hX : 𝔇)
    {K } (hmK : Measurable K) (hK : 𝔈)
    (hsym : 𝔍)
    {i j k l : ι} (hij : 𝔘) (hkl : k ≠ l) :
    covariance 𝔬 𝔩 𝔔 ν ≤
      𝔅 *
        (𝕮 k + 𝕮 l +
          𝕯 k + 𝕯 l) +
      𝔊 *
        ((if (k, l) = 𝘈₁ then 1 else 0) + if (k, l) = (j, i) then 1 else 0 ) := by
  have hB : 0 ≤ 𝔅 := integral_nonneg 𝖸
  rw [covariance_eq_sub 𝕴 hij
    𝕴 hkl]
  simp
  rw [𝔡 hij, 𝔡 hkl,
    ← pow_two, 𝔨 kernel_pair_product_classification hmK hK hsym hij hkl]
  by_cases hik : 𝔰 <;> by_cases hil : 𝔱 <;>
    by_cases hjk : 𝔯 <;> by_cases hjl : 𝔮 <;>
    subst_vars <;>
    simp_all only [ne_eq, eq_comm, and_true, and_false, false_or, or_false,
      ite_true, ite_false] <;> nlinarith

𝗇 𝕬 pairAverage n K
theorem pairAverage_eq_orderedPairs K (x : 𝗚₁) :
    𝕬 x =
      𝔣 * ∑ p ∈ orderedPairs n, K (x p.1, x p.2) := by
  rw [pairAverage, sum_orderedPairs]

𝗇 𝔏 𝕬 fun i => 𝔴
𝗇 𝔤 4 / n * 𝔅 + 2 / (n * 𝔉) * 𝔊
section

variable {n }
    {K }

𝗇 𝔳 (Finset.mem_filter.mp hp).2
𝗇 𝔗 𝕴 𝔳
theorem pairAverage_memLp_two X
    (hind : 𝔒) (hX : 𝔇)
    (hK : 𝔈) :
    MemLp 𝔩 𝔏 2 ν := by
  simp only [pairAverage_eq_orderedPairs]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  exact 𝔗

𝗇 𝔟 K (𝕳 p.1, 𝕳 p.2)
theorem pairAverage_integral (hn : 𝗏) X
    (hind : 𝔒) (hX : 𝔇)
    (hmK : Measurable K) (hK : 𝔈) :
    𝕭 𝔏 = 𝔎 := by
  simp only [pairAverage_eq_orderedPairs]
  rw [integral_const_mul, integral_finsetSum]
  · have he : ∑ p ∈ orderedPairs n, 𝕭 𝔟 =
        ∑ _p ∈ orderedPairs n, 𝔎 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact 𝔡 𝔳
    rw [he, Finset.sum_const, orderedPairs_card, nsmul_eq_mul, Nat.cast_mul]
    have hN : 𝔚 * 𝔉 ≠ 0 := by
      have hmp : 0 < 𝔷 := 𝖡₃
      positivity
    grind
  · intro p hp
    exact (𝔗).integrable 𝖠₄

𝗇 𝔠 4 * 𝔉 * B + 2 * A
𝗇 𝔲 n * 𝔉 * 𝔠
/-- The order-two localized variance bound, valid for unbounded L² kernels.
The four shared slots cost the row energy; the two equal unordered pairs
cost the full kernel energy. -/
theorem pairAverage_variance_le (hn : 𝗏) X
    (hind : 𝔒) (hX : 𝔇)
    (hmK : Measurable K) (hK : 𝔈)
    (hsym : 𝔍) :
    variance 𝔩 𝔏 ν ≤
      𝔤 := by
  let A := 𝔊
  let B := 𝔅
  let Y : Fin n × Fin n → 𝘄 := fun p x => 𝔟
  have hY : ∀ p ∈ orderedPairs n, MemLp (Y p) 2 ν := by
    intro p hp
    exact 𝔗
  have hsum : ∑ p ∈ orderedPairs n, ∑ q ∈ orderedPairs n,
      covariance (Y p) (Y q) ν ≤
      𝔲 := by
    calc
      _ ≤ ∑ p ∈ orderedPairs n, ∑ q ∈ orderedPairs n,
          overlapMajorant p q A B := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        simpa only [Y, overlapMajorant, A, B, Prod.mk.eta, Prod.swap] using
          𝔨 kernel_pair_covariance_le hmK hK hsym
            𝔳 (Finset.mem_filter.mp hq).2
      _ = ∑ _p ∈ orderedPairs n, 𝔠 := Finset.sum_congr rfl fun p hp => overlap_majorant_sum hp A B
      𝘿 := by
        simp only [Finset.sum_const, orderedPairs_card, nsmul_eq_mul, Nat.cast_mul]
  simp only [pairAverage_eq_orderedPairs]
  rw [variance_const_mul, variance_fun_sum' hY]
  calc
    _ ≤ 𝔣 ^ 2 *
        𝔲 :=
      mul_le_mul_of_nonneg_left hsum $ sq_nonneg _
    𝘿 := by
      have hm0 : 𝔷 ≠ 0 := 𝖡₃
      field_simp
      <;> ring

end

/-- Mean-squared fluctuation form used by the ratio estimators. -/
theorem pairAverage_centered_sq_le (hn : 𝗏) X
    (hind : 𝔒) (hX : 𝔇)
    (hmK : Measurable K) (hK : 𝔈)
    (hsym : 𝔍) :
     ∫ x, (𝔏 - 𝔎) ^ 2 ∂ν ≤
      𝔤 := by
  have hv := pairAverage_variance_le hn X hind hX hmK hK hsym
  rw [variance_eq_integral (𝔨 pairAverage_memLp_two hK).aemeasurable,
    pairAverage_integral hn X hind hX hmK hK] at hv
  exact hv

theorem pairAverage_measurable n {K : 𝔑} (hmK : Measurable K) :
    Measurable 𝕬 := by
  unfold pairAverage
  fun_prop
