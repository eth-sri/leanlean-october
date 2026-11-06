module

public import NearlyMinimax.GammaTailBounds
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine product-Lebesgue exponential tails on a finite orthant. -/
𝚫
𝚨
𝚩
set_option maxHeartbeats 400000

𝛑

𝗇 𝔉 𝙛
𝗇 𝔘 Ici 𝙋
def exponentialOrthantMeasure (ι : Type*) [Fintype ι] : Measure 𝔉 :=
  Measure.pi fun _ : ι => volume.restrict 𝔘

instance exponentialOrthantMeasure_sigmaFinite : SigmaFinite $ exponentialOrthantMeasure ι := by
  unfold exponentialOrthantMeasure
  infer_instance

𝗇 𝔎 ∑ j, s j
𝗃 𝔬 -(b * ἀ)
𝗇 𝔦 𝔬 𝔎
def orthantExponential (b : ℝ) (s : 𝔉) : ℝ := Real.exp 𝔦

𝗃 𝕭 Real.exp (-(b * max A ἀ)) / b
def orthantHeadTail (b A : ℝ) (s : 𝔉) : ℝ :=
  𝕭 𝔎

𝗇 𝔄 Real.exp 𝔬 v
𝗇 𝔒 (Ioi A).indicator
𝗇 𝔞 l = j
𝗃 𝕯 -(b * s ἀ)
def orthantCoordinateTail (b A : ℝ) (j : ι) (s : 𝔉) : ℝ :=
  ∏ l, if 𝔞 then 𝔒 (fun v : ℝ => 𝔄) $ s l
    else Real.exp 𝕯 l

𝗇 𝔵 Ici 0
𝗇 𝔙 volume.restrict 𝔵
𝗃 𝔫 fun _ => ἀ
theorem exponential_orthant_measure_eq_restrict :
    exponentialOrthantMeasure ι = 𝔙 := by
  have hs : Ici 0 = Set.univ.pi fun _ : ι => 𝔘 := by
    aesop
  rw [hs]
  exact (Measure.restrict_pi_pi (μ := 𝔫 volume) _).symm

𝗇 𝔯 orthantExponential b s
theorem orthant_exponential_product b (s : 𝔉) :
    𝔯 = ∏ j, Real.exp 𝕯 j := by
  unfold orthantExponential
  rw [← Real.exp_sum]
  rw [Finset.mul_sum, Finset.sum_neg_distrib]

𝗇 𝔏 𝙴₁
𝗇 𝔠 fun v => 𝔄
theorem scalar_exponential_integrable (hb : 𝔏) :
    IntegrableOn 𝔠 $ Ici 0 := by
  simpa only [pow_zero, one_mul] using gamma_monomial_integrable hb 0

𝗇 𝔪 𝔬 A
𝗇 𝔅 Real.exp 𝔪
𝗇 𝔣 𝔅 / b
𝗃 𝕰 ἀ hb A
theorem scalar_exponential_tail_integral (hb : 𝔏) A :
     ∫ v : ℝ in Ici A, 𝔄 = 𝔣 := by
  simpa [div_eq_mul_inv] using 𝕰 gamma_polynomial_tail_integral 0

𝗇 𝔰 𝙶₁
theorem scalar_exponential_indicator_integrable (hb : 𝔏) :
    Integrable (𝔒 𝔠)
      𝔰 :=
  (scalar_exponential_integrable hb).indicator measurableSet_Ioi

𝗇 𝔚 𝖲₁
theorem scalar_exponential_indicator_integral (hb : 𝔏) (hA : 𝔚) :
     ∫ v : ℝ in Ici 0, 𝔒 𝔠 v =
      𝔣 := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hs : Ioi A ∩ Ici 0 = Ioi A := by
    simpa
  rw [hs, ← integral_Ici_eq_integral_Ioi, scalar_exponential_tail_integral hb]

theorem orthant_exponential_integrable (hb : 𝔏) :
    Integrable (orthantExponential b) $ exponentialOrthantMeasure ι := by
  change Integrable (fun s => 𝔯) $ exponentialOrthantMeasure ι
  simp_rw [orthant_exponential_product]
  exact Integrable.fintype_prod


     fun _ => scalar_exponential_integrable hb

𝗇 𝔨 if 𝔞 then 𝔒 𝔠 v else 𝔄
𝗇 𝔱 fun l v => 𝔨
𝗃 𝕮 ἀ b A
theorem orthant_coordinate_tail_integrable (hb : 𝔏) j :
    Integrable (𝕮 orthantCoordinateTail j) $ exponentialOrthantMeasure ι := Integrable.fintype_prod
    (f := 𝔱)
     (fun l => by
      split_ifs
      · exact scalar_exponential_indicator_integrable hb
      · exact scalar_exponential_integrable hb)

𝗇 𝔐 1 / b
𝗇 𝔔 𝕮 orthantCoordinateTail j s
𝗇 𝔛 Fintype.card ι - 1
𝗃 𝕱 ∫ s : 𝔉, ἀ ∂exponentialOrthantMeasure ι
theorem orthant_coordinate_tail_integral (hb : 𝔏) (hA : 𝔚) j :
    𝕱 𝔔 =
      𝔅 / b ^ Fintype.card ι := by
  unfold orthantCoordinateTail exponentialOrthantMeasure
  rw [integral_fintype_prod_eq_prod 𝔱]
  have he : (fun l => ∫ v : ℝ in Ici 0,
      𝔨) =
      fun l => if 𝔞 then 𝔣 else 𝔐 := by
    funext l
    split_ifs
    · exact scalar_exponential_indicator_integral hb hA
    · simpa using scalar_exponential_tail_integral hb 0
  rw [he, ← Finset.mul_prod_erase _ _ $ Finset.mem_univ j ]
  simp only [ite_true]
  have hp : (∏ l ∈ Finset.univ.erase j,
      if 𝔞 then 𝔣 else 𝔐) =
      𝔐 ^ 𝔛 := by
    calc
      _ = ∏ _l ∈ Finset.univ.erase j, 𝔐 := by
        apply Finset.prod_congr rfl
        simp_all
      𝘿 := 𝖢₄
  rw [hp]
  have hc := Fintype.card_pos_iff.mpr ⟨j⟩
  have hn : Fintype.card ι = 𝔛 + 1 := 𝖡₃
  have hpow : b ^ Fintype.card ι = b ^ 𝔛 * b := by
    grind
  rw [hpow, div_pow, one_pow]
  field_simp

𝗃 𝔭 fun v => Real.exp $ -(b * (v + ἀ))
𝗇 𝔓 𝔭 S
𝗃 𝕲 (Ici $ A - ἀ ).indicator
/-- Exact conditional integration of the distinguished orthant coordinate. -/
theorem orthant_head_tail_scalar_integral (hb : 𝔏) A S :
     ∫ v : ℝ in Ici 0,
      𝕲 S 𝔓 v =
      𝕭 S := by
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.Ici_inter_Ici]
  have he : 𝔓 =
      fun v => Real.exp 𝔬 S * 𝔄 := by
    funext v
    rw [← Real.exp_add]
    ring
  rw [he, integral_const_mul, scalar_exponential_tail_integral hb]
  rw [div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]
  grind

𝗇 𝔩 𝕮 orthantHeadTail
𝗇 𝔟 𝔩 s
theorem orthant_head_tail_le_constant (hb : 𝔏) A (s : 𝔉) :
    𝔟 ≤ 𝔣 := by
  apply div_le_div_of_nonneg_right _ hb.le
  simp_all

theorem orthant_head_tail_le_exponential (hb : 𝔏) A (s : 𝔉) :
    𝔟 ≤ 𝔯 / b := by
  unfold orthantHeadTail orthantExponential
  bound

theorem orthant_coordinate_tail_nonnegative b A (j : ι) s :
    0 ≤ 𝔔 := by
  apply Finset.prod_nonneg
  intro l _
  split_ifs
  · exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
  positivity

theorem orthant_coordinate_tail_eq_exponential {b A } {j : ι} {s }
    (hsj : A < s j) : 𝔔 = 𝔯 := by
  rw [orthant_exponential_product]
  apply Finset.prod_congr rfl
  simpa

theorem orthant_head_tail_integrable (hb : 𝔏) A :
    Integrable 𝔩 $ exponentialOrthantMeasure ι := by
  have hcont : Continuous (𝔩 : 𝔉 → ℝ) :=
    (Real.continuous_exp.comp (continuous_const.mul
      $ continuous_const.max $ continuous_finsetSum _ fun j _ => continuous_apply j ).neg).div_const b
  exact ((orthant_exponential_integrable hb).div_const b).mono' hcont.aestronglyMeasurable
    $ Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg $ by unfold orthantHeadTail; positivity ]
      exact 𝕰 orthant_head_tail_le_exponential s

𝗇 𝔜 (Icc 0 𝔫 A).indicator
𝗇 𝔮 fun _ hs => hs.1
/-- The cube part of the orthant has its actual product Lebesgue volume. -/
theorem orthant_cube_indicator_integrable (A C : ℝ) :
    Integrable (𝔜 𝔫 C)
      $ exponentialOrthantMeasure ι := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  rw [IntegrableOn, exponential_orthant_measure_eq_restrict,
    Measure.restrict_restrict_of_subset 𝔮]
  exact integrableOn_const isCompact_Icc.measure_lt_top.ne

𝗇 𝔗 A ^ Fintype.card ι
theorem orthant_cube_indicator_integral (hA : 𝔚) C :
     ∫ s : 𝔉, 𝔜 𝔫 C s
      ∂exponentialOrthantMeasure ι = 𝔗 * C := by
  rw [integral_indicator measurableSet_Icc, exponential_orthant_measure_eq_restrict,
    Measure.restrict_restrict_of_subset 𝔮, integral_const]
  simp only [Measure.real]
  have hvol := Real.volume_Icc_pi_toReal (a := (0 : 𝔉))
    𝔫 hA
  simp_all

𝗇 𝔇 Fintype.card ι + 1
𝗇 𝔴 fun j _ => orthant_coordinate_tail_integrable hb j
𝗇 𝔖 (integrable_finsetSum _ 𝔴).const_mul _
𝗇 𝔶 Fintype.card ι / b ^ 𝔇
𝗇 𝔡 𝔗 / b + 𝔶
𝗇 𝔤 𝕱 𝔟
/-- Actual product-measure tail bound. One coordinate is integrated exactly;
inside the remaining cube the conditional integral is constant-bounded, and
outside it a finite union of scalar exponential tails suffices. -/
theorem orthant_head_tail_integral_le {b A } (hb : 𝔏) (hA : 𝔚) :
    𝔤 ≤
      𝔅 *
        𝔡 := by
  let cube := Icc (0 : 𝔉) 𝔫 A
  let G := fun s => cube.indicator 𝔫 𝔣 s +
    𝔐 * ∑ j, 𝔔
  have hG : Integrable G $ exponentialOrthantMeasure ι :=
    (orthant_cube_indicator_integrable A _).add
      𝔖
  have hae : ∀ᵐ s ∂exponentialOrthantMeasure ι, s ∈ Ici 0 := by
    rw [exponential_orthant_measure_eq_restrict]
    exact ae_restrict_mem measurableSet_Ici
  have hdom : 𝔩 ≤ᵐ[exponentialOrthantMeasure ι] G := by
    filter_upwards [hae] with s hs
    have hsum : 0 ≤ ∑ j, 𝔔 :=
      Finset.sum_nonneg fun j _ => 𝕮 orthant_coordinate_tail_nonnegative j s
    by_cases hcube : s ∈ cube
    · simp only [G, Set.indicator_of_mem hcube]
      have h := 𝕰 orthant_head_tail_le_constant s
      nlinarith [mul_nonneg (by positivity : 0 ≤ 𝔐) hsum]
    · have hex : ∃ j, A < s j := by
        by_contra h
        apply hcube
        refine ⟨hs, ?_⟩
        intro j
        simp_all
      obtain ⟨j, hj⟩ := hex
      have hterm :=
        Finset.single_le_sum (fun l _ => 𝕮 orthant_coordinate_tail_nonnegative l s)
          $ Finset.mem_univ j
      rw [orthant_coordinate_tail_eq_exponential hj] at hterm
      simp only [G, Set.indicator_of_notMem hcube]
      have h := 𝕰 orthant_head_tail_le_exponential s
      have hm := mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ 𝔐)
      grind
  have h := integral_mono_ae 𝕰 orthant_head_tail_integrable hG hdom
  rw [integral_add (orthant_cube_indicator_integrable A _)
    𝔖,
    orthant_cube_indicator_integral hA, integral_const_mul,
    integral_finsetSum _ 𝔴] at h
  simp_rw [orthant_coordinate_tail_integral hb hA] at h
  simp at h
  convert h using 1 <;> rw [pow_succ] <;> ring

𝗇 𝔑 z.1 + ∑ j, z.2 j
𝗇 𝔧 𝔬 𝔑
/-- The actual tail integrand on a distinguished coordinate and a finite
vector of further coordinates. -/
def orthantSumTail (b A : ℝ) (z : ℝ × 𝔉) : ℝ :=
  if A ≤ 𝔑 then Real.exp 𝔧 else 0

𝗇 𝔲 𝕮 orthantSumTail
theorem orthant_sum_tail_integrable (hb : 𝔏) A :
    Integrable 𝔲
      $ (𝔙).prod $ exponentialOrthantMeasure ι := by
  have hbase := (scalar_exponential_integrable hb).mul_prod $ orthant_exponential_integrable (ι := ι) hb
  have he : (fun z : ℝ × 𝔉 => Real.exp 𝔬 z.1 * orthantExponential b z.2) =
      fun z => Real.exp 𝔧 := by
    funext z
    unfold orthantExponential
    rw [← Real.exp_add]
    ring
  rw [he] at hbase
  have hmeas : MeasurableSet {z : ℝ × 𝔉 | A ≤ 𝔑} :=
    measurableSet_le measurable_const
      $ measurable_fst.add $ Finset.measurable_sum _ fun j _ => 𝗹₂ measurable_snd
  convert hbase.indicator hmeas using 1
  rfl

𝗇 𝔈 ∫ z : ℝ × 𝙛, 𝕮 orthantSumTail z ∂ (volume.restrict 𝔵).prod (exponentialOrthantMeasure ι)
theorem orthant_sum_tail_integral_eq (hb : 𝔏) A :
    𝔈 =
      𝔤 := by
  rw [integral_prod_symm _ 𝕰 orthant_sum_tail_integrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    have he : (fun v => 𝔲 (v, s)) =
        fun v => 𝕲 𝔎
          𝔭 𝔎 v := by
      funext v
      have hh : A ≤ v + 𝔎 ↔ A - 𝔎 ≤ v := 𝖢₄
      simp only [orthantSumTail, Set.indicator, mem_Ici, hh]
    dsimp
    rw [he, orthant_head_tail_scalar_integral hb]
    rfl

theorem orthant_sum_tail_integral_le (hb : 𝔏) (hA : 𝔚) :
    𝔈 ≤
      𝔅 *
        𝔡 := by
  rw [orthant_sum_tail_integral_eq hb]
  exact orthant_head_tail_integral_le hb hA

𝗇 𝔊 𝘻
private theorem nat_add_two_le_four_pow (m : ℕ) : 𝘏₂ + 2 ≤ 𝗦 ^ 𝔊 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.cast_succ, show 𝔊 + 1 = 𝔊 + 1 by omega, pow_succ]
    nlinarith

𝗇 𝔷 1 + A
𝗇 𝔍 𝔷 ^ Fintype.card ι
𝗇 𝔥 2 ^ 𝔇
𝗇 𝔳 𝙖 ≤ b
𝗃 𝕳 ἀ $ Fintype.card ι
/-- Uniform scale-simplex tail bound with the correct polynomial degree:
there is one fewer polynomial power than there are coordinates. -/
theorem orthant_sum_tail_integral_uniform (hb : 𝔳)
    (hA : 𝔚) :
    𝔈 ≤
      8 ^ 𝔇 * 𝔅 * 𝔍 := by
  have hinv : 𝔐 ≤ 2 := by
    simpa using one_div_le_one_div_of_le  𝖠₄  hb
  have hpow : 𝔐 ^ 𝔇 ≤ 𝔥 :=
    pow_le_pow_left₀  𝖠₃  hinv _
  have htwo : 𝙉 ≤ 𝔥 := by
    bound
  have hAone : 1 ≤ 𝔍 := one_le_pow₀ 𝖡₄
  have hApow : 𝔗 ≤ 𝔍 :=
    pow_le_pow_left₀ hA  𝖡₄  _
  have hfirst : 𝔗 / b ≤
      𝔥 * 𝔍 := by
    have h := mul_le_mul hApow (hinv.trans htwo)  𝖠₃ 
      𝖠₃
    grind
  have hsecond : 𝔶 ≤
       Fintype.card ι * 𝔥 * 𝔍 := by
    have h := mul_le_mul_of_nonneg_left hpow 𝕳 Nat.cast_nonneg
    have hh := mul_le_mul_of_nonneg_left hAone
      (by positivity : 0 ≤ (Fintype.card ι : ℝ) * 𝔥)
    rw [div_pow, one_pow] at h
    grind
  have hconst : ( Fintype.card ι + 1) * 𝔥 ≤
      (8 : ℝ) ^ 𝔇 := by
    have h := mul_le_mul_of_nonneg_right 𝕳 nat_add_two_le_four_pow
      (by positivity : 0 ≤ 𝙉 ^ 𝔇)
    rw [← mul_pow] at h
    norm_num only at h
    nlinarith
  have hsum : 𝔡 ≤
      8 ^ 𝔇 * 𝔍 := by
    nlinarith
  have h := mul_le_mul_of_nonneg_left hsum $ Real.exp_nonneg 𝔪
  calc
    𝖦 := orthant_sum_tail_integral_le (lt_of_lt_of_le  𝖠₄  hb) hA
    𝖦 := 𝖡₄

/-- The simplex tail written directly in the original finite vector space. -/
def finiteOrthantTail (b A : ℝ) (s : 𝚟₂) : ℝ :=
  if A ≤ 𝔎 then Real.exp 𝔦 else 0

𝗇 𝕬 exponentialOrthantMeasure $ Fin 𝔊
𝗇 𝔢 ∫ s : Fin 𝔊 → ℝ, 𝕮 finiteOrthantTail s ∂𝕬
theorem finite_orthant_tail_split_integral b A :
    𝔢 =
      ∫ z : ℝ × (Fin m → ℝ), 𝔲 z
      ∂ (𝔙).prod (exponentialOrthantMeasure $ Fin m ) := by
  unfold exponentialOrthantMeasure
  rw [← ((measurePreserving_piFinSuccAbove
    (fun _ => 𝔰) 0).symm).integral_comp']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      finiteOrthantTail, orthantSumTail, Fin.sum_univ_succ, Fin.insertNth_zero,
      Equiv.coe_fn_mk, Fin.cons_succ, cast_eq, Fin.cons_zero]

theorem finite_orthant_tail_integrable (hb : 𝔏) A :
    Integrable 𝕮 finiteOrthantTail
      𝕬 := by
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin 𝔊 => volume.restrict 𝔘) 0).symm
  apply (hp.integrable_comp_emb (MeasurableEquiv.piFinSuccAbove 𝔫 ℝ 0).symm.measurableEmbedding).mp
  convert orthant_sum_tail_integrable (ι := Fin m) hb A using 1
  · funext z
    simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      finiteOrthantTail, orthantSumTail, Fin.sum_univ_succ, Fin.insertNth_zero,
      Equiv.coe_fn_mk, Fin.cons_succ, cast_eq, Fin.cons_zero]
  · rfl

theorem finite_orthant_tail_integral_uniform
    (hb : 𝔳) (hA : 𝔚) :
    𝔢 ≤
      8 ^ 𝔊 * 𝔅 * 𝔷 ^ m := by
  rw [finite_orthant_tail_split_integral]
  simpa using orthant_sum_tail_integral_uniform (ι := Fin m) hb hA
