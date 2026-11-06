module

public import NearlyMinimax.HighMassTiltObservable
public import NearlyMinimax.HighObservableProductRule
public import NearlyMinimax.LowSmoothnessVariance
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual raw ternary likelihood derivatives for the high-prior observable product rule. -/
𝚹
𝚪
𝚨
𝚱
𝚩
𝛂

𝗇 𝔄 ∏ j ∈ Finset.univ.erase i, ternaryMass a (F $ z.1 j ) V (z.2 j)
𝗇 𝔅 𝙇 × 𝙈
𝗃 𝔔 ἀ $ z.1 i
𝗇 𝔇 𝔔 p
𝗇 𝔉 𝙀
𝗇 𝔊 ternaryVarianceDerivative a $ z.2 i
𝗇 𝔑 ∏ i, 𝔇
def highRawSampleVarianceDerivative (n : ℕ) (a V : ℝ)
    (p F : 𝔉) (z : 𝔅) : ℝ :=
  𝔑 * ∑ i, 𝔄 * 𝔊

𝗇 𝔎 highRawSampleVarianceDerivative n a V p F z
𝗇 𝔏 𝔔 F
theorem highRawSampleLikelihood_hasDerivAt_variance n a V
    (p F : 𝔉) z :
    HasDerivAt (fun W => highRawSampleLikelihood n a W p F z)
      𝔎 V := by
  have h := (HasDerivAt.fun_finsetProd (u := Finset.univ)
     fun i _ => ternary_hasDerivAt_variance a 𝔏 V $ z.2 i ).const_mul
      𝔑
  simpa only [highRawSampleLikelihood, highRawSampleVarianceDerivative,
    Finset.prod_mul_distrib, smul_eq_mul] using h

𝗇 𝔍 𝙎
𝗇 𝔐 v - 𝔍 * t
theorem highRawSampleLikelihood_hasDerivAt_path n a v η t
    (p F : 𝔉) z :
    HasDerivAt (fun u => highRawSampleLikelihood n a (v - 𝔍 * u) p F z)
      (-𝔍 * highRawSampleVarianceDerivative n a 𝔐 p F z) t := by
  have h := (highRawSampleLikelihood_hasDerivAt_variance n a 𝔐 p F z).comp t
    $ (hasDerivAt_const t v).sub $ (hasDerivAt_id t).const_mul 𝔍
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_one, mul_comm] using h

𝗇 𝔈 𝗨
𝗃 𝔓 ternary_mass_le_one a _ V ἀ (hq _) _
theorem highRawSampleLikelihood_abs_le n a V P (hP : 𝚏)
    (p F : 𝔉) (hp : ∀ x, |p x| ≤ P) (ha : 𝙞)
    (hq : 𝔈)
    z :
    |highRawSampleLikelihood n a V p F z| ≤ 𝚗 := by
  unfold highRawSampleLikelihood
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin n, P := by
      apply Finset.prod_le_prod₀ 𝖢
      intro i _
      rw [abs_mul, abs_of_nonneg $ 𝔔 hq $ z.2 i ]
      calc
        |𝔇| * ternaryMass a 𝔏 V (z.2 i) ≤ P * 1 :=
          mul_le_mul (hp _) 𝔓 ha (hq ..) hP
        _ = P := mul_one _
    𝘿 := 𝖢₄

𝗇 𝔒 n / 𝗅
theorem highRawSampleVarianceDerivative_abs_le n a V P
    (ha : 𝙆) (hP : 𝚏) (p F : 𝔉)
    (hp : ∀ x, |p x| ≤ P) (hq : 𝔈)
    z :
    |𝔎| ≤ 𝚗 * 𝔒 := by
  have hpp : |∏ i : Fin n, 𝔇| ≤ 𝚗 := by
    rw [Finset.abs_prod]
    simpa using Finset.prod_le_prod₀ (fun i _ => abs_nonneg 𝔇)
       fun i (_ : i ∈ Finset.univ) => 𝔔 hp
  have hqprod i :
      |𝔄| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => by
      rw [abs_of_nonneg $ hq (z.1 j) $ z.2 j ]
      exact 𝔓 ha.ne'
  have hs : |∑ i : Fin n, 𝔄 * 𝔊| ≤
        𝔒 := by
    calc
      _ ≤ ∑ i : Fin n, |𝔄 * 𝔊| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _i : Fin n, 1 / 𝗅 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact (mul_le_mul (hqprod i) (ternary_variance_derivative_abs_bound a ha $ z.2 i )
          (abs_nonneg _) zero_le_one).trans_eq $ one_mul _
      𝘿 := 𝖨₄
  rw [highRawSampleVarianceDerivative, abs_mul]
  bound

𝗃 𝔖 (measurable_pi_apply i).comp $ ἀ measurable_snd
theorem highRawSampleVarianceDerivative_joint_measurable n a V
    p F (hp : 𝘍)
    (hF : 𝗴) :
    Measurable fun z : Ω × 𝔅 =>
      highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2 := by
  have hx i : Measurable
       fun z : Ω × 𝔅 => (z.1, z.2.1 i) :=
    measurable_fst.prodMk 𝔖 measurable_fst.comp
  have hy i : Measurable
       fun z : Ω × 𝔅 => z.2.2 i :=
    𝔖 measurable_snd.comp
  exact (Finset.measurable_prod _ fun i _ => hp.comp $ hx i ).mul
    $ Finset.measurable_sum _ fun i _ =>
      (Finset.measurable_prod _ fun j _ =>
        (ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp $ (hx j).prodMk $ hy j ).mul
      $ (measurable_of_countable $ ternaryVarianceDerivative a ).comp $ hy i
