module

public import NearlyMinimax.HighRawObservable
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Genuine variance-path derivatives of bounded raw data observables. -/
𝚹
𝚨
𝚭
𝚩
𝛂

𝗇 𝔐 𝙎
𝗇 𝔄 v - 𝔐 * u
𝗇 𝔅 v - 𝔐 * t
𝗇 𝔇 H 𝗟₁
𝗇 𝔈 -𝔐
𝗃 𝔍 ἀ n a 𝔄 (p ω) $ F ω
𝗇 𝔉 𝔍 highRawSampleVarianceDerivative
𝗇 𝔊 𝔍 highRawSampleLikelihood z
𝗇 𝔎 (hH.comp $ encodeDesignResponse_measurable a ).mul
𝗇 𝔏 𝘱
𝗃 𝔑 ἀ n a 𝔅 (p ω) $ F ω
/-- Differentiating the real bounded data observable follows from the actual
finite ternary product derivative and a derived constant majorant. -/
theorem highRawObservable_hasDerivAt_path n a v η t T P B
    (ha : 𝙆) (ht : 𝘁₁) (htT : t < T) (hP : 𝚏) (hB : 𝙐)
    (p F : Ω → 𝙀) (hp : 𝘍)
    (hF : 𝗴) (hpb : ∀ ω x, |𝗃₁| ≤ P)
    (hq : ∀ u ∈ 𝗏₂, ∀ ω x y, 0 ≤ 𝙅 𝔄 y)
    H (hH : Measurable H)
    (hHb : ∀ z, |H z| ≤ B) ω :
    HasDerivAt (fun u => 𝔍 highRawObservable H)
      (𝔈 * 𝔑 highRawObservableVarianceDerivative H) t := by
  let L := fun u z =>
    𝔇 * 𝔊
  let L' := fun u z =>
    𝔇 * (𝔈 *
      𝔉 z)
  have hLM u : Measurable $ L u := by
    have hj : Measurable $ Function.uncurry fun ω z =>
        𝔊 :=
      highRawSampleLikelihood_joint_measurable n a 𝔄 p F hp hF
    exact 𝔎 hj.of_uncurry_left
  have hL'M u : Measurable $ L' u := by
    have hj : Measurable $ Function.uncurry fun ω z =>
        𝔉 z :=
      highRawSampleVarianceDerivative_joint_measurable n a 𝔄 p F hp hF
    have hw : Measurable 𝔉 :=
      hj.of_uncurry_left
    exact 𝔎 $ hw.const_mul 𝔈
  have hi : Integrable (L t) 𝔏 := by
    apply Integrable.of_bound (hLM t).aestronglyMeasurable $ B * 𝚗
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact 𝘣 (highRawSampleLikelihood_abs_le n a 𝔅 P
        hP (p ω) (F ω) (hpb ω) ha.ne' (hq t ⟨ht, htT⟩ ω) z) (abs_nonneg _) hB
  have hb u (hu : u ∈ 𝗏₂) z :
      ‖L' u z‖ ≤ B * (𝔐 * (𝚗 * (n / 𝗅))) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, 𝚓₁]
    exact 𝘣 (mul_le_mul_of_nonneg_left
      (highRawSampleVarianceDerivative_abs_le n a 𝔄 P ha hP
        (p ω) (F ω) (hpb ω) (hq u hu ω) z) $ sq_nonneg η )  𝖠₃  hB
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le


     𝗍₂
    (Eventually.of_forall fun u => (hLM u).aestronglyMeasurable) hi
    (hL'M t).aestronglyMeasurable
    (Eventually.of_forall fun z u hu => hb u hu z)
    (integrable_const _)
    $ Eventually.of_forall fun z u _ =>
      𝗡₂
        𝔇 ).2
  apply hd.congr_deriv
  change ∫ z, L' t z ∂𝔏 =
    𝔈 * ∫ z, 𝔇 *
      𝔑 highRawSampleVarianceDerivative z ∂𝔏
  rw [← integral_const_mul]
  grind
