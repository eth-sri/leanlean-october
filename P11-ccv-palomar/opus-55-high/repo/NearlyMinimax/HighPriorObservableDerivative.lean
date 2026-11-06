module

public import NearlyMinimax.HighRawObservableDerivative
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual high-prior observable derivative: signed append generator plus variance heat. -/
𝚹
𝚨
𝚭
𝚩
𝚲

𝗇 𝔄 v - 𝙎 * u
𝗇 𝔅 𝙎
𝗃 𝔍 ἀ n a 𝔄 (p ω) (F ω) H
𝗇 𝔇 𝔍 highRawObservable
𝗃 𝔈 ἀ n a (v - 𝔅 * t) (p ω) (F ω) H
𝗇 𝔉 hq u hu ω
𝗇 𝔊 (𝘱).real Set.univ
𝗃 𝔎 ἀ n a 𝔄 p F hp hF H hH
theorem historyMarkedPrior_rawObservable_hasDerivAt (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝘼)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝘽)
    (T Ba t : ℝ) (ht : 𝘁₁) (htT : t < T) (hBa : 𝙑)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝖤)
    (n : ℕ) (a v η P B : ℝ) (ha : 𝙆) (hP : 𝚏) (hB : 𝙐)
    (p F : 𝙗 → 𝙀)
    (hp : 𝘍) (hF : 𝗴)
    (hpb : ∀ ω x, |𝗃₁| ≤ P)
    (hq : ∀ u ∈ 𝗏₂, ∀ ω x y, 0 ≤ 𝙅 𝔄 y)
    H (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    HasDerivAt (fun u => ∫ ω, 𝔇
      ∂𝘳 u π activation)
      ( -𝔅 * ∫ ω, 𝔈 highRawObservableVarianceDerivative
        ∂𝘳 t π activation +
        𝚄₂ activation
           fun ω => 𝔈 highRawObservable ) t := by
  let G := fun u ω =>
    𝔇
  let G' := fun u ω =>
    -𝔅 * 𝔍 highRawObservableVarianceDerivative
  let M := B * 𝚗 * 𝔊
  let M' := 𝔅 * (B * (𝚗 * (n / 𝗅)) * 𝔊)
  have hM : 𝙷 := 𝖠₃
  have hM' : 0 ≤ M' := 𝖠₃
  have hGM u := 𝔎 highRawObservable_measurable
  have hG'M u :=
    (𝔎 highRawObservableVarianceDerivative_measurable).const_mul $ -𝔅
  have hGb u hu ω :=
    highRawObservable_abs_le n a 𝔄 P B hP hB (p ω) (F ω) (hpb ω)
      ha.ne' 𝔉 H hHb
  have hG'b u (hu : u ∈ 𝗏₂) ω : |G' u ω| ≤ M' := by
    rw [abs_mul, abs_neg, 𝚓₁]
    exact mul_le_mul_of_nonneg_left (highRawObservableVarianceDerivative_abs_le n a 𝔄
      P B ha hP hB (p ω) (F ω) (hpb ω) 𝔉 H hHb) $ sq_nonneg η
  have hGD ω u (hu : u ∈ 𝗏₂) :=
    highRawObservable_hasDerivAt_path n a v η u T P B ha hu.1 hu.2 hP hB p F hp hF hpb hq H hH hHb ω
  have h := historyMarkedPrior_observable_product_rule dependent hrefl hsymm Δ hΔ hlabels
    T Ba t ht htT hBa π activation hactivation habound hsmall G G' hGM hG'M M M' hM hM' hGb hG'b hGD
  simpa only [G, G', integral_const_mul] using h
