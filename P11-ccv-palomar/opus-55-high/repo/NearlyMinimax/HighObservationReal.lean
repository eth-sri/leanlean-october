module

public import NearlyMinimax.HighObservationKernel
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Original real-response kernel and likelihood integrals for the high prior. -/
𝚴
𝛉
𝚨
𝚰
𝚩
𝛂

𝗇 𝔅 Ω → 𝙀
𝗃 𝔉 ἀ n a V p F hp hF
/-- The jointly Borel experiment on the original real observation space. -/
def highRealSampleKernel (n : ℕ) (a V : ℝ)
    (p F : 𝔅) (hp : 𝘍)
    (hF : 𝗴) : Kernel Ω 𝙌 :=
  (𝔉 highSampleIndexKernel).map $ encodeDesignResponse a

𝗇 𝔄 𝔉 highRealSampleKernel
theorem highRealSampleKernel_apply n a V
    (p F : 𝔅) hp
    hF ω :
    𝔄 ω =
      (𝔉 highSampleIndexKernel ω).map (encodeDesignResponse a) :=
  Kernel.map_apply _ (encodeDesignResponse_measurable a) ω

𝗇 𝔇 ∀ ω x y, 0 ≤ 𝙅 V y
𝗇 𝔈 𝙄
theorem highRealSampleKernel_markov n a V
    (p F : 𝔅) hp
    hF aRaw bRaw (haRaw : 𝙓)
    (hraw : 𝔈) (ha : 𝙞)
    (hq : 𝔇) :
    IsMarkovKernel 𝔄 := by
  let _ := 𝔉 highSampleIndexKernel_markov aRaw bRaw haRaw hraw ha hq
  exact Kernel.IsMarkovKernel.map _ $ encodeDesignResponse_measurable a

/-- Each fiber is the actual original-model sample law. -/
theorem highRealSampleKernel_eq_sampleLaw n a V
    (p F : 𝔅) hp
    hF aRaw bRaw (haRaw : 𝙓)
    (hraw : 𝔈) ha
    (hq : 𝔇) ω :
    𝔄 ω =
      sampleLaw (𝙼 V hF.of_uncurry_left ha $ hq ω ) n := by
  rw [highRealSampleKernel_apply]
  exact 𝔉 highSampleIndexKernel_encode aRaw bRaw haRaw hraw ha hq ω
