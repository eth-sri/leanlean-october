module

public import NearlyMinimax.HighSourceOriginalResponse
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual count-two radial cancellation in the original canonical
periodic-field source, with all response positivity guards derived. -/
𝚫
𝚪
𝚨
𝚩
set_option maxHeartbeats 1600000
𝚬
𝚿

𝗇 𝔄 coefficientRegression eta g w 𝙬 $ c j
𝗇 𝔅 𝖿
𝗇 𝔇 fun i => highLocalFieldWithout d k D eta c j $ x i
𝗇 𝔈 N*𝙹
𝗇 𝔉 𝖻 lam ell N mu
𝗃 𝔎 ἀ d k j $ x i
𝗇 𝔊 fun i => 𝔎 highLocalCoordinates
𝗇 𝔍 fun i => 𝔎 highPeriodicTensor
𝗇 𝔏 𝖯
𝗇 𝔐 𝙾
theorem completeSource_original_count_two [NeZero d]
    C (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 , 𝚣₂ ∧ 𝖴₁ ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder 𝙯),
      𝗑 → 𝗕 → 𝖯₂ → 𝘧 →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 𝚁₁ → 𝘈₂ → 𝚐₁ →
      𝔅 ≤ eta0 →
      ∀ V , |𝖮₂| ≤ Q.ρ → ∀ j ,
      ∀ h ,
      ∀ x , (∀ i, x i ∈ 𝘋) →
      ∀ y ,
      let R := 𝔉
      let eta := 𝔅
      let c := 𝔏
      let U := 𝔊
      let g := 𝔇
      let w := 𝔍
      highUnionSourceMarkedNumerator C R 2 Q.a V eta j h x y =
        eta^2*w 0*w 1*𝔐 (x 0)*𝔐 (x 1)*
        ((1+𝔈)*Real.exp (-𝔈))*
        ternaryMeanDerivative Q.a (𝔄 0) (y 0)*
        ternaryMeanDerivative Q.a (𝔄 1) (y 1) := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta V hV j h x hx y
  letI := hk0
  letI := horder
  let R := 𝔉
  let eta := 𝔅
  let c := 𝔏
  let U := 𝔊
  let p := fun i => 𝔐 $ x i
  let g := 𝔇
  let w := 𝔍
  have he := (hresponse k D M q hk0 horder hk hD  𝖡₃  hM Cfr lam ell N mu cf
    hfr hell hellN hcf heta V hV j h 2 x hx y).1
  have G := completeSourceRows_guards C k D M q hD  𝖡₃  hM Cfr lam ell N mu
    (hfr0.trans hfr) hell hellN
  obtain ⟨ha,hab⟩ := 𝗌₁
  have hp (i : Fin 2) :=
    𝘄₁
  have hU (i : Fin 2) (r : Fin d) : |U i r| ≤ 2 :=
    (𝔎 highLocalCoordinates_abs_le_one r).trans 𝖠₄
  have hQ (i : Fin 2) :=
    𝔎 highLocalCoordinates_abs_le_one
  exact he.trans $ completeSourceRawNumerator_count_two _ _ lam ell N mu ha hab hell.le hellN.le
    D M q hD (by exact_mod_cast (𝚀₁ hM).1) hq Cfr Q.a V eta  𝖡₄  U hU hQ p g w hp (c j) y
