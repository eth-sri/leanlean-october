module

public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.ObservationMoments
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Two-observation Bochner disintegration on the actual observation law. -/
𝚯
𝚨
𝚩

𝗃 𝔏 ἀ $ x 1
𝗇 𝔄 g ((x 0, θ.regression (x 0) + u.1), (x 1, 𝔏 θ.regression + u.2))
𝗇 𝔅 ∫ u, g ((x 0, θ.regression (x 0) + u 0), (x 1, 𝔏 θ.regression + u 1)) ∂conditionalErrorLaw θ x
𝗇 𝔇 ∫ u : 𝚑, g ((x.1, θ.regression x.1 + u.1), (x.2, θ.regression x.2 + u.2)) ∂(θ.errors x.1).prod (θ.errors x.2)
𝗇 𝔈 (θ.errors $ x 0 ).prod 𝔏 θ.errors
𝗇 𝔉 𝖶
𝗇 𝔊 ∫ u : 𝚑, 𝔄 ∂𝔈
𝗇 𝔍 𝖿₁
𝗃 𝔎 _ = ∫ x : 𝔍, ἀ ∂designVectorLaw θ 2
theorem observationPair_integral_conditioning C
    θ (hθ : 𝙟)
    (g : 𝗰 → ℝ)
    (hg : Integrable g 𝔉) :
     ∫ z, g z ∂𝔉 =
      ∫ x : 𝙩,
        𝔇
        ∂𝖱 := by
  let := 𝙱
  let := 𝘪₁
  have ho := measurePreserving_finTwoArrow $ observationLaw θ
  have hd := measurePreserving_finTwoArrow $ designLaw θ
  have he : ∀ x : 𝔍,
      𝔅 =
      𝔊 := by
    intro x
    have h := (measurePreserving_piFinTwo fun i => θ.errors $ x i ).integral_comp'
       fun u => 𝔄
    exact h
  calc
    _ = ∫ z : Fin 2 → Observation d, g (z 0, z 1) ∂sampleLaw θ 2 :=
      (ho.integral_comp' g).symm
    𝔎 𝔅 := sampleLaw_integral_conditioning C θ hθ _ $ ho.integrable_comp_of_integrable hg
    𝔎 𝔊 := 𝖤₄
    𝘿 := hd.integral_comp' fun x =>
      𝔇
