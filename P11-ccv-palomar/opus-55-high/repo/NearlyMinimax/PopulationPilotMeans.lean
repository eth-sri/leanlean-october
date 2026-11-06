module

public import NearlyMinimax.DyadicPopulationBias
public import NearlyMinimax.ResponseOperators
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual uniformly bounded multiscale population coefficient fields. -/

𝛎
𝚺
𝚨
𝚭
𝚩

𝗇 𝔄 𝘮
𝗃 𝔈 ἀ θ j x
𝗇 𝔅 𝔈 dyadicIncrementRawMean
theorem dyadicIncrementRawMean_eq_with_virtual_parent C
    θ (hθ : 𝙟) j
    x (hx : 𝗌) :
    𝔅 = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram 𝘎₂ 𝔈 dyadicNormalizedDensity)
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor 𝔄 x)
          $ if 𝘠 then 𝙃 else dyadicNormalizedDensity θ 𝔄 x )
        𝔈 dyadicFinPilotMoments (if 𝘠 then 0 else dyadicFinPilotMoments θ 𝔄 x)
        $ (Fintype.equivFin $ incrementVariables 𝚃 ).symm a := by
  rw [dyadicIncrementRawMean_eq_population C θ hθ j x hx]
  unfold dyadicIncrementPopulation
  rw [dyadicFinPilotGram_eq_normalized C θ hθ j x]
  by_cases hj : 𝘠
  · simp [hj, anchoredFinNormalizedGram_one]
  · simp only [hj, ite_false]
    rw [dyadicFinPilotGram_eq_normalized C θ hθ 𝔄 x]

𝗇 𝔇 𝗣
def dyadicPopulationRawPolynomial (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (t : Bool) (m : ℕ) : Fin 𝔇 → ℝ :=
  incrementFinRawVector 𝔇 C.densityLower C.densityUpper
    𝖼₁ t m 𝔅

theorem dyadicPopulationPolynomial_affine C θ
    j (x : Covariate d) y m :
    dyadicPopulationPolynomial C θ j x y m = dyadicPopulationRawPolynomial C θ j x false m -
      y • dyadicPopulationRawPolynomial C θ j x true m := congrFun (incrementFinVector_affine _ _ _ _ y m) 𝔅
