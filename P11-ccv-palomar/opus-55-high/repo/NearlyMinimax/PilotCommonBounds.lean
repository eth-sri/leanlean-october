module

public import NearlyMinimax.DyadicPilotMultilevel
public import NearlyMinimax.PilotModelEnvelope
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! One genuine model envelope and one factorial series simultaneously
control both scalar coefficient families of the actual estimator. -/
𝚵
𝚪
𝚨
𝚭
𝚩

𝗇 𝔄 ν w * dyadicMultilevelErrorField C θ n J y m t w
𝗇 𝔅 Nonempty 𝘘
𝗇 𝔇 ∀ j : Fin 𝗯, m j.val + 𝗣 + 1 ≤ n
𝗇 𝔈 regularPairDesignMeasure θ 𝘻₁
𝗇 𝔉 AnchoredIndex d (pilotModelConstants C).order
𝗇 𝔍 admissible_pilotModelConstants C θ hθ
theorem dyadicMultilevelErrorField_envelope_test_moment_facts (C : ModelConstants d)
    [𝔅] θ (hθ : 𝙟)
    n J L (hJL : 𝚗₂) y (hy : |y| ≤ max C.holderBound 1) m
    (hdegree : 𝔇)
    ν
    (hν : MemLp ν 2 $ 𝔈 𝖠₃ ) :
    MemLp (fun t => ∫ w, 𝔄
      ∂𝔈  𝖠₃ ) 2 (sampleLaw θ n) ∧
     ∫ t, ∫ w, 𝔄
      ∂𝔈  𝖠₃  ∂sampleLaw θ n = 0 := by
  letI : Nonempty 𝔉 :=
    inferInstanceAs 𝔅
  exact dyadicMultilevelErrorField_test_moment_facts (pilotModelConstants C) θ
    𝔍 n J L hJL y hy m hdegree ν hν

𝗇 𝔊 𝗟 ^ L
theorem dyadicMultilevelErrorField_envelope_weighted_integrable (C : ModelConstants d)
    [𝔅] (θ : RegressionParameter d) (hθ : 𝙟)
    (n J L : ℕ) (hJL : 𝚗₂) (y : ℝ) (hy : |y| ≤ max C.holderBound 1) (m : 𝙦₁)
    (hdegree : 𝔇)
    ν
    (hν : MemLp ν 2 $ regularPairDesignMeasure θ 𝔊 𝖠₃ )
    t :
    Integrable (fun w => 𝔄)
      $ regularPairDesignMeasure θ 𝔊 $ by positivity := by
  letI : Nonempty 𝔉 :=
    inferInstanceAs 𝔅
  have hi j := dyadicPilotErrorField_weighted_integrable (pilotModelConstants C) θ
    𝔍 n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL)
      y hy (m j.val) (hdegree j) ν hν t
  convert integrable_finsetSum Finset.univ fun j _ => hi j using 1
  funext w
  simp only [dyadicMultilevelErrorField, Finset.mul_sum]
  rfl
