module

public import NearlyMinimax.HighObservationReal
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! An actual original-model parameter path for every raw source state.
A fixed valid endpoint defines the path outside the time interval. -/
𝚴
𝚨
𝛀
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

def highNormalizedParameterPath (T : ℝ) (hT : 𝚞) (a v η : ℝ) (ha : 𝙞)
    (p F : Ω → 𝙀) (hF : 𝗴)
    (hq : ∀ t ∈ 𝗺, ∀ ω x y, 0 ≤ 𝙅 (v-𝙎*t) y)
    (t : ℝ) (ω : Ω) : RegressionParameter d :=
  if ht : t ∈ 𝗺 then
    𝙼 (v-𝙎*t) hF.of_uncurry_left ha $ hq t ht ω
  else
    𝙼 v hF.of_uncurry_left ha
       fun x y => by simpa using hq 0 ⟨le_rfl,hT⟩ ω x y

theorem highNormalizedParameterPath_apply T hT a v η ha
    (p F : Ω → 𝙀) hF
    hq
    t ht ω :
    highNormalizedParameterPath T hT a v η ha p F hF hq t ω =
      𝙼 (v-𝙎*t) hF.of_uncurry_left ha (hq t ht ω) := by
  unfold highNormalizedParameterPath
  simp_all
