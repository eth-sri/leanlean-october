module

public import NearlyMinimax.Model
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! A harmless fixed envelope permits both scalar evaluations 0 and 1
when representing the response slope by an exact polynomial difference. -/
𝚯
𝚨

def pilotModelConstants (C : ModelConstants d) : ModelConstants d :=
  { C with
    holderBound := max C.holderBound 1
    holderBound_pos := C.holderBound_pos.trans_le 𝚂₁ }

theorem admissible_pilotModelConstants C
    (θ : RegressionParameter d) (hθ : 𝙟) :
    Admissible (pilotModelConstants C) θ := by
  obtain ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, hFnorm⟩, hVlo, hVhi, herr⟩ := hθ
  refine ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, ?_⟩, hVlo, hVhi, herr⟩
  exact hFnorm.trans $ ENNReal.ofReal_mono $ le_max_left ..
