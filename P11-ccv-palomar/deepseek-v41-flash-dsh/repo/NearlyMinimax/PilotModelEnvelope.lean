module

public import NearlyMinimax.Model

@[expose] public section

/-! A harmless fixed envelope permits both scalar evaluations 0 and 1
when representing the response slope by an exact polynomial difference. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax

variable {d : ℕ} (C : ModelConstants d)

def pilotModelConstants (C : ModelConstants d) : ModelConstants d :=
  { C with
    holderBound := max C.holderBound 1
    holderBound_pos := C.holderBound_pos.trans_le (le_max_left _ _) }

theorem admissible_pilotModelConstants 
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    Admissible (pilotModelConstants C) θ := by
  obtain ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, hFnorm⟩, hVlo, hVhi, herr⟩ := hθ
  refine ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, ?_⟩, hVlo, hVhi, herr⟩
  exact hFnorm.trans (ENNReal.ofReal_mono (le_max_left _ _))

end NearlyMinimax
