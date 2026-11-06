module

public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.StaticSurvivalMonotonicity
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold

/-- Canonicalize a valid split only when the factors commute and the right
factor is shorter. Equal-length commuting factors are identical, so there is
no separate tie to collapse. Invalid coordinates are harmless unused marks. -/
def canonicalIndex (z : List Bool × ℕ) : List Bool × ℕ :=
  if 0 < z.2 ∧ z.2 < z.1.length ∧ z.1.length-z.2 < z.2 ∧
      z.1.take z.2 ++ z.1.drop z.2 = z.1.drop z.2 ++ z.1.take z.2 then
    (z.1,z.1.length-z.2)
  else z

@[simp] theorem canonicalIndex_product (z : List Bool × ℕ) :
    (canonicalIndex z).1 = z.1 := by unfold canonicalIndex; split <;> rfl

theorem canonicalIndex_prefix {B : ℕ} {z : List Bool × ℕ}
    (hz : z ∈ splitPrefixCoordinates B) : canonicalIndex z ∈ splitPrefixCoordinates B := by
  have hz' := (mem_splitPrefixCoordinates B z).mp hz
  apply (mem_splitPrefixCoordinates B _).mpr
  unfold canonicalIndex
  split
  · dsimp
    exact ⟨hz'.1,(Nat.sub_le _ _).trans hz'.1⟩
  · exact hz'

def quotientField (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (canonicalIndex (w,k))

theorem quotientField_measurable : Measurable quotientField := by
  apply Measurable.of_eval
  intro w
  apply Measurable.of_eval
  intro k
  exact measurable_pi_apply _

/-- Infinite reversible quotient survival, realized by iid marks on canonical
coordinates. Noncanonical and invalid latent coordinates do not affect it. -/
noncomputable def quotientSurvival (a : I) : ENNReal :=
  infiniteSplitPi a {ω | ReversibleUnbounded 2 (quotientField ω)}

end RAFReactionQuotient
