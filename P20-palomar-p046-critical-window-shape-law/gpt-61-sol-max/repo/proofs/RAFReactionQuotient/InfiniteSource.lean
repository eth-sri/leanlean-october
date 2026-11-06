
import proofs.HordijkSteelThreshold.RecordTargetTrial
import proofs.HordijkSteelThreshold.ReversibleEscapeProbability
import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
import proofs.HordijkSteelThreshold.SplitPrefixIndependence



namespace RAFReactionQuotient
open unitInterval HordijkSteelThreshold

variable (z : List Bool × ℕ)

/-- Canonicalize a valid split only when the factors commute and the right
factor is shorter. Equal-length commuting factors are identical, so there is
no separate tie to collapse. Invalid coordinates are harmless unused marks. -/
def canonicalIndex   :=
  if 0 < z.2 ∧ z.2 < z.1.length ∧ z.1.length-z.2 < z.2 ∧
      z.1.take z.2 ++ z.1.drop z.2 = z.1.drop z.2 ++ z.1.take z.2 then
    (z.1,z.1.length-z.2)
  else z

@[simp] theorem canonicalIndex_product  :
    (canonicalIndex z).1 = z.1 := by grind [canonicalIndex]

theorem canonicalIndex_prefix {B : ℕ} {z : _}
    (hz : z ∈ splitPrefixCoordinates B) : canonicalIndex z ∈ splitPrefixCoordinates B := by
  grind [canonicalIndex, mem_splitPrefixCoordinates]

def quotientField (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (canonicalIndex (w,k))

theorem quotientField_measurable : Measurable quotientField := by
  unfold quotientField
  fun_prop

/-- Infinite reversible quotient survival, realized by iid marks on canonical
coordinates. Noncanonical and invalid latent coordinates do not affect it. -/
noncomputable def quotientSurvival (a : I)  :=
  infiniteSplitPi a {ω | ReversibleUnbounded 2 (quotientField ω)}

end RAFReactionQuotient
