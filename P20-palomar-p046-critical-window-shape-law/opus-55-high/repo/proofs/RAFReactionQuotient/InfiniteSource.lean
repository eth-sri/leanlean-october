module

public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.ReversibleEscapeProbability
public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
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

def quotientField (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω $ canonicalIndex (w,k)


/-- Infinite reversible quotient survival, realized by iid marks on canonical
coordinates. Noncanonical and invalid latent coordinates do not affect it. -/
noncomputable def quotientSurvival (a : I) : ENNReal :=
  infiniteSplitPi a {ω | ReversibleUnbounded 2 $ quotientField ω}

end RAFReactionQuotient
