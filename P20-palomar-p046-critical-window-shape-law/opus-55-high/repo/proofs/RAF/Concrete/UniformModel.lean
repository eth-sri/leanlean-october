module

public import proofs.RAF.Concrete.SeedGateway
public import Mathlib.Probability.Distributions.SetBernoulli

@[expose] public section

namespace RAF.Concrete

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer

section
variable (n : Nat)

abbrev SeedCoord  := Molecule n × PolymerSeedReaction n 2
abbrev NonseedReaction  :=
  {r : Reaction n // ¬ RevSeedReaction (binaryPolymerCRS n 2) r}
abbrev NonseedCoord  := Molecule n × NonseedReaction n

/-- Partitioned representation of every molecule--reaction coordinate. -/
abbrev CatalysisSample  := Set (SeedCoord n) × Set (NonseedCoord n)

variable (lambda : ℝ)

noncomputable def rawCatalysisP   : ℝ :=
  lambda * n / Fintype.card (Reaction n)

/-- Clamp only to obtain a total unit-interval parameter.  The asymptotic proof
later shows the clamp is inactive in the positive fixed-lambda tail. -/
noncomputable def catalysisP   : I :=
  ⟨min 1 $ max 0 $ rawCatalysisP n lambda, by
    constructor
    · exact le_min (by norm_num) $ le_max_left _ _
    · exact min_le_left _ _⟩

/-- Genuine product Bernoulli probability measure.  Seed and nonseed
coordinates are independently sampled with the same parameter. -/
noncomputable def uniformCatalysisMeasure   :
    Measure (CatalysisSample n) :=
  (setBernoulli (Set.univ : Set $ SeedCoord n) $ catalysisP n lambda).prod
    (setBernoulli (Set.univ : Set $ NonseedCoord n) $ catalysisP n lambda)

noncomputable instance uniformCatalysisMeasure_isProbability   :
    IsProbabilityMeasure (uniformCatalysisMeasure n lambda) := by
  unfold uniformCatalysisMeasure
  infer_instance

end

/-- Convert a sampled partition back to the catalysis relation on the concrete
base reactions. -/
def catalysisOf {n : Nat} (ω : CatalysisSample n) :
    Catalysis (Molecule n) (Reaction n) := fun x r =>
  if h : RevSeedReaction (binaryPolymerCRS n 2) r then
    (x, ⟨r, h⟩) ∈ ω.1
  else
    (x, ⟨r, h⟩) ∈ ω.2

end RAF.Concrete
