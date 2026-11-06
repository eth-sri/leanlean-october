import proofs.RAFCriticalWindowQuantitative.ComputableParameters

import proofs.RAF.Concrete.SeedGateway
import Mathlib.Probability.Distributions.SetBernoulli



namespace RAF.Concrete

open MeasureTheory ProbabilityTheory unitInterval
open RAF.Polymer

variable (n : Nat)

abbrev SeedCoord  := Molecule n × PolymerSeedReaction n 2
abbrev NonseedReaction  :=
  {r : Reaction n // ¬ RevSeedReaction (binaryPolymerCRS n 2) r}
abbrev NonseedCoord  := Molecule n × NonseedReaction n

/-- Partitioned representation of every molecule--reaction coordinate. -/
abbrev CatalysisSample  := Set (SeedCoord n) × Set (NonseedCoord n)

/-- Genuine product Bernoulli probability measure.  Seed and nonseed
coordinates are independently sampled with the same parameter. -/
noncomputable def uniformCatalysisMeasure  (lambda : ℝ) :
    Measure (CatalysisSample n) :=
  (setBernoulli Set.univ (catalysisP n lambda)).prod
    (setBernoulli Set.univ (catalysisP n lambda))

noncomputable instance uniformCatalysisMeasure_isProbability (n : Nat) (lambda : ℝ) :
    IsProbabilityMeasure (uniformCatalysisMeasure n lambda) := by
  unfold uniformCatalysisMeasure
  infer_instance

/-- Convert a sampled partition back to the catalysis relation on the concrete
base reactions. -/
def catalysisOf {n : Nat} (ω : CatalysisSample n) :
    Catalysis (Molecule n) (Reaction n) := fun x r =>
  if h : RevSeedReaction (binaryPolymerCRS n 2) r then
    (x, ⟨r, h⟩) ∈ ω.1
  else
    (x, ⟨r, h⟩) ∈ ω.2

end RAF.Concrete
