module
public import proofs.RAF.Concrete.Closure

/-! The split reaction ensemble, indexed by the seed/nonseed partition. -/

@[expose] public section

namespace RAF.Concrete

open MeasureTheory ProbabilityTheory unitInterval
open RAF.Polymer
variable (n : Nat) (lambda : ℝ)

abbrev SeedCoord := Molecule n × PolymerSeedReaction n 2
abbrev NonseedReaction :=
  {r : Reaction n // ¬ RevSeedReaction (binaryPolymerCRS n 2) r}
abbrev NonseedCoord := Molecule n × NonseedReaction n

/-- Partitioned representation of every molecule--reaction coordinate. -/
abbrev CatalysisSample := Set (SeedCoord n) × Set (NonseedCoord n)

noncomputable def rawCatalysisP : ℝ :=
  lambda * n / Fintype.card (Reaction n)

/-- Clamp only to obtain a total unit-interval parameter.  The asymptotic proof
later shows the clamp is inactive in the positive fixed-lambda tail. -/
noncomputable def catalysisP : I :=
  ⟨min 1 (max 0 (rawCatalysisP n lambda)), by
    constructor
    · exact le_min (by norm_num) (le_max_left _ _)
    · exact min_le_left _ _⟩

/-- Genuine product Bernoulli probability measure.  Seed and nonseed
coordinates are independently sampled with the same parameter. -/
noncomputable def uniformCatalysisMeasure :
    Measure (CatalysisSample n) :=
  (setBernoulli (Set.univ : Set (SeedCoord n)) (catalysisP n lambda)).prod
    (setBernoulli (Set.univ : Set (NonseedCoord n)) (catalysisP n lambda))

/-- Convert a sampled partition back to the catalysis relation on the concrete
base reactions. -/
def catalysisOf {n : Nat} (ω : CatalysisSample n) :
    Catalysis (Molecule n) (Reaction n) := fun x r =>
  if h : RevSeedReaction (binaryPolymerCRS n 2) r then
    (x, ⟨r, h⟩) ∈ ω.1
  else
    (x, ⟨r, h⟩) ∈ ω.2

noncomputable instance uniformCatalysisMeasure_isProbability :
    IsProbabilityMeasure (uniformCatalysisMeasure n lambda) := by
  unfold uniformCatalysisMeasure
  infer_instance

def HasRAFEvent : Set (CatalysisSample n) :=
  {ω | ∃ S : Finset (Reaction n),
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf ω) S}

end RAF.Concrete

namespace RAFEmergenceApprox
open RAF.Polymer RAF.Concrete HordijkSteelThreshold unitInterval

/-- The inherited lambda parametrization covers every homogeneous probability
at every nontrivial finite source size. -/
theorem catalysisP_covers_probability (n : ℕ) (hn : 2 ≤ n) (p : I) :
    catalysisP n ((p:ℝ) * Fintype.card (Reaction n) / n) = p := by
  have hj : 0 < Fintype.card (Reaction n) := Fintype.card_pos_iff.mpr ⟨⟨⟨1,by omega⟩,0,0⟩⟩
  apply Subtype.ext
  have he : rawCatalysisP n ((p:ℝ) * Fintype.card (Reaction n) / n) = p := by
    unfold rawCatalysisP
    field_simp
  change min 1 (max 0 (rawCatalysisP n _)) = (p:ℝ)
  grind

end RAFEmergenceApprox
