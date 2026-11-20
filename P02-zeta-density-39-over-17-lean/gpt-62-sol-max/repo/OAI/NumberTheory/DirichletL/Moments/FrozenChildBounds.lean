module
public import OAI.NumberTheory.DirichletL.Moments.SecondFrozenRatioCost
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalAggregate
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

@[expose] public section

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace OAI.SevenEighths.FrozenSource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondExceptionalFamily CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum CenteredMomentRadialEligibleEnergy CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar CenteredMomentMobiusRegroup CenteredMomentSecondRetainedAggregate

local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- One choice of child character per live label, unit set and ray character. -/
abbrev ChildCharacters (S : Finset (Ideal O)) (β : Ideal O → ℂ) :=
  (q : ActiveLabel S β) → Finset (CommonIndex q.val.1 q.val.2) → RayCharacter → Character

/-- The chosen characters must supply the family on every such unit set. -/
abbrev ChildFamilies (η : Character) {S : Finset (Ideal O)} {β : Ideal O → ℂ}
    (τ : ChildCharacters S β) : Prop :=
  ∀ q U, Family η q.val.1 q.val.2
    (commonLabels_supported (activeSource S β) _ _ q.property).1
    (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)

/-- Child energy on the selected column of each nonexceptional physical block.
`envelope` is either the canonical envelope or its reference-scale normalization. -/
abbrev ChildBound (s : Input ι) (R0 : Ideal O) {S : Finset (Ideal O)} {β : Ideal O → ℂ}
    (τ : ChildCharacters S β) (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (W : 𝓢(ℝ,ℂ)) (Kphys radius : ℝ) (column : Ideal O × Ideal O → Ideal O)
    (envelope : (C D : Ideal O) → Finset (CommonIndex C D) → (Fin 4 → ℤ) → ℝ)
    (E : ℝ) (J : ℕ) : Prop :=
  ∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
  ∀n:SourceBlocks q.val.1 q.val.2 U Kphys radius (sourceRadius s),
  physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
    (commonLabels_supported (activeSource S β) _ _ q.property).1
    (commonLabels_supported (activeSource S β) _ _ q.property).2 U radius
    (partRows false s.η χ₀ Q m q.val.1 q.val.2 U radius) W Kphys
    (fun i=>(n i:ℤ))≠0→
  ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
    (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
  (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
  ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools (column q.val),
  frozenCoefficient b.val (column q.val) R0 s.ν s.W s.P≠0 →
  ∀a∈(commonData (withHeight s (τ q U χ) v) (column q.val) R0 b).toSource.active D0,
  childEnergy (commonData (withHeight s (τ q U χ) v) (column q.val) R0 b)
    (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
      E*envelope q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
      (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J)

end OAI.SevenEighths.FrozenSource
