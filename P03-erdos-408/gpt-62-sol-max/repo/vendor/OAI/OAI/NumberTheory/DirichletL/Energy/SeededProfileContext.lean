module

public import OAI.NumberTheory.DirichletL.Energy.Bands
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair

@[expose] public section

namespace OAI.SevenEighths
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve CenteredMomentEnergyBands
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

/-- The matched plain profiles at the prescribed side-length ceiling. -/
abbrev WithPlainProfiles {α : Type*} [Fintype α] (src : Input α) (a b L Z : ℝ)
    (P : Profiles a b → Prop) : Prop :=
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L → P p

/-- Select a bounded squarefree seed and a profile for the source's two weights. -/
abbrev WithSeedProfiles {α : Type*} [Fintype α] (src : Input α) (a b L Z Bseed : ℝ)
    (P : Ideal O → Profiles a b → Prop) : Prop :=
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    WithPlainProfiles src a b L Z (P seed)

/-- The profile and scale bounds used by the seeded canonical estimates. -/
abbrev WithSeededProfile {α : Type*} [Fintype α] (src : Input α) (w : α → ℝ)
    (a b L κ Mcap Z K sigma Bseed : ℝ) (P : Ideal O → Profiles a b → ℝ → ℝ → ℝ → Prop) : Prop :=
    WithSeedProfiles src a b L Z Bseed fun seed p =>
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip → P seed p Mdecl Mwidth θclip

/-- Reserve used to charge the declared source width and clipping loss. -/
abbrev WithClipBudget {α : Type*} [Fintype α] (src : Input α) (w : α → ℝ)
    (b κ Z K : ℝ) (P : ℝ → ℝ → Prop) : Prop :=
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip → P Mdecl θclip

end OAI.SevenEighths
