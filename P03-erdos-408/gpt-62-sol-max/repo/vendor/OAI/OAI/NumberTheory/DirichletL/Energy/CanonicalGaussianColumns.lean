module

public import OAI.NumberTheory.DirichletL.Moments.SeededGaussianPower
public import OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
public import OAI.NumberTheory.DirichletL.Energy.CanonicalWindow

@[expose] public section

namespace OAI.SevenEighths

open scoped Classical
open HeckeFamily ConcreteTraceCRT CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentCommonAllocationSum
open CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate ConcretePrimeRowBridge
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentSecondPhysicalBlock
open CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic CenteredMomentSecondWindowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondInputCapacitySource
local notation "O" => HeckeFamily.O

/-- A choice of ray characters for each live column and its prime subsets. -/
abbrev ColumnFamily (Scols : Finset (Ideal O)) (β : Ideal O → ℂ) :=
  (q : ActiveLabel Scols β) → Finset (CommonIndex q.val.1 q.val.2) → RayCharacter → Character

/-- Select the column families of a seeded input, then use them on a good row. -/
abbrev WithGaussianColumns {ι : Type*} [Fintype ι] [DecidableEq (ι ⊕ Fin 2)] (input : Input ι) (R seed : Ideal O)
    (P : ∀ (Scols : Finset (Ideal O)) (β : Ideal O → ℂ), ColumnFamily Scols β →
      RayCharacter → O → Prop) : Prop :=
  ∀ Scols β, Scols = finiteColumns (Fintype.piFinset input.pools) → β = coefficient input R seed →
  ∃ family : ColumnFamily Scols β,
    (∀ q U, Family input.η q.val.1 q.val.2
      (commonLabels_supported (activeSource Scols β) _ _ q.property).1
      (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
  ∀ χ₀ m, m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m → P Scols β family χ₀ m


/-- Work at any scale below all four side lengths of the input. -/
abbrev AtGaussianScale {ι : Type*} [Fintype ι] (input : Input ι) (Z : ℝ) (P : ℝ → Prop) : Prop :=
  ∀ r : ℝ, Z^r ≤ input.X₁ → Z^r ≤ input.X₂ → Z^r ≤ input.Y₁ → Z^r ≤ input.Y₂ → P r

lemma profile_at_zero {a b : ℝ} (p : Profiles a b) (ha : 0 < a) (j : Fin 2) :
    p.profile j 0 = 0 := by
  by_contra h
  exact (not_le_of_gt ha) (p.support j h).1

/-- A support lower bound follows from the chosen plain profiles and the input floor. -/
lemma gaussian_lower_support {α ι : Type*} [Fintype ι] (cfg : CanonicalEnergyWindow α)
    (input : Input ι) (p : Profiles cfg.a cfg.b)
    (hcard : Fintype.card ι ≤ cfg.N) (hlower : cfg.lower ≤ input.lower)
    (h₁ : p.profile 0 = input.W₁) (h₂ : p.profile 1 = input.W₂)
    (aₛ : ℝ) (haₛ : aₛ ≤ lowerFactor cfg.N cfg.lower cfg.a) (R seed I : Ideal O)
    (hne : coefficient input R seed I ≠ 0) : aₛ * volume input ≤ (I.absNorm : ℝ) := by
  refine (mul_le_mul_of_nonneg_right haₛ (volume_pos input).le).trans ?_
  refine actual_lower_support cfg.N cfg.lower cfg.a cfg.hlower cfg.haPlain input hcard hlower ?_ ?_ _ _ _ hne
  · intro x hx; rw [← h₁] at hx; exact (p.support 0 hx).1
  · intro x hx; rw [← h₂] at hx; exact (p.support 1 hx).1

end OAI.SevenEighths
