module
public import OAI.NumberTheory.DirichletL.Energy.CanonicalSources
public import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
public import OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
public import OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate

@[expose] public section

noncomputable section
open scoped BigOperators Classical

namespace OAI.SevenEighths.CanonicalGaussianFrame
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentCommonRadialData
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional CenteredMomentSecondInputCapacitySource
open CenteredMomentAmplificationChildInput (volume_pos volume)
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentActiveSource
open CenteredMomentSecondBlockAggregate CenteredMomentSecondExceptionalFamily
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate
open OAI.RayFourExpansion ConcretePrimeRowBridge

local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- A bounded squarefree seed and the two common test profiles of a source. -/
abbrev WithSeedProfile {ι : Type*} [Fintype ι] (g : CanonicalSources.Geometry α) (src : Input ι) (Z Bseed : ℝ)
    (P : Ideal O → Profiles g.a g.b → Prop) : Prop :=
  ∀ seed : Ideal O, Squarefree seed → seed ≠ 0 → (seed.absNorm : ℝ) ≤ Z^Bseed →
  ∀ p : Profiles g.a g.b, p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
    src.X₁ ≤ Z^g.L → src.X₂ ≤ Z^g.L → src.Y₁ ≤ Z^g.L → src.Y₂ ≤ Z^g.L → P seed p

/-- Declared volume and width caps, with a penalty for clipping the profile. -/
abbrev WithWidthBudget {ι : Type*} [Fintype ι] (g : CanonicalSources.Geometry α) (src : Input ι)
    (Z K sigma asource : ℝ) (w : ι → ℝ) (P : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Mdecl Mwidth θclip : ℝ, 0 ≤ θclip →
    length Z src.X₁ + length Z src.X₂ + 6*g.κ*(∑ i, w i) ≤ Mdecl →
    Real.logb Z K + Real.logb Z (src.η.modulus.absNorm : ℝ) ≤ Mdecl →
    Real.logb Z K + Real.logb Z (src.η.modulus.absNorm : ℝ) ≤ Mwidth →
    Mwidth - sigma/2 ≤ g.Mcap → Real.logb Z (max 1 g.b * max 1 g.b) ≤ 2*θclip →
    asource ≤ lowerFactor g.N g.lower g.a → P Mdecl Mwidth θclip

/-- The finite common-source column family in the Gaussian estimate. -/
abbrev WithGaussFamily (input : Input α) (R seed : Ideal O)
    (P : ∀ (Scols : Finset (Ideal O)) (β : Ideal O → ℂ),
      ((q : ActiveLabel Scols β) → Finset (CommonIndex q.val.1 q.val.2) → RayCharacter → Character) →
      RayCharacter → O → Prop) : Prop :=
  ∀ Scols : Finset (Ideal O), ∀ β : Ideal O → ℂ,
    Scols = finiteColumns (Fintype.piFinset input.pools) → β = coefficient input R seed →
  ∃ family : (q : ActiveLabel Scols β) → Finset (CommonIndex q.val.1 q.val.2) → RayCharacter → Character,
    (∀ q U, Family input.η q.val.1 q.val.2
      (commonLabels_supported (activeSource Scols β) _ _ q.property).1
      (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀ χ₀ : RayCharacter, ∀ m : O, m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m → P Scols β family χ₀ m

/-- The Gaussian estimates use the lower of the four length scales. -/
abbrev WithLowerLengths (input : Input α) (Z : ℝ) (P : ℝ → Prop) : Prop :=
    ∀ r : ℝ, Z^r ≤ input.X₁ → Z^r ≤ input.X₂ → Z^r ≤ input.Y₁ → Z^r ≤ input.Y₂ → P r

/-- The constants of a Gaussian provider, followed by the internal modulus and height. -/
abbrev GaussProvider (M : Ideal O)
    (P : ℕ → Finset (ℕ × ℕ) → ℕ → ℝ → ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) →
      ℝ → ℝ → ℝ → ℝ → Character → Ideal O → ℝ → ℝ → Prop) : Prop :=
  ∃ n : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ dc : ℕ, ∃ Cc : ℝ, 0 < Cc ∧
  ∃ J : ℕ, ∃ Sp Sf : Finset (ℕ × ℕ), (0,0) ∈ Sp ∧
  ∃ Cm Ce Cd Ct : ℝ, 0 < Cm ∧ 0 ≤ Ce ∧ 0 < Cd ∧ 0 < Ct ∧
  CanonicalSources.WithInternalModulus M fun η₀ Q =>
    ∃ Kc : ℝ, 0 < Kc ∧ ∃ Z₀ : ℝ, 1 < Z₀ ∧ P n T dc Cc J Sp Sf Cm Ce Cd Ct η₀ Q Kc Z₀

theorem Profiles.zero_of_pos {a b : ℝ} (p : Profiles a b) (ha : 0 < a) (j : Fin 2) :
    p.profile j 0 = 0 := by
  by_contra h
  exact ha.not_ge (p.support j h).1

/-- Capacity transferred to every nonzero column of the structured child. -/
theorem column_capacity (g : CanonicalSources.Geometry α) {ι : Type*} [Fintype ι]
    (input : Input ι) (p : Profiles g.a g.b) (hp₁ : p.profile 0 = input.W₁)
    (hp₂ : p.profile 1 = input.W₂) (hc : Fintype.card ι ≤ g.N) (hl : g.lower ≤ input.lower)
    {asource : ℝ} (ha : asource ≤ lowerFactor g.N g.lower g.a) (R seed : Ideal O)
    (I : Ideal O) (hI : coefficient input R seed I ≠ 0) :
    asource * volume input ≤ (I.absNorm : ℝ) := by
  apply (mul_le_mul_of_nonneg_right ha (volume_pos input).le).trans
  apply actual_lower_support g.N g.lower g.a g.hlower g.haPlain input hc hl _ _ R seed I hI
  · rw [← hp₁]
    exact fun _ h => (p.support 0 h).1
  · rw [← hp₂]
    exact fun _ h => (p.support 1 h).1

/-- Common profile support, degree and thresholds for finitely many Gaussian bounds. -/
theorem uniform_profiles {ι : Type*} [Fintype ι] (M : Ideal O)
    (P : ι → Finset (ℕ × ℕ) → ℕ → Character → Ideal O → ℝ → ℝ → Prop)
    (h : ∀ i, ∃ U J, CanonicalSources.WithInternalModulus M fun η Q =>
      ∃ C : ℝ, 0 < C ∧ ∃ Z : ℝ, 1 < Z ∧ P i U J η Q C Z) :
    ∃ U J, CanonicalSources.WithInternalModulus M fun η Q =>
      ∃ C : ℝ, 0 < C ∧ ∃ Z : ℝ, 1 < Z ∧ ∀ i, ∃ Ui Ji Ci Zi,
        Ui ⊆ U ∧ Ji ≤ J ∧ 0 < Ci ∧ Ci ≤ C ∧ Zi ≤ Z ∧ P i Ui Ji η Q Ci Zi := by
  choose U J h using h
  refine ⟨Finset.univ.biUnion U, ∑ i, J i, ?_⟩
  intro η Q hQM hQ0 hQt hQ72
  choose C hC Z hZ hp using fun i => h i η Q hQM hQ0 hQt hQ72
  obtain ⟨C', hC', hCC⟩ := CenteredMomentEnergyCanonicalUniformReference.exists_uniform_above 0 C
  obtain ⟨Z', hZ', hZZ⟩ := CenteredMomentEnergyCanonicalUniformReference.exists_uniform_above 1 Z
  exact ⟨C', hC', Z', hZ', fun i => ⟨U i, J i, C i, Z i,
    fun x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩,
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i), hC i, hCC i, hZZ i, hp i⟩⟩

end OAI.SevenEighths.CanonicalGaussianFrame
