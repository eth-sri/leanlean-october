module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyData
public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyCount

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawRowSumDefinitions31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def q (u : Frequency D.recipe) : ℝ := frequencyNorm D.recipe u

def dyadIndex (u : Frequency D.recipe) : ℕ := Nat.log 2 ⌊q D u⌋₊

theorem one_le_q (u : Frequency D.recipe) : (1 : ℝ) ≤ q D u :=
  RawFrequencyCount.one_le_frequencyNorm D.recipe u

theorem dyadIndex_spec (u : Frequency D.recipe) :
    (2 : ℝ) ^ dyadIndex D u ≤ q D u ∧ q D u < (2 : ℝ) ^ (dyadIndex D u + 1) := by
  have h1 := one_le_q D u
  have hn : ⌊q D u⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊q D u⌋₊ := Nat.le_floor (by grind)
    omega
  constructor
  · have h := Nat.pow_log_le_self 2 hn
    have h2 : ((2 ^ Nat.log 2 ⌊q D u⌋₊ : ℕ) : ℝ) ≤ (⌊q D u⌋₊ : ℝ) := by exact_mod_cast h
    have h3 : (⌊q D u⌋₊ : ℝ) ≤ q D u := Nat.floor_le (by linarith)
    unfold dyadIndex
    grind
  · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌊q D u⌋₊
    have h2 : ((⌊q D u⌋₊ : ℕ) : ℝ) < ((2 ^ (Nat.log 2 ⌊q D u⌋₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    have h3 : q D u < (⌊q D u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h4 : (⌊q D u⌋₊ : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 ⌊q D u⌋₊ + 1) : ℕ) : ℝ) := by
      have : ⌊q D u⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊q D u⌋₊ + 1) := h
      exact_mod_cast this
    unfold dyadIndex
    grind

theorem dyadIndex_spec' (u : Frequency D.recipe) :
    (2 : ℝ) ^ dyadIndex D u ≤ q D u ∧ q D u < 2 * (2 : ℝ) ^ dyadIndex D u := by
  have h := dyadIndex_spec D u
  rw [pow_succ] at h
  grind

theorem dyadIndex_eq_of_bounds (u : Frequency D.recipe) (k : ℕ)
    (h1 : (2 : ℝ) ^ k ≤ q D u) (h2 : q D u < (2 : ℝ) ^ (k + 1)) : dyadIndex D u = k := by
  have a1 : 2 ^ k ≤ ⌊q D u⌋₊ := by
    apply Nat.le_floor
    grind
  have a2 : ⌊q D u⌋₊ < 2 ^ (k + 1) := by
    apply Nat.floor_lt (by linarith [one_le_q D u]) |>.mpr
    grind
  exact Nat.log_eq_of_pow_le_of_lt_pow a1 a2

theorem dyadIndex_unique (u : Frequency D.recipe) (k : ℕ) :
    dyadIndex D u = k ↔ (2 : ℝ) ^ k ≤ q D u ∧ q D u < (2 : ℝ) ^ (k + 1) := by
  constructor
  · rintro rfl
    exact dyadIndex_spec D u
  · exact fun h => dyadIndex_eq_of_bounds D u k h.1 h.2

def rawDyad (k : ℕ) : Set (Frequency D.recipe) := {u | dyadIndex D u = k}

theorem rawDyad_eq (k : ℕ) :
    rawDyad D k = {u : Frequency D.recipe | (2 : ℝ) ^ k ≤ frequencyNorm D.recipe u ∧
      frequencyNorm D.recipe u < 2 * (2 : ℝ) ^ k} := by
  ext u
  simp only [rawDyad, Set.mem_setOf_eq, dyadIndex_unique, pow_succ]
  change _ ≤ q D u ∧ q D u < _ ↔ _ ≤ q D u ∧ q D u < _
  grind

theorem rawDyad_finite_card :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℕ, (rawDyad D k).Finite ∧
      (Set.ncard (rawDyad D k) : ℝ) ≤ K * (2 : ℝ) ^ k := by
  obtain ⟨K, hK, h⟩ := RawFrequencyCount.frequency_dyad_count D.recipe
  refine ⟨K, hK, fun k => ?_⟩
  rw [rawDyad_eq]
  exact h _ (one_le_pow₀ (by norm_num))

theorem finite_q_le (B : ℝ) : {u : Frequency D.recipe | q D u ≤ B}.Finite := by
  obtain ⟨K, hK, h⟩ := RawFrequencyCount.frequency_count_lt D.recipe
  refine ((h (max 1 (B + 1)) (le_max_left _ _)).1).subset ?_
  intro u hu
  have : q D u ≤ B := hu
  change frequencyNorm D.recipe u < _
  exact lt_of_lt_of_le (by change q D u < B + 1; linarith) (le_max_right _ _)

def smallSet (Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ q D u ≤ Z ^ Scales.smallCutoffExponent}

def mediumSet (Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ Z ^ Scales.smallCutoffExponent < q D u ∧ q D u ≤ Z ^ Scales.largeCutoffExponent}

def largeSet (Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ Z ^ Scales.largeCutoffExponent < q D u}

theorem smallSet_finite (Z : ℝ) : (smallSet D Z).Finite :=
  (finite_q_le D (Z ^ Scales.smallCutoffExponent)).subset fun _ h => h.2

theorem mediumSet_finite (Z : ℝ) : (mediumSet D Z).Finite :=
  (finite_q_le D (Z ^ Scales.largeCutoffExponent)).subset fun _ h => h.2.2

theorem nonprincipal_cover (Z : ℝ) :
    {u : Frequency D.recipe | u ≠ principalFrequency D.recipe} =
      smallSet D Z ∪ mediumSet D Z ∪ largeSet D Z := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_union, smallSet, mediumSet, largeSet]
  constructor
  · intro h
    by_cases h1 : q D u ≤ Z ^ Scales.smallCutoffExponent
    · grind
    · grind
  · grind

theorem mem_small_iff (Z : ℝ) (u : Frequency D.recipe) :
    u ∈ smallSet D Z ↔ u ≠ principalFrequency D.recipe ∧ q D u ≤ Z ^ Scales.smallCutoffExponent := Iff.rfl

def exceptionalMedium (ρ Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ∈ mediumSet D Z ∧ u ∈ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u)}

def goodMedium (ρ Z : ℝ) : Set (Frequency D.recipe) :=
  {u | u ∈ mediumSet D Z ∧ u ∉ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u)}

theorem exceptionalMedium_subset (ρ Z : ℝ) : exceptionalMedium D ρ Z ⊆ mediumSet D Z :=
  fun _ h => h.1

theorem goodMedium_subset (ρ Z : ℝ) : goodMedium D ρ Z ⊆ mediumSet D Z :=
  fun _ h => h.1

theorem exceptional_good_union (ρ Z : ℝ) :
    exceptionalMedium D ρ Z ∪ goodMedium D ρ Z = mediumSet D Z := by
  ext u
  simp only [exceptionalMedium, goodMedium, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · grind
  · grind

theorem goodMedium_finite (ρ Z : ℝ) : (goodMedium D ρ Z).Finite :=
  (mediumSet_finite D Z).subset (goodMedium_subset D ρ Z)

theorem exceptionalMedium_mem_dyad {ρ Z : ℝ} {u : Frequency D.recipe}
    (h : u ∈ exceptionalMedium D ρ Z) :
    u ∈ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u) ∧
      u ∈ rawDyad D (dyadIndex D u) := ⟨h.2, rfl⟩

end

end DedekindZetaZeroFree.Quantitative.RawRowSumDefinitions31
