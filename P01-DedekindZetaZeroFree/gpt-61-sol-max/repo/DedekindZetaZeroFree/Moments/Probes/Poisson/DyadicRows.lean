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

section
variable (u : Frequency D.recipe)
include u
def q   : ℝ := frequencyNorm D.recipe u

def dyadIndex   : ℕ := Nat.log 2 ⌊q D u⌋₊

theorem one_le_q   : (1 : ℝ) ≤ q D u :=
  RawFrequencyCount.one_le_frequencyNorm D.recipe u

theorem dyadIndex_spec   :
    (2 : ℝ) ^ dyadIndex D u ≤ q D u ∧ q D u < (2 : ℝ) ^ (dyadIndex D u + 1) := by
  have h1 := one_le_q D u
  have hn : ⌊q D u⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊q D u⌋₊ := Nat.le_floor (by simpa using h1)
    omega
  constructor
  · have h := Nat.pow_log_le_self 2 hn
    have h2 : ((2 ^ Nat.log 2 ⌊q D u⌋₊ : ℕ) : ℝ) ≤ (⌊q D u⌋₊ : ℝ) := by exact_mod_cast h
    have h3 : (⌊q D u⌋₊ : ℝ) ≤ q D u := Nat.floor_le (by linarith)
    unfold dyadIndex
    push_cast at h2
    linarith
  · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌊q D u⌋₊
    have h2 : ((⌊q D u⌋₊ : ℕ) : ℝ) < ((2 ^ (Nat.log 2 ⌊q D u⌋₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    have h3 : q D u < (⌊q D u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h4 : (⌊q D u⌋₊ : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 ⌊q D u⌋₊ + 1) : ℕ) : ℝ) := by
      have : ⌊q D u⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊q D u⌋₊ + 1) := h
      exact_mod_cast this
    unfold dyadIndex
    push_cast at h4
    linarith

theorem dyadIndex_spec'   :
    (2 : ℝ) ^ dyadIndex D u ≤ q D u ∧ q D u < 2 * (2 : ℝ) ^ dyadIndex D u := by
  have h := dyadIndex_spec D u
  rw [pow_succ] at h
  exact ⟨h.1, by linarith [h.2]⟩

theorem dyadIndex_eq_of_bounds   (k : ℕ)
    (h1 : (2 : ℝ) ^ k ≤ q D u) (h2 : q D u < (2 : ℝ) ^ (k + 1)) : dyadIndex D u = k := by
  have a1 : 2 ^ k ≤ ⌊q D u⌋₊ := by
    apply Nat.le_floor
    exact_mod_cast h1
  have a2 : ⌊q D u⌋₊ < 2 ^ (k + 1) := by
    apply Nat.floor_lt (by linarith [one_le_q D u]) |>.mpr
    exact_mod_cast h2
  exact Nat.log_eq_of_pow_le_of_lt_pow a1 a2

theorem dyadIndex_unique   (k : ℕ) :
    dyadIndex D u = k ↔ (2 : ℝ) ^ k ≤ q D u ∧ q D u < (2 : ℝ) ^ (k + 1) := by
  constructor
  · rintro rfl
    exact dyadIndex_spec D u
  · exact fun h => dyadIndex_eq_of_bounds D u k h.1 h.2
end


def rawDyad (k : ℕ) : Set (Frequency D.recipe) := {u | dyadIndex D u = k}

theorem rawDyad_eq (k : ℕ) :
    rawDyad D k = {u : Frequency D.recipe | (2 : ℝ) ^ k ≤ frequencyNorm D.recipe u ∧
      frequencyNorm D.recipe u < 2 * (2 : ℝ) ^ k} := by
  ext u
  simp only [rawDyad, Set.mem_setOf_eq, dyadIndex_unique, pow_succ]
  change _ ≤ q D u ∧ q D u < _ ↔ _ ≤ q D u ∧ q D u < _
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by linarith⟩

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

section
variable (Z : ℝ)
include Z
def smallSet   : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ q D u ≤ Z ^ Scales.smallCutoffExponent}

def mediumSet   : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ Z ^ Scales.smallCutoffExponent < q D u ∧ q D u ≤ Z ^ Scales.largeCutoffExponent}

def largeSet   : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ Z ^ Scales.largeCutoffExponent < q D u}

theorem smallSet_finite   : (smallSet D Z).Finite :=
  (finite_q_le D (Z ^ Scales.smallCutoffExponent)).subset fun _ h => h.2

theorem mediumSet_finite   : (mediumSet D Z).Finite :=
  (finite_q_le D (Z ^ Scales.largeCutoffExponent)).subset fun _ h => h.2.2

theorem nonprincipal_cover   :
    {u : Frequency D.recipe | u ≠ principalFrequency D.recipe} =
      smallSet D Z ∪ mediumSet D Z ∪ largeSet D Z := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_union, smallSet, mediumSet, largeSet]
  constructor
  · intro h
    by_cases h1 : q D u ≤ Z ^ Scales.smallCutoffExponent
    · exact Or.inl (Or.inl ⟨h, h1⟩)
    · by_cases h2 : q D u ≤ Z ^ Scales.largeCutoffExponent
      · exact Or.inl (Or.inr ⟨h, not_le.mp h1, h2⟩)
      · exact Or.inr ⟨h, not_le.mp h2⟩
  · rintro ((h | h) | h)
    · exact h.1
    · exact h.1
    · exact h.1

theorem mem_small_iff   (u : Frequency D.recipe) :
    u ∈ smallSet D Z ↔ u ≠ principalFrequency D.recipe ∧ q D u ≤ Z ^ Scales.smallCutoffExponent := Iff.rfl
end


section
variable (ρ Z : ℝ)
include ρ Z
def exceptionalMedium   : Set (Frequency D.recipe) :=
  {u | u ∈ mediumSet D Z ∧ u ∈ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u)}

def goodMedium   : Set (Frequency D.recipe) :=
  {u | u ∈ mediumSet D Z ∧ u ∉ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u)}

theorem exceptionalMedium_subset   : exceptionalMedium D ρ Z ⊆ mediumSet D Z :=
  fun _ h => h.1

theorem goodMedium_subset   : goodMedium D ρ Z ⊆ mediumSet D Z :=
  fun _ h => h.1

theorem exceptional_good_union   :
    exceptionalMedium D ρ Z ∪ goodMedium D ρ Z = mediumSet D Z := by
  ext u
  simp only [exceptionalMedium, goodMedium, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    by_cases h' : u ∈ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u)
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩

theorem goodMedium_finite   : (goodMedium D ρ Z).Finite :=
  (mediumSet_finite D Z).subset (goodMedium_subset D ρ Z)
end


theorem exceptionalMedium_mem_dyad {ρ Z : ℝ} {u : Frequency D.recipe}
    (h : u ∈ exceptionalMedium D ρ Z) :
    u ∈ RawFixed.FixedData.rawExceptionalSet D ρ ((2 : ℝ) ^ dyadIndex D u) ∧
      u ∈ rawDyad D (dyadIndex D u) := ⟨h.2, rfl⟩

end

end DedekindZetaZeroFree.Quantitative.RawRowSumDefinitions31
