module

public import NearlyMinimax.HistoryShapeCount
public import NearlyMinimax.WordHeap


@[expose] public section

/-!
# The actual dependent-degree shape-count exponent

Each distinct dependent pair contributes one binary interleaving. Counting
pair incidences label by label proves the exact exponent
`(Delta-1) * sum_j n_j` in the source reference-law estimate.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

def historyIncidentPairs (dependent : J → J → Prop) (j : J) : Finset (HistoryOrderedDependentPair dependent) := by
  classical
  exact Finset.univ.filter (fun p => p.val.1 = j ∨ p.val.2 = j)

section
variable {dependent : J → J → Prop}

def historyPairOtherLabel (j : J)
    (p : HistoryOrderedDependentPair dependent) : J := if p.val.1 = j then p.val.2 else p.val.1

theorem historyIncidentPair_reconstruct {j : J}
    {p : HistoryOrderedDependentPair dependent} (hp : p ∈ historyIncidentPairs dependent j) :
    p.val = if j < historyPairOtherLabel j p then
      (j, historyPairOtherLabel j p) else (historyPairOtherLabel j p, j) := by
  rcases p with ⟨⟨a, b⟩, hab, hdep⟩
  obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
  rcases hp with rfl | rfl
  · simp [historyPairOtherLabel, hab]
  · simp [historyPairOtherLabel, hab.ne, not_lt_of_gt hab]

theorem historyIncidentPairs_card_le
    [Std.Refl dependent] [Std.Symm dependent] (j : J) :
    (historyIncidentPairs dependent j).card ≤ (dependentLabelFinset dependent j).card - 1 := by
  classical
  have hj : j ∈ dependentLabelFinset dependent j := Finset.mem_filter.2 ⟨Finset.mem_univ _, Std.Refl.refl _⟩
  rw [← Finset.card_erase_of_mem hj]
  apply Finset.card_le_card_of_injOn (historyPairOtherLabel j)
  · intro p hp
    obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
    rcases hp with hp | hp
    · have he : historyPairOtherLabel j p = p.val.2 := by simp [historyPairOtherLabel, hp]
      apply Finset.mem_erase.2
      refine ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩ <;> grind
    · have hne : p.val.1 ≠ j := by grind
      have he : historyPairOtherLabel j p = p.val.1 := by simp [historyPairOtherLabel, hne]
      rw [he]
      exact Finset.mem_erase.2 ⟨hne, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [← hp]; exact symm p.prop.2⟩⟩
  · intro p hp q hq hpq
    apply Subtype.ext
    rw [historyIncidentPair_reconstruct hp,
      historyIncidentPair_reconstruct hq, hpq]

end

theorem historyPairExponent_incidence (dependent : J → J → Prop) (n : J → ℕ) :
    (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) =
      ∑ j, (historyIncidentPairs dependent j).card * n j := by
  classical
  have hp : ∀ p : HistoryOrderedDependentPair dependent,
      n p.val.1 + n p.val.2 = ∑ j, if p.val.1 = j ∨ p.val.2 = j then n j else 0 := by
    intro p
    have ht : ∀ j, (if p.val.1 = j ∨ p.val.2 = j then n j else 0) =
        (if p.val.1 = j then n j else 0) + (if p.val.2 = j then n j else 0) := by
      aesop
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  calc
    _ = _ :=
      Finset.sum_congr rfl (fun p _ => hp p)
    _ = _ :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      simp [historyIncidentPairs]

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {Δ : ℕ}
    (hlabels : DegreeAtMost dependent Δ) (n : J → ℕ)
include hlabels

theorem historyPairExponent_le :
    (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) ≤ (Δ - 1) * ∑ j, n j := by
  rw [historyPairExponent_incidence, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.mul_le_mul_right (n j) ((historyIncidentPairs_card_le j).trans
    (Nat.sub_le_sub_right (hlabels j) 1))

/-- The exact finite-multiplicity shape bound in `lower_heaps`. -/
theorem historyMultiplicityShape_card_le_degree :
    Nat.card (HistoryMultiplicityShape dependent n) ≤ 2 ^ ((Δ - 1) * ∑ j, n j) := by
  calc
    _ ≤ _ :=
      historyMultiplicityShape_card_le n
    _ = _ :=
      Finset.prod_pow_eq_pow_sum ..
    _ ≤ _ := pow_le_pow_right₀ (by decide)
      (historyPairExponent_le hlabels n)

end NearlyMinimax
