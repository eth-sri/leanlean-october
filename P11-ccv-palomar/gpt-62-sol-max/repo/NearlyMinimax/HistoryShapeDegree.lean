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

def historyPairOtherLabel (dependent : J → J → Prop) (j : J)
    (p : HistoryOrderedDependentPair dependent) : J := if p.val.1 = j then p.val.2 else p.val.1

section
variable (dependent : J → J → Prop)

theorem historyIncidentPair_reconstruct (j : J)
    (p : HistoryOrderedDependentPair dependent) (hp : p ∈ historyIncidentPairs dependent j) :
    p.val = if j < historyPairOtherLabel dependent j p then
      (j, historyPairOtherLabel dependent j p) else (historyPairOtherLabel dependent j p, j) := by
  rcases p with ⟨⟨a, b⟩, hab, hdep⟩
  obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
  dsimp at hp ⊢
  rcases hp with rfl | rfl
  · simp [historyPairOtherLabel, hab]
  · simp [historyPairOtherLabel, hab.ne, not_lt_of_gt hab]

theorem historyIncidentPairs_card_le
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (j : J) :
    (historyIncidentPairs dependent j).card ≤ (dependentLabelFinset dependent j).card - 1 := by
  classical
  have hj : j ∈ dependentLabelFinset dependent j := Finset.mem_filter.2 ⟨Finset.mem_univ _, hrefl _⟩
  rw [← Finset.card_erase_of_mem hj]
  apply Finset.card_le_card_of_injOn (historyPairOtherLabel dependent j)
  · intro p hp
    obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
    grind [historyPairOtherLabel, dependentLabelFinset]
  · intro p hp q hq hpq
    apply Subtype.ext
    rw [historyIncidentPair_reconstruct dependent j p hp,
      historyIncidentPair_reconstruct dependent j q hq, hpq]

theorem historyPairExponent_incidence (n : J → ℕ) :
    (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) =
      ∑ j : J, (historyIncidentPairs dependent j).card * n j := by
  classical
  have hp : ∀ p : HistoryOrderedDependentPair dependent,
      n p.val.1 + n p.val.2 = ∑ j : J, if p.val.1 = j ∨ p.val.2 = j then n j else 0 := by
    intro p
    have ht : ∀ j : J, (if p.val.1 = j ∨ p.val.2 = j then n j else 0) =
        (if p.val.1 = j then n j else 0) + (if p.val.2 = j then n j else 0) := by
      grind
    simp [ht, Finset.sum_add_distrib]
  calc
    _ = ∑ p : HistoryOrderedDependentPair dependent, ∑ j : J, if p.val.1 = j ∨ p.val.2 = j then n j else 0 :=
      Finset.sum_congr rfl (fun p _ => hp p)
    _ = ∑ j : J, ∑ p : HistoryOrderedDependentPair dependent, if p.val.1 = j ∨ p.val.2 = j then n j else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      simp [historyIncidentPairs]

end

section
variable {dependent : J → J → Prop} {Δ : ℕ}
    (geom : HistoryDegreeBound dependent Δ) (n : J → ℕ)
include geom

theorem historyPairExponent_le :
    (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) ≤ (Δ - 1) * ∑ j : J, n j := by
  rw [historyPairExponent_incidence, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.mul_le_mul_right (n j) ((historyIncidentPairs_card_le dependent geom.refl geom.symm j).trans
    (Nat.sub_le_sub_right (geom.degree_le j) 1))

/-- The exact finite-multiplicity shape bound in `lower_heaps`. -/
theorem historyMultiplicityShape_card_le_degree :
    Nat.card (HistoryMultiplicityShape dependent n) ≤ 2 ^ ((Δ - 1) * ∑ j : J, n j) := by
  calc
    _ ≤ ∏ p : HistoryOrderedDependentPair dependent, 2 ^ (n p.val.1 + n p.val.2) :=
      historyMultiplicityShape_card_le dependent geom.refl geom.symm n
    _ = 2 ^ (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
      (historyPairExponent_le geom n)

end

end NearlyMinimax
