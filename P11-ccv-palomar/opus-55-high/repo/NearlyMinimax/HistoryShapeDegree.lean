module

public import NearlyMinimax.HistoryShapeCount
public import NearlyMinimax.WordHeap
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗎

/-!
# The actual dependent-degree shape-count exponent

Each distinct dependent pair contributes one binary interleaving. Counting
pair incidences label by label proves the exact exponent
`(Delta-1) * sum_j n_j` in the source reference-law estimate.
-/


𝚲

𝗇 𝔏 p.val.1 = j
𝗇 𝔐 p.val.2 = j
def historyIncidentPairs (dependent : 𝙁) (j : J) : Finset $ HistoryOrderedDependentPair dependent := by
  classical
  exact Finset.univ.filter fun p => 𝔏 ∨ 𝔐

def historyPairOtherLabel (dependent : 𝙁) (j : J)
    (p : HistoryOrderedDependentPair dependent) : J := if 𝔏 then p.val.2 else p.val.1

𝗃 𝔑 ἀ dependent j
𝗇 𝔉 𝔑 historyPairOtherLabel p
theorem historyIncidentPair_reconstruct dependent (j : J)
    p (hp : p ∈ 𝔑 historyIncidentPairs) :
    p.val = if j < 𝔉 then
      (j, 𝔉) else (𝔉, j) := by
  rcases p with ⟨⟨a, b⟩, hab, hdep⟩
  obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
  rcases hp with rfl | rfl
  · simp [historyPairOtherLabel, hab]
  · simp [historyPairOtherLabel, hab.ne, not_lt_of_gt hab]

𝗇 𝔇 𝘼
𝗇 𝔊 𝙂
𝗇 𝔍 (𝔑 dependentLabelFinset).card
theorem historyIncidentPairs_card_le dependent
    (hrefl : 𝔊) (hsymm : 𝔇) (j : J) :
    (𝔑 historyIncidentPairs).card ≤ 𝔍 - 1 := by
  classical
  have hj : j ∈ 𝔑 dependentLabelFinset := Finset.mem_filter.2 ⟨Finset.mem_univ _, hrefl _⟩
  rw [← Finset.card_erase_of_mem hj]
  apply Finset.card_le_card_of_injOn 𝔑 historyPairOtherLabel
  · intro p hp
    obtain ⟨_, hp⟩ := Finset.mem_filter.1 hp
    rcases hp with hp | hp
    · have he : 𝔉 = p.val.2 := by simp [historyPairOtherLabel, hp]
      rw [he]
      apply Finset.mem_erase.2
      refine ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      · rw [← hp]; exact p.prop.1.ne.symm
      · rw [← hp]; exact p.prop.2
    · have hne : p.val.1 ≠ j := by rw [← hp]; exact p.prop.1.ne
      have he : 𝔉 = p.val.1 := by simp [historyPairOtherLabel, hne]
      rw [he]
      exact Finset.mem_erase.2 ⟨hne, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [← hp]; exact hsymm p.prop.2⟩⟩
  · intro p hp q hq hpq
    apply Subtype.ext
    rw [𝔑 historyIncidentPair_reconstruct p hp,
      𝔑 historyIncidentPair_reconstruct q hq, hpq]

𝗇 𝔄 if p.val.1 = j ∨ 𝔐 then n j else 0
𝗇 𝔎 n p.val.1 + n p.val.2
𝗇 𝔅 ∑ p : HistoryOrderedDependentPair dependent, 𝔎
𝗃 𝔒 if ἀ then n j else 0
theorem historyPairExponent_incidence dependent (n : J → ℕ) :
    𝔅 =
      ∑ j : J, (𝔑 historyIncidentPairs).card * n j := by
  classical
  have hp : ∀ p : HistoryOrderedDependentPair dependent,
      𝔎 = ∑ j : J, 𝔄 := by
    intro p
    have ht : ∀ j , 𝔄 =
        𝔒 𝔏 + 𝔒 𝔐 := by
      intro j
      by_cases h1 : 𝔏
      · have h2 : p.val.2 ≠ j := fun h => p.prop.1.ne $ h1.trans h.symm
        simp [h2]
      · by_cases h2 : 𝔐 <;> simp [h1]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  calc
    _ = ∑ p : HistoryOrderedDependentPair dependent, ∑ j : J, 𝔄 :=
      Finset.sum_congr rfl fun p _ => hp p
    _ = ∑ j : J, ∑ p : HistoryOrderedDependentPair dependent, 𝔄 :=
      Finset.sum_comm
    𝘿 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      simp [historyIncidentPairs]

𝗇 𝔈 (Δ - 1) * ∑ j : J, n j
theorem historyPairExponent_le dependent
    (hrefl : 𝔊) (hsymm : 𝔇)
    Δ (hlabels : ∀ j, 𝔍 ≤ Δ) (n : J → ℕ) :
    𝔅 ≤ 𝔈 := by
  rw [historyPairExponent_incidence, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.mul_le_mul_right (n j) $ (historyIncidentPairs_card_le dependent hrefl hsymm j).trans
    $ Nat.sub_le_sub_right (hlabels j) 1

/-- The exact finite-multiplicity shape bound in `lower_heaps`. -/
theorem historyMultiplicityShape_card_le_degree dependent
    (hrefl : 𝔊) (hsymm : 𝔇)
    Δ (hlabels : ∀ j, 𝔍 ≤ Δ) n :
    Nat.card (HistoryMultiplicityShape dependent n) ≤ 2 ^ 𝔈 := by
  calc
    _ ≤ ∏ p : HistoryOrderedDependentPair dependent, 2 ^ 𝔎 :=
      historyMultiplicityShape_card_le dependent hrefl hsymm n
    _ = 2 ^ 𝔅 :=
      Finset.prod_pow_eq_pow_sum ..
    𝖦 := pow_le_pow_right₀  𝖨₃ 
      $ historyPairExponent_le dependent hrefl hsymm Δ hlabels n
