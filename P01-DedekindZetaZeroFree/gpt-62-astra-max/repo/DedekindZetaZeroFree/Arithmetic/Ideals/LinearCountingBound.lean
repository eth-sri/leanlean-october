module

public import DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

variable (F : Type*) [Field F] [NumberField F]

private theorem card_boundedNormIdeals_eq_natCard (X : ℝ) :
    Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} = (boundedNormIdeals F X).card := by
  change Nat.card (setOf (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ≤ X)) =
    (boundedNormIdeals F X).card
  have h := Set.ncard_eq_toFinset_card
    (setOf (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ≤ X)) (finite_ideals_absNorm_le F X)
  rw [Nat.card_coe_set_eq, h]
  rfl

theorem exists_ideal_count_bound_finset :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ X : ℝ, 1 ≤ X → ((boundedNormIdeals F X).card : ℝ) ≤ C * X) ∧
      (∀ X : ℝ, 1 ≤ X → ∀ s : Finset (Ideal (𝓞 F)),
        (∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ X) → (s.card : ℝ) ≤ C * X) := by
  classical

  obtain ⟨b, hb⟩ := ((NumberField.Ideal.tendsto_norm_le_div_atTop F).isBoundedUnder_le).eventually_le
  rw [Filter.eventually_atTop] at hb
  obtain ⟨T, hT⟩ := hb

  set T' : ℝ := max T 1 with hT'def
  have hbound : ∀ X : ℝ, T' ≤ X → ((boundedNormIdeals F X).card : ℝ) ≤ b * X := by
    intro X hX
    have h := hT X (le_trans (le_max_left _ _) hX)
    rw [card_boundedNormIdeals_eq_natCard F X] at h
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hX))).mp h

  set K : ℝ := max 1 (max b ((boundedNormIdeals F T').card : ℝ)) with hK
  have hK1 : 1 ≤ K := by rw [hK]; exact le_max_left _ _
  have hglob : ∀ X : ℝ, 1 ≤ X → ((boundedNormIdeals F X).card : ℝ) ≤ K * X := by
    intro X hX1
    rcases le_or_gt T' X with h | h
    · refine le_trans (hbound X h) (mul_le_mul_of_nonneg_right ?_ (le_of_lt (lt_of_lt_of_le zero_lt_one hX1)))
      rw [hK]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    · have hKT : ((boundedNormIdeals F T').card : ℝ) ≤ K := by
        rw [hK]; exact le_trans (le_max_right _ _) (le_max_right _ _)
      exact le_trans (by
        exact_mod_cast Finset.card_le_card (boundedNormIdeals_mono F (le_of_lt h))) (le_trans hKT (le_mul_of_one_le_right (le_trans zero_le_one hK1) hX1))
  refine ⟨K, hK1, hglob, ?_⟩
  intro X hX1 s hs
  have hsub : s ⊆ boundedNormIdeals F X := by
    intro I hI
    rw [mem_boundedNormIdeals]
    exact hs I hI
  refine le_trans ?_ (hglob X hX1)
  exact_mod_cast Finset.card_le_card hsub

theorem exists_ideal_count_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ((boundedNormIdeals F X).card : ℝ) ≤ C * X := by
  obtain ⟨C, hC, hglobal, _⟩ := exists_ideal_count_bound_finset F
  exact ⟨C, hC, hglobal⟩

end DedekindZetaZeroFree.LargeSieve
