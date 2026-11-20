module

public import Mathlib

@[expose] public section

/-! Positivity from the local deletion recurrence in lower_heaps.
This proves the algebraic positivity induction.  Constructing the history
space, its connected-component recurrence and its reference law is separate.
-/

noncomputable section
open scoped BigOperators
namespace NearlyMinimax

variable {α β : Type*} [DecidableEq α] {F : Finset α → ℝ}

theorem deletion_comparison
    (F : Finset α → ℝ) {T U : Finset α} (hUT : U ⊆ T)
    (hstep : ∀ V ⊆ T, ∀ x ∈ V, F (V.erase x) ≤ 2 * F V) :
    F U ≤ 2 ^ (T.card - U.card) * F T := by
  induction T using Finset.strongInductionOn generalizing U
  rename_i T ih
  by_cases heq : U = T
  · subst U
    simp
  · obtain ⟨x, hxT, hxU⟩ := Finset.not_subset.mp (fun hTU => heq (Finset.Subset.antisymm hUT hTU))
    have hue : U ⊆ T.erase x := by
      apply Finset.subset_erase.mpr <;> grind
    have hsmall := ih (T.erase x) (Finset.erase_ssubset hxT) hue
      (fun V hV => hstep V (hV.trans (Finset.erase_subset _ _)))
    have hscale : 2 ^ ((T.erase x).card - U.card) * F (T.erase x) ≤
        2 ^ ((T.erase x).card - U.card) * (2 * F T) :=
      by bound
    have hcard : T.card - U.card = ((T.erase x).card - U.card) + 1 := by
      have hle := Finset.card_le_card hue
      have herase := Finset.card_erase_of_mem hxT
      have hpos := Finset.card_pos.mpr ⟨x, hxT⟩
      omega
    calc
      _ ≤ _ := hsmall
      _ ≤ _ := hscale
      _ = _ := by rw [hcard]; ring
/-- A signed finite recurrence with sufficiently small weighted local activity
has a positive partition function, uniformly in the number of labels. -/
theorem positive_deletion_recurrence (rows : Finset α → α → Finset β)
    (removed : β → Finset α) (weight : β → ℝ)
    (hempty : F ∅ = 1)
    (hremove : ∀ S x, x ∈ S → ∀ P ∈ rows S x, x ∈ removed P ∧ removed P ⊆ S)
    (hrec : ∀ S x, x ∈ S →
      F S = F (S.erase x) + ∑ P ∈ rows S x, weight P * F (S \ removed P))
    (hactivity : ∀ S x, x ∈ S →
      (∑ P ∈ rows S x, |weight P| * 2 ^ ((removed P).card - 1)) ≤ 1 / 2) :
    ∀ S, 0 < F S ∧ ∀ x ∈ S,
      F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x) := by
  intro S
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases he : S = ∅
  · grind
  · have hratio : ∀ x ∈ S,
        0 < F (S.erase x) ∧
        F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x) := by
      intro x hx
      have hprevious := ih (S.erase x) (Finset.erase_ssubset hx)
      have hterms : ∀ P ∈ rows S x,
          0 ≤ F (S \ removed P) ∧
          F (S \ removed P) ≤ 2 ^ ((removed P).card - 1) * F (S.erase x) := by
        intro P hP
        obtain ⟨hxP, hPS⟩ := hremove S x hx P hP
        have hsub : S \ removed P ⊆ S.erase x := by
          apply sdiff_le_comm.mp <;> grind
        have hproper  :=
          hsub.trans_ssubset (Finset.erase_ssubset hx)
        have hc : (S.erase x).card - (S \ removed P).card = (removed P).card - 1 := by
          grind [Finset.card_le_card hPS]
        refine ⟨(ih (S \ removed P) hproper).1.le, ?_⟩
        rw [← hc]
        apply deletion_comparison F hsub
        intro V hV y hy
        grind
      have herr : |F S - F (S.erase x)| ≤ F (S.erase x) / 2 := by
        rw [hrec S x hx, add_sub_cancel_left]
        calc
          _ ≤
              _ :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ P ∈ rows S x, |weight P| * F (S \ removed P) := by
            apply Finset.sum_congr rfl
            simp_all
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro P hP
            exact mul_le_mul_of_nonneg_left (hterms P hP).2 (abs_nonneg _)
          _ = (∑ P ∈ rows S x, |weight P| * 2 ^ ((removed P).card - 1)) *
              F (S.erase x) := by simp_rw [← mul_assoc]; rw [Finset.sum_mul]
          _ ≤ 1 / 2 * F (S.erase x) :=
            by bound
          _ = _ := by ring
      grind
    grind

/-- Multiplying the deletion ratios gives the history density bounds in
lower_heaps, independently of the total number of pieces. -/
theorem deletion_ratios_global_bounds (hempty : F ∅ = 1)
    (hstep : ∀ S x, x ∈ S →
      F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x)) :
    ∀ S, (1 / 2) ^ S.card ≤ F S ∧ F S ≤ (3 / 2) ^ S.card := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp [hempty]
  | @insert x S hx ih =>
    have h := hstep (insert x S) x (by simp)
    simp [Finset.erase_insert hx] at h
    rw [Finset.card_insert_of_notMem hx, pow_succ, pow_succ]
    grind

end NearlyMinimax
