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

theorem deletion_comparison {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (T U : Finset α) (hUT : U ⊆ T)
    (hstep : ∀ V ⊆ T, ∀ x ∈ V, F (V.erase x) ≤ 2 * F V) :
    F U ≤ (2 : ℝ) ^ (T.card - U.card) * F T := by
  induction T using Finset.strongInductionOn generalizing U
  rename_i T ih
  by_cases heq : U = T
  · subst U
    simp
  · have hnot : ¬ T ⊆ U := fun hTU => heq (Finset.Subset.antisymm hUT hTU)
    obtain ⟨x, hxT, hxU⟩ := Finset.not_subset.mp hnot
    have hue : U ⊆ T.erase x := by
      intro y hy
      exact Finset.mem_erase.mpr ⟨by intro h; subst y; exact hxU hy, hUT hy⟩
    have hsmall := ih (T.erase x) (Finset.erase_ssubset hxT) U hue
      (fun V hV => hstep V (hV.trans (Finset.erase_subset _ _)))
    have hscale : (2 : ℝ) ^ ((T.erase x).card - U.card) * F (T.erase x) ≤
        (2 : ℝ) ^ ((T.erase x).card - U.card) * (2 * F T) :=
      mul_le_mul_of_nonneg_left (hstep T Finset.Subset.rfl x hxT) (by positivity)
    have hcard : T.card - U.card = ((T.erase x).card - U.card) + 1 := by
      have hle := Finset.card_le_card hue
      have herase := Finset.card_erase_of_mem hxT
      have hpos := Finset.card_pos.mpr ⟨x, hxT⟩
      omega
    calc
      F U ≤ (2 : ℝ) ^ ((T.erase x).card - U.card) * F (T.erase x) := hsmall
      _ ≤ (2 : ℝ) ^ ((T.erase x).card - U.card) * (2 * F T) := hscale
      _ = (2 : ℝ) ^ (T.card - U.card) * F T := by rw [hcard, pow_succ]; ring
/-- A signed finite recurrence with sufficiently small weighted local activity
has a positive partition function, uniformly in the number of labels. -/
theorem positive_deletion_recurrence {α β : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (rows : Finset α → α → Finset β)
    (removed : β → Finset α) (weight : β → ℝ)
    (hempty : F ∅ = 1)
    (hremove : ∀ S x, x ∈ S → ∀ P ∈ rows S x, x ∈ removed P ∧ removed P ⊆ S)
    (hrec : ∀ S x, x ∈ S →
      F S = F (S.erase x) + ∑ P ∈ rows S x, weight P * F (S \ removed P))
    (hactivity : ∀ S x, x ∈ S →
      (∑ P ∈ rows S x, |weight P| * (2 : ℝ) ^ ((removed P).card - 1)) ≤ 1 / 2) :
    ∀ S, 0 < F S ∧ ∀ x ∈ S,
      F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x) := by
  intro S
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases he : S = ∅
  · subst S
    simp [hempty]
  · have hratio : ∀ x ∈ S,
        0 < F (S.erase x) ∧
        F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x) := by
      intro x hx
      have hprevious := ih (S.erase x) (Finset.erase_ssubset hx)
      have hterms : ∀ P ∈ rows S x,
          0 ≤ F (S \ removed P) ∧
          F (S \ removed P) ≤ (2 : ℝ) ^ ((removed P).card - 1) * F (S.erase x) := by
        intro P hP
        obtain ⟨hxP, hPS⟩ := hremove S x hx P hP
        have hsub : S \ removed P ⊆ S.erase x := by
          intro y hy
          obtain ⟨hyS, hyn⟩ := Finset.mem_sdiff.mp hy
          exact Finset.mem_erase.mpr ⟨by intro h; subst y; exact hyn hxP, hyS⟩
        have hproper : S \ removed P ⊂ S :=
          hsub.trans_ssubset (Finset.erase_ssubset hx)
        have hc : (S.erase x).card - (S \ removed P).card = (removed P).card - 1 := by
          have hRcard := Finset.card_le_card hPS
          have hRpos := Finset.card_pos.mpr ⟨x, hxP⟩
          rw [Finset.card_erase_of_mem hx, Finset.card_sdiff_of_subset hPS]
          omega
        refine ⟨(ih (S \ removed P) hproper).1.le, ?_⟩
        rw [← hc]
        apply deletion_comparison F (S.erase x) (S \ removed P) hsub
        intro V hV y hy
        have hp : V ⊂ S := hV.trans_ssubset (Finset.erase_ssubset hx)
        have hlower := (ih V hp).2 y hy |>.1
        linarith
      have herr : |F S - F (S.erase x)| ≤ F (S.erase x) / 2 := by
        rw [hrec S x hx, add_sub_cancel_left]
        calc
          |∑ P ∈ rows S x, weight P * F (S \ removed P)| ≤
              ∑ P ∈ rows S x, |weight P * F (S \ removed P)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ P ∈ rows S x, |weight P| * F (S \ removed P) := by
            apply Finset.sum_congr rfl
            intro P hP
            rw [abs_mul, abs_of_nonneg (hterms P hP).1]
          _ ≤ ∑ P ∈ rows S x,
              |weight P| * ((2 : ℝ) ^ ((removed P).card - 1) * F (S.erase x)) := by
            apply Finset.sum_le_sum
            intro P hP
            exact mul_le_mul_of_nonneg_left (hterms P hP).2 (abs_nonneg _)
          _ = (∑ P ∈ rows S x, |weight P| * (2 : ℝ) ^ ((removed P).card - 1)) *
              F (S.erase x) := by simp_rw [← mul_assoc]; rw [Finset.sum_mul]
          _ ≤ 1 / 2 * F (S.erase x) :=
            mul_le_mul_of_nonneg_right (hactivity S x hx) hprevious.1.le
          _ = F (S.erase x) / 2 := by ring
      refine ⟨hprevious.1, ?_, ?_⟩
      · linarith [neg_le_abs (F S - F (S.erase x))]
      · linarith [le_abs_self (F S - F (S.erase x))]
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have h := hratio x hx
    refine ⟨by linarith [h.1], fun y hy => (hratio y hy).2⟩

/-- Multiplying the deletion ratios gives the history density bounds in
lower_heaps, independently of the total number of pieces. -/
theorem deletion_ratios_global_bounds {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (hempty : F ∅ = 1)
    (hstep : ∀ S x, x ∈ S →
      F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x)) :
    ∀ S, (1 / 2 : ℝ) ^ S.card ≤ F S ∧ F S ≤ (3 / 2 : ℝ) ^ S.card := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp [hempty]
  | @insert x S hx ih =>
    have h := hstep (insert x S) x (by simp)
    simp only [Finset.erase_insert hx] at h
    rw [Finset.card_insert_of_notMem hx, pow_succ, pow_succ]
    constructor <;> nlinarith [ih.1, ih.2]

end NearlyMinimax
