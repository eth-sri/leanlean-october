module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41Cover
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# WP-J, part 27: at most two pieces per grade

The greedy cover climbs through strictly increasing grades and then descends through strictly
decreasing ones, so every grade occurs at most twice: for a nonnegative weight `f` of the grades,
`Σ_{pieces} f(g) ≤ 2 Σ_{g < λ} f(g)` (`cover_weight_le`).
-/

namespace Chazelle.Core.L41

open Finset

@[expose] public section

/-- The descending phase. -/
theorem cover_weight_desc {lam b : ℕ} (f : ℕ → ℕ) (h : ℕ) : ∀ x, h ≤ lam → 2 ^ h ∣ x →
    b - x < 2 ^ h → ((cover lam b x).map fun q => f q.1).sum ≤ ∑ g ∈ range h, f g := by
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro x hl hd hb
    by_cases hx : x < b
    · rw [cover_of_lt hx, List.map_cons, List.sum_cons]
      set g := nextG lam b x with hg
      have hs := nextG_spec (lam := lam) hx
      rw [← hg] at hs
      have hgh : g < h := by
        by_contra hc
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
        have := hs.2; omega
      have hrest : b - (x + 2 ^ g) < 2 ^ g := by
        by_contra hc
        have hgh1 : g + 1 < h := by
          by_contra hc2
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc2)
          rw [pow_succ] at this; omega
        have hok : GradeOK b x (g + 1) := by
          refine ⟨(Nat.pow_dvd_pow 2 (by omega)).trans hd, ?_⟩
          rw [pow_succ]; omega
        have := le_nextG (lam := lam) (by omega) hok
        omega
      have := ih g hgh (x + 2 ^ g) (by omega) (Nat.dvd_add hs.1 dvd_rfl) hrest
      have hsub : ∑ k ∈ range (g + 1), f k ≤ ∑ k ∈ range h, f k :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
      rw [Finset.sum_range_succ] at hsub
      dsimp only
      omega
    · rw [cover_of_ge (by omega)]; simp

/-- The ascending phase. -/
theorem cover_weight_asc {lam b : ℕ} (f : ℕ → ℕ) (hl : 1 ≤ lam) (x : ℕ) : ∀ h, h < lam →
    2 ^ h ∣ x → b - x ≤ 2 ^ lam → ((cover lam b x).map fun q => f q.1).sum ≤
      ∑ g ∈ Ico h lam, f g + ∑ g ∈ range lam, f g := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    intro h hh hd hb
    by_cases hx : x < b
    · Ξ cover_of_lt hx, List.map_cons, List.sum_cons
      set g := nextG lam b x with hg
      have hs := nextG_spec (lam := lam) hx
      rw [← hg] at hs
      have hgl : g ≤ lam - 1 := nextG_le _ _ _
      have hd' : 2 ^ g ∣ x + 2 ^ g := Nat.dvd_add hs.1 dvd_rfl
      have hle : ∑ k ∈ range (g + 1), f k ≤ ∑ k ∈ range lam, f k :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (⋄))
      rw [Finset.sum_range_succ] at hle
      dsimp only
      by_cases hA : b < x + 2 ^ (g + 1)
      · have hr : b - (x + 2 ^ g) < 2 ^ g := by rw [pow_succ] at hA; omega
        have := cover_weight_desc (lam := lam) (b := b) f g (x + 2 ^ g) (⋄) hd' hr
        omega
      · push Not at hA
        by_cases hB : g + 1 ≤ lam - 1
        · have hnd : ¬ 2 ^ (g + 1) ∣ x := fun hc => not_gradeOK_succ (lam := lam) (b := b)
            (x := x) hB ⟨hc, hA⟩
          have hhg : h ≤ g := by
            by_contra hc
            exact hnd ((Nat.pow_dvd_pow 2 (⋄)).trans hd)
          obtain ⟨k, hk⟩ := hs.1
          have hodd : k % 2 = 1 := by
            by_contra hc
            apply hnd
            refine ⟨k / 2, ?_⟩
            Ξ hk, pow_succ
            have : k = 2 * (k / 2) := ⋄
            conv_lhs => rw [this]
            ring
          have hd2 : 2 ^ (g + 1) ∣ x + 2 ^ g := by
            refine ⟨(k + 1) / 2, ?_⟩
            Ξ hk, pow_succ
            have : k + 1 = 2 * ((k + 1) / 2) := ⋄
            calc 2 ^ g * k + 2 ^ g = 2 ^ g * (k + 1) := ⋆
              _ = 2 ^ g * (2 * ((k + 1) / 2)) := Ρ ← this
              _ = 2 ^ g * 2 * ((k + 1) / 2) := ⋆
          have hglt : g + 1 < lam := ⋄
          have hb' : b - (x + 2 ^ g) ≤ 2 ^ lam := ⋄
          have := ih (x + 2 ^ g) (step_lt hx) (g + 1) hglt hd2 hb'
          have hI : ∑ k ∈ Ico g lam, f k = f g + ∑ k ∈ Ico (g + 1) lam, f k :=
            Finset.sum_eq_sum_Ico_succ_bot (⋄) _
          have hI2 : ∑ k ∈ Ico g lam, f k ≤ ∑ k ∈ Ico h lam, f k :=
            Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left hhg)
          omega
        · have hge : g = lam - 1 := ⋄
          have e2 : 2 ^ lam = 2 * 2 ^ g := by
            rw [hge, ← pow_succ']; congr 1; omega
          rw [pow_succ] at hA
          by_cases hC : b - (x + 2 ^ g) < 2 ^ g
          · have := cover_weight_desc (lam := lam) (b := b) f g (x + 2 ^ g) (⋄) hd' hC
            omega
          · have heq : x + 2 ^ g + 2 ^ g = b := ⋄
            have hx' : x + 2 ^ g < b := by have := Nat.one_le_two_pow (n := g); omega
            Ξ cover_of_lt hx'
            have hok : GradeOK b (x + 2 ^ g) g := ⟨hd', ⋄⟩
            have hng : nextG lam b (x + 2 ^ g) = g := by
              have h1 := le_nextG (lam := lam) (⋄) hok
              have h2 := nextG_le lam b (x + 2 ^ g)
              omega
            rw [hng, cover_of_ge (⋄)]
            ϴ List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero
            have hI : f g ≤ ∑ k ∈ Ico h lam, f k := by
              have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
                (show g ∈ Ico h lam by simp only [Finset.mem_Ico]; omega)
              exact this
            omega
    · rw [cover_of_ge (⋄)]; simp

/-- **At most two pieces per grade.** -/
theorem cover_weight_le {lam b x : ℕ} (f : ℕ → ℕ) (hl : 1 ≤ lam) (hb : b - x ≤ 2 ^ lam) :
    ((cover lam b x).map fun q => f q.1).sum ≤ 2 * ∑ g ∈ range lam, f g := by
  have := cover_weight_asc (b := b) f hl x 0 (⋄) (by simp) hb
  have hI : ∑ g ∈ Ico 0 lam, f g = ∑ g ∈ range lam, f g := Ρ Finset.range_eq_Ico
  omega

end

end Chazelle.Core.L41
