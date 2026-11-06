module
public import Mathlib

public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Fekete's lemma for connection probabilities

This module isolates the analytic step used once the finite-distance
connection probabilities are known to be positive and supermultiplicative.
-/

@[expose] public section

namespace PottsDiscontinuity.CorrLength

open Filter Topology

/-- A nonnegative subadditive sequence has a finite asymptotic rate. -/
theorem nonnegative_subadditive_rate (a : ℕ → ℝ)
    (hsub : Subadditive a) (ha : ∀ n, 0 ≤ a n) :
    0 ≤ hsub.lim ∧ hsub.lim ≤ a 1 ∧
      Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 hsub.lim) := by
  have hbdd : BddBelow (Set.range fun n  => a n /  n ) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact div_nonneg (ha n) (Nat.cast_nonneg n)
  have hlim := hsub.tendsto_lim hbdd
  have hnonneg : 0 ≤ hsub.lim := by
    rw [Subadditive.lim]
    apply le_csInf
    · simp_all
    · rintro x ⟨n, hn, rfl⟩
      exact div_nonneg (ha n) (Nat.cast_nonneg n)
  have hle := hsub.lim_le_div hbdd (by norm_num : (1 : ℕ) ≠ 0)
  simp_all

/-- Positive supermultiplicative probabilities yield a finite limit for their
negative logarithms divided by the distance parameter. -/
theorem log_rate_of_supermultiplicative (p : ℕ → ℝ)
    (hp : ∀ n, 0 < p n) (hpone : ∀ n, p n ≤ 1)
    (hmul : ∀ m n, p m * p n ≤ p (m + n)) :
    ∃ L : ℝ, 0 ≤ L ∧ L ≤ -Real.log (p 1) ∧
      Tendsto (fun n : ℕ => -Real.log (p n) / (n : ℝ)) atTop (𝓝 L) := by
  
  
  
  obtain ⟨hL0, hL1, hlim⟩ := nonnegative_subadditive_rate (fun n => -Real.log (p n)) (by
                                                               intro m n
                                                               
                                                               have hlog  :=
                                                                 Real.log_le_log (mul_pos (hp m) (hp n)) (hmul m n)
                                                               rw [Real.log_mul (hp m).ne' (hp n).ne'] at hlog
                                                               linarith)  fun n => neg_nonneg.mpr (Eq.mp (congrArg (LE.le (Real.log (p n))) Real.log_one) (Real.log_le_log (hp n) (hpone n))) 
  grind

/-- Reindexing a sequence by the diagonal sites `diagonalSite n` halves its
per-site logarithmic rate. The only input is the exact identity
`diagonalSite (2*m) = diagonalSite (2*m+1) = (m,m)`. -/
theorem tendsto_rate_of_even_odd_subsequence (a b : ℕ → ℝ) (L : ℝ)
    (h : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 L))
    (heven : ∀ m, b (2 * m) = a m)
    (hodd : ∀ m, b (2 * m + 1) = a m) :
    Tendsto (fun n : ℕ => b n / (n : ℝ)) atTop (𝓝 (L / 2)) := by
  
  have hevenLim : Tendsto (fun m  => b (2 * m) /  (2 * m ) ) atTop
      (𝓝 (L / 2)) := by
    have h'  :=
      h.div_const 2
    grind
  
  have hoddLim : Tendsto (fun m  => b (2 * m + 1) /  (2 * m + 1 ) ) atTop
      (𝓝 (L / 2)) := by
    have h'  := h.mul  Stirling.tendsto_self_div_two_mul_self_add_one 
    have h'' : L * (1 / 2) = L / 2 := by ring
    rw [h''] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    rw [hodd m]
    
    field_simp
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro x hx
    
    exact Filter.Eventually.atTop_of_arithmetic
      (p := fun n => x < b n /  n ) (n := 2) (by norm_num)  fun k hk => by
                                                                  have hk' : k = 0 ∨ k = 1 := by omega
                                                                  rcases hk' with rfl | rfl
                                                                  · simpa using hevenLim.eventually (Ioi_mem_nhds hx)
                                                                  · simpa using hoddLim.eventually (Ioi_mem_nhds hx) 
  · intro y hy
    
    exact Filter.Eventually.atTop_of_arithmetic
      (p := fun n => b n /  n  < y) (n := 2) (by norm_num)  fun k hk => by
                                                                  have hk' : k = 0 ∨ k = 1 := by omega
                                                                  rcases hk' with rfl | rfl
                                                                  · simpa using hevenLim.eventually (Iio_mem_nhds hy)
                                                                  · simpa using hoddLim.eventually (Iio_mem_nhds hy) 

end PottsDiscontinuity.CorrLength
