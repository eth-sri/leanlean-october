module
public import Mathlib

public import PottsDiscontinuity.Bethe.Theorem23Bootstrap
public import PottsDiscontinuity.Bethe.Theorem23Spacing

/-! # Strict quantitative gap improvement at Bethe solutions -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem one_le_rootGapMultiplicity {N n : ℕ} (hs : 2 * n ≤ N) (j : Fin (n + 1)) :
    1 ≤ rootGapMultiplicity N n hs j := by
  unfold rootGapMultiplicity
  split_ifs
  · exact_mod_cast  by omega 
  · exact le_rfl

/-- A fixed outer mesh region has no Bethe solution on its gap boundaries
for large sizes. The additional inequalities on `c,D` make the limiting
explicit configuration lie strictly between the same boundaries. -/
theorem exists_uniform_strict_gap_bootstrap (r : ℕ) {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ c D K : ℝ, 0 < c ∧ c ≤ Real.pi ∧
      8 * Real.pi * (2 * r + 1 : ℝ) < D ∧ 0 < K ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀), ∀ (N k : ℕ),
      N₀ ≤ N → N = 2 * ( k + 1  + r) →
      ∀ (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N),
      DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
        (fun x => rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x)
        (rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) p hp (by omega) hs) ≤ K / N ∧
      ∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ∈ Ioo (c / (N : ℝ)) (D / (N : ℝ)) := by
  obtain ⟨mρ, hmρ, hρ⟩ := rho_uniform_lower_bound hΔ₀
  obtain ⟨mXi, hmXi, hXi⟩ := exists_uniform_Xi_lower_bound hΔ₀
  obtain ⟨M, hM⟩ := rho_uniform_upper_bound hΔ₀
  have hMpos  := (rho_pos hΔ₀ 0).trans_le (hM Δ₀ le_rfl 0)
  let B := M + 1 / mXi
  have hB : 0 < B := by  positivity
  let c := min Real.pi (1 / (2 * B))
  
  let D := 4 * (2 * r + 1 ) / mρ + 8 * Real.pi * (2 * r + 1 )
  have hDlarge : 8 * Real.pi * (2 * r + 1 ) < D := by
    
    have hpos : 0 < 4 * (2 * r + 1 ) / mρ := by positivity
    linarith
  
  obtain ⟨K, hK, hestimate⟩ := exists_uniform_density_bound_of_Bethe_mesh r hΔ₀ D (lt_trans (by positivity) hDlarge).le
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max K (2 * K / (mρ * mXi)))
  
  have hN₀nat : 0 < N₀ := by exact_mod_cast  hK.trans ((le_max_left _ _).trans_lt hN₀) 
  refine ⟨c, D, K,  lt_min Real.pi_pos (by positivity) , min_le_left _ _, hDlarge, hK, N₀, hN₀nat,
    fun Δ hΔ N k hlarge hcount p hp hs hBE hmesh => ?_⟩
  let hb := rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) p hp (by omega) hs
  have herr := hestimate Δ hΔ N k hcount p hp hs hBE hmesh
  have hNc : (0 : ℝ) < N := by exact_mod_cast  lt_of_lt_of_le hN₀nat hlarge 
  have hcast : (N₀ : ℝ) ≤ N := by exact_mod_cast hlarge
  
  
  refine ⟨herr, fun j => ⟨?_, ?_⟩⟩
  · 
    
    
    
    
    
    calc
      c /  N  <  1 / B  /  N  := div_lt_div_of_pos_right (by
                                                              
                                                              
                                                              bound) hNc
      _ = 1 / ( N  * B) := by rw [div_div, mul_comm B N]
      _ ≤ _ := ((div_le_div_of_nonneg_right (one_le_rootGapMultiplicity hs j) (mul_pos hNc hB).le).trans (rootPartition_gap_lower_of_densityNorm hΔ₀ hΔ p hp (by omega) hs
                                                                      hmXi hXi hb (herr.trans ((div_le_one hNc).2 (((le_max_left _ _).trans_lt hN₀).trans_le hcast).le)) hM hB j))
  · 
    
    
    calc
      _ ≤ 2 * rootGapMultiplicity N (k + 1) hs j / (mρ *  N ) :=  rootPartition_gap_upper_of_norm_le hΔ₀ hΔ p hp (by omega) hs
                                                                        hmXi hXi mρ hmρ hρ hb herr (by
                                                                                                      apply (div_le_iff₀ (mul_pos hNc hmXi)).2
                                                                                                      
                                                                                                      have ht' := (div_lt_iff₀ (mul_pos hmρ hmXi)).mp (((le_max_right _ _).trans_lt hN₀).trans_le hcast)
                                                                                                      nlinarith only [ht']) j 
      _ ≤ 2 * (2 * r + 1 ) / (mρ *  N ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount j) (by norm_num)) (by positivity)
      _ =  2 * (2 * r + 1 ) / mρ  /  N  := by rw [div_div]
      _ < D /  N  := div_lt_div_of_pos_right (by
                                                    dsimp [D]
                                                    
                                                    have hpi : 0 < 8 * Real.pi * (2 * r + 1 ) := by positivity
                                                    rw [show 4 * (2 * r + 1 ) / mρ = 2 * (2 * (2 * r + 1 ) / mρ) by ring]
                                                    have hpos2 : 0 < 2 * (2 * r + 1 ) / mρ := by positivity
                                                    linarith) hNc

end PottsDiscontinuity.Bethe
