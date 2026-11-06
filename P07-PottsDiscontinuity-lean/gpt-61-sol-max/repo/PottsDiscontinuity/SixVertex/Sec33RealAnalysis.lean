module

public import Mathlib

/-!
# Exponential-growth comparison for the dominance repair

This real-analysis lemma isolates the inequality behind the large-`N` repair.  One-sided eventual
bounds for the two logarithmic growth rates are a reusable formulation of the corresponding
limsup hypotheses.  To apply it along even heights, replace each sequence `F M` by `F (2*M)`.
-/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.SixVertex

/-- If a positive exponential lower bound for `X` is controlled above by `Y * Z`, then the
exponential rate of `X` cannot exceed the sum of the one-sided rates of `Y` and `Z`. -/
theorem log_growth_le_of_eventually_factorized
    {C Λ Λmax a b : ℝ} (hC : 0 < C) (hΛ : 0 < Λ)
    (X Y Z : ℕ → ℝ)
    (hYpos : ∀ᶠ M : ℕ in atTop, 0 < Y M)
    (hZpos : ∀ᶠ M : ℕ in atTop, 0 < Z M)
    (hlower : ∀ᶠ M : ℕ in atTop, C * Λ ^ M ≤ X M)
    (hupper : ∀ᶠ M : ℕ in atTop, X M ≤ Y M * Z M)
    (hYrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop,
       1 / (M : ℝ)  * Real.log (Y M) ≤ a + ε)
    (hZrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop,
       1 / (M : ℝ)  * Real.log (Z M) ≤ Real.log Λmax + b + ε) :
    Real.log Λ ≤ Real.log Λmax + a + b := by
  by_contra hnot
  
  let ε  := (Real.log Λ - (Real.log Λmax + a + b)) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  
  have hsmall : Tendsto (fun M : ℕ =>  1 /  M   * Real.log C) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat).mul_const (Real.log C)
  have hsum : Tendsto (fun M : ℕ => Real.log Λ +
       1 /  M   * Real.log C) atTop (𝓝 (Real.log Λ)) := by
    simpa using (tendsto_const_nhds (x := Real.log Λ)).add hsmall
  have hleft : Tendsto (fun M : ℕ =>  1 /  M   *
      Real.log (C * Λ ^ M)) atTop (𝓝 (Real.log Λ)) := by
    have heq : (fun M : ℕ =>  1 /  M   * Real.log (C * Λ ^ M)) =ᶠ[atTop]
         fun M  => Real.log Λ +  1 /  M   * Real.log C  := by
      filter_upwards [eventually_gt_atTop 0] with M hM
      
      have hpow : Λ ^ M ≠ 0 := pow_ne_zero _ hΛ.ne'
      rw [Real.log_mul hC.ne' hpow]
      simp only [Real.log_pow]
      field_simp
      ring
    exact hsum.congr' heq.symm
  
  
  
  
  have hfalse : ∀ᶠ M : ℕ in atTop, False := by
    filter_upwards [ by
                       have hthreshold : Real.log Λmax + a + b + 3 * ε < Real.log Λ := by
                         dsimp [ε]
                         linarith
                       exact hleft.eventually (Ioi_mem_nhds hthreshold) , hlower, hupper, hYpos, hZpos,  hYrate ε hε ,  hZrate ε hε ,  eventually_gt_atTop 0 ]
      with M hleftM hlowerM hupperM hYposM hZposM hYM hZM hMposM
    have hbasepos  := mul_pos hC (pow_pos hΛ M)
    
    
    have hlog₂ := Real.log_le_log (lt_of_lt_of_le hbasepos hlowerM) hupperM
    rw [Real.log_mul hYposM.ne' hZposM.ne'] at hlog₂
    
    have hscaled := mul_le_mul_of_nonneg_left ((Real.log_le_log hbasepos hlowerM).trans hlog₂) (by positivity :
      0 ≤  1 / (M : ℝ) )
    grind
  rcases hfalse.exists with ⟨M, hM⟩
  exact hM

end PottsDiscontinuity.SixVertex
