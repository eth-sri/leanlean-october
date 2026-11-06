module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.ZeroRootTheorem
public import PottsDiscontinuity.SixVertex.Cor34FinalEquations

/-! # Corollary 3.4: apply the coordinate Bethe Ansatz on the block -/

@[expose] public section

open Matrix

namespace PottsDiscontinuity.SixVertex

/-- Restrict a full transfer-matrix eigenvector supported on particle number `n` to the
`n`-particle block. -/
theorem cor34_final_restrict_full_eigen {N n : ℕ} {c Δ : ℝ}
    {p : Fin n → ℝ} {μ : ℂ}
    (hfull : (transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.betheVector Δ p =
      μ • BetheAnsatz.betheVector Δ p) :
    (transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.blockWave Δ p =
      μ • BetheAnsatz.blockWave Δ p := by
  
  ext x
  have hx := congrFun hfull x.1
  simp only [Matrix.mulVec, dotProduct] at hx
  
  have hcompl :
       ∑ y : {y : Finset (Fin N) // y.card ≠ n},
        ((transferMatrix N c).map (algebraMap ℝ ℂ)) x.1 y.1 *
          BetheAnsatz.betheVector Δ p y.1  = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    simp [BetheAnsatz.betheVector_eq_zero Δ p y.2]
  have hrestr :
       ∑ y : State N n,
        ((transferMatrix N c).map (algebraMap ℝ ℂ)) x.1 y.1 *
          BetheAnsatz.betheVector Δ p y.1  =
      ∑ y : State N n,
        ((transferBlock N c n).map (algebraMap ℝ ℂ)) x y *
          BetheAnsatz.blockWave Δ p y := by
    
    
    simp [transferBlock, BetheAnsatz.betheVector]
  rw [←  Fintype.sum_subtype_add_sum_subtype
           (fun y  => y.card = n)
            fun y => ((transferMatrix N c).map (algebraMap ℝ ℂ)) x.1 y *
             BetheAnsatz.betheVector Δ p y  , hcompl, add_zero] at hx
  rw [hrestr] at hx
  simpa [BetheAnsatz.betheVector, Matrix.mulVec, dotProduct, x.2] using hx

/-- On the even branch, a Theorem 2.3 root tuple gives the regular Theorem 3.1
eigenvector equation on the transfer block. -/
theorem cor34_final_even_block_eigen {N n : ℕ} {c Δ : ℝ}
    (hc : 2 < c) (hΔ : BetheAnsatz.anisotropy c = Δ)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hn : Even n)
    (hBE : Bethe.DiscreteBetheEquation Δ N n p) :
    (transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.blockWave Δ p =
      BetheAnsatz.eigenvalueRegular c p • BetheAnsatz.blockWave Δ p := by
  
  
  rcases  BetheAnsatz.betheAnsatz_all hc p (fun j => hp.1 j)
            (cor34_S_n_injective hp) (by
                                        rw [hΔ]
                                        exact cor34_discreteBetheEquation_to_betheEquations p hBE)  with ⟨hnonzero, hfull⟩ | ⟨l, hl, hfull⟩
  · 
    exact cor34_final_restrict_full_eigen (by
                                               simpa only [hΔ] using hfull)
  · exact (cor34_even_S_n_roots_nonzero hp hn l hl).elim

/-- On the odd branch, the centered momentum is zero and injectivity identifies the
Theorem 3.1 eigenvalue with its derivative-corrected zero-root expression. -/
theorem cor34_final_odd_block_eigen {N n q : ℕ} {c Δ : ℝ}
    (hc : 2 < c) (hΔ : BetheAnsatz.anisotropy c = Δ)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q)
    (hBE : Bethe.DiscreteBetheEquation Δ N n p) :
    (transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.blockWave Δ p =
      BetheAnsatz.eigenvalueZero N c p (⟨q - 1, by omega⟩ : Fin n) •
        BetheAnsatz.blockWave Δ p := by
  have hcenter  :=
    cor34_odd_S_n_center_zero hp hnq
  
  
  rcases  BetheAnsatz.betheAnsatz_all hc p (fun j => hp.1 j)
            (cor34_S_n_injective hp) (by
                                        rw [hΔ]
                                        exact cor34_discreteBetheEquation_to_betheEquations p hBE)  with ⟨hnonzero, hfull⟩ | ⟨l, hl, hfull⟩
  · simp_all
  · have hl'  :=
      (cor34_S_n_injective hp) (hl.trans hcenter.symm)
    subst l
    
    exact cor34_final_restrict_full_eigen (by
                                               simpa only [hΔ] using hfull)

end PottsDiscontinuity.SixVertex
