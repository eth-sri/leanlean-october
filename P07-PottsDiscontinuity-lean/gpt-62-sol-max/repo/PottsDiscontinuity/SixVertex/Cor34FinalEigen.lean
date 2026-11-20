module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.ZeroRootTheorem
public import PottsDiscontinuity.BetheAnsatz.Parity
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
  classical
  ext x
  have hx := congrFun hfull x.1
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun y : Finset (Fin N) => y.card = n)
    (fun y => ((transferMatrix N c).map (algebraMap ℝ ℂ)) x.1 y *
      BetheAnsatz.betheVector Δ p y)
  have hcompl :
      (∑ y : {y : Finset (Fin N) // y.card ≠ n},
        ((transferMatrix N c).map (algebraMap ℝ ℂ)) x.1 y.1 *
          BetheAnsatz.betheVector Δ p y.1) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    simp [BetheAnsatz.betheVector_eq_zero Δ p y.2]
  have hrestr :
      (∑ y : State N n,
        ((transferMatrix N c).map (algebraMap ℝ ℂ)) x.1 y.1 *
          BetheAnsatz.betheVector Δ p y.1) =
      ∑ y : State N n,
        ((transferBlock N c n).map (algebraMap ℝ ℂ)) x y *
          BetheAnsatz.blockWave Δ p y := by
    apply Finset.sum_congr rfl
    intro y hy
    simp [transferBlock, BetheAnsatz.betheVector]
  rw [← hsplit, hcompl, add_zero, hrestr] at hx
  simpa [BetheAnsatz.betheVector, Matrix.mulVec, dotProduct] using hx

/-- On a symmetric tuple only an odd-sized sector has a zero root. -/
theorem cor34_parity_block_eigen {N n : ℕ} {c Δ : ℝ}
    (hc : 2 < c) (hΔ : BetheAnsatz.anisotropy c = Δ)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hBE : Bethe.DiscreteBetheEquation Δ N n p) :
    (transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ BetheAnsatz.blockWave Δ p =
      Bethe.parityEigenvalue N c p • BetheAnsatz.blockWave Δ p := by
  have hBA := cor34_discreteBetheEquation_to_betheEquations p hBE
  rw [← hΔ] at hBA
  have hinj := hp.2.1.injective
  have hbranch := BetheAnsatz.betheAnsatz_all hc p hp.1 hinj hBA
  rw [hΔ] at hbranch
  unfold Bethe.parityEigenvalue
  by_cases he : Even n
  · rw [dite_eq_left he]
    rcases hbranch with ⟨_, h⟩ | ⟨l, hl, _⟩
    · exact cor34_final_restrict_full_eigen h
    · exact (cor34_even_S_n_roots_nonzero hp he l hl).elim
  · rw [dite_eq_right he]
    have hz :=
      cor34_odd_S_n_center_zero (q := n / 2 + 1) hp (by rw [Nat.even_iff] at he; omega)
    rcases hbranch with ⟨h, _⟩ | ⟨l, hl, h⟩
    · exact (h _ hz).elim
    · obtain rfl : l = Bethe.oddCenter he := hinj (hl.trans hz.symm)
      exact cor34_final_restrict_full_eigen h

end PottsDiscontinuity.SixVertex
