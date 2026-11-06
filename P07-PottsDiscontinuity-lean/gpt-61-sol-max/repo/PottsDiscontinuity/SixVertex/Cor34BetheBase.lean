module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteBase
public import PottsDiscontinuity.SixVertex.Cor34BetheWave

/-!
# Corollary 3.4: Bethe wave and eigenvalue at infinity

This module specializes the continuous regularizations to the discrete base momentum family.
The parameter `ε` is `1/Δ`; the displayed source limit is always the limit as `ε → 0` from
below when it is interpreted with `Δ < 0`.
-/

@[expose] public section

open Finset Complex Filter Matrix Topology


namespace PottsDiscontinuity.SixVertex

/-- The determinant whose Leibniz expansion is the normalized Bethe coordinate at
`(2,4,...,2n)`. Rows label the momenta and columns label source positions. -/
noncomputable def cor34_baseCoordinateMatrix {N n : ℕ} :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => BetheAnsatz.z (Bethe.discreteBaseSolution N n i) ^ (n + j.val + 1)

/-- The half-angle root whose square is the source's `ζ=e^(2πi/(N-n))`. -/
noncomputable def cor34_halfRoot (m : ℕ)  :=
  Complex.exp (Real.pi * I / (m : ℂ))

/-- The discrete base momentum phase is the centered half-root power, including the even
particle-number half-integer shift. -/
theorem cor34_base_z_eq_halfRoot_zpow {N n : ℕ} (hnN : n < N) (j : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) =
      cor34_halfRoot (N - n) ^ (2 * (j.val : ℤ) + 1 - (n : ℤ)) := by
  
  
  have hp : Bethe.discreteBaseSolution N n j =
      Real.pi *  (2 *  j.val  + 1 -  n  )  /
         (N - n : ℕ)  := by
    dsimp [Bethe.discreteBaseSolution, Bethe.discreteBetheIndex]
    push_cast
    
    ring
  have harg : I *  Bethe.discreteBaseSolution N n j  =
       (2 *  j.val  + 1 -  n  : ℤ)  *
        (Real.pi * I /  (N - n : ℕ) ) := by
    simp_all <;> grind
  unfold BetheAnsatz.z cor34_halfRoot
  rw [harg, Complex.exp_int_mul]

private theorem cor34_z_nat_power (x : ℝ) (k : ℕ) :
    Complex.exp (I * (x : ℂ) * (k : ℂ)) = BetheAnsatz.z x ^ k := by
  rw [BetheAnsatz.z, ← Complex.exp_nat_mul]
  
  ring

/-- The limiting normalized coordinate at the source tuple is a determinant. -/
theorem cor34_coordinate_infinity_eq_det {N n : ℕ} :
    cor34_normalizedCoordinate 0 (Bethe.discreteBaseSolution N n)
      cor34_sourceEvenPositions = (cor34_baseCoordinateMatrix (N := N) (n := n)).det := by
  
  let z  := fun j => BetheAnsatz.z (Bethe.discreteBaseSolution N n j)
  have hcoef (σ : Equiv.Perm (Fin n)) :
       ∏ k : Fin n, ∏ l ∈ Finset.Ioi k, z (σ k)  =
        ∏ k : Fin n, z (σ k) ^ (n - 1 - k.val) := by
    simp_all
  have hplane (σ : Equiv.Perm (Fin n)) :
      BetheAnsatz.planeWave (Bethe.discreteBaseSolution N n) σ
          cor34_sourceEvenPositions =
        ∏ k : Fin n, z (σ k) ^ (2 * (k.val + 1)) := by
                                                      solve_by_elim [_root_.Finset.prod_congr, _root_.rfl, _root_.PottsDiscontinuity.SixVertex.cor34_z_nat_power]
  have hterm (σ : Equiv.Perm (Fin n)) :
      cor34_normalizedAmplitude 0 (Bethe.discreteBaseSolution N n) σ *
          BetheAnsatz.planeWave (Bethe.discreteBaseSolution N n) σ
            cor34_sourceEvenPositions =
         Equiv.Perm.sign σ  *
          ∏ k : Fin n, z (σ k) ^ (n + k.val + 1) := by
    rw [cor34_normalizedAmplitude_zero, hcoef, hplane]
    have hprod :
        (∏ k : Fin n, z (σ k) ^ (n - 1 - k.val)) *
          ∏ k : Fin n, z (σ k) ^ (2 * (k.val + 1)) =
        ∏ k : Fin n, z (σ k) ^ (n + k.val + 1) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro k hk
      rw [← pow_add]
      congr 1
      omega
    calc
      (  Equiv.Perm.sign σ   *
          ∏ k : Fin n, z (σ k) ^ (n - 1 - k.val)) *
          ∏ k : Fin n, z (σ k) ^ (2 * (k.val + 1)) =
          Equiv.Perm.sign σ   *
          ((∏ k : Fin n, z (σ k) ^ (n - 1 - k.val)) *
            ∏ k : Fin n, z (σ k) ^ (2 * (k.val + 1))) := by ring
      _ =   Equiv.Perm.sign σ   *
          ∏ k : Fin n, z (σ k) ^ (n + k.val + 1) := by rw [hprod]
  rw [Matrix.det_apply' (cor34_baseCoordinateMatrix (N := N) (n := n))]
  unfold cor34_normalizedCoordinate
  apply Finset.sum_congr rfl
  intro σ hσ
  simpa [cor34_baseCoordinateMatrix, z] using hterm σ

/-- The determinant at the source coordinate is a nonzero Vandermonde: the base momenta are
strictly ordered in `(-π,π)`, so their phases are distinct. -/
theorem cor34_coordinate_infinity_nonzero {N n : ℕ}
    (hN : 0 < N) (hn : 2 * n ≤ N) :
    cor34_normalizedCoordinate 0 (Bethe.discreteBaseSolution N n)
      cor34_sourceEvenPositions ≠ 0 := by
  
  let z  := fun j => BetheAnsatz.z (Bethe.discreteBaseSolution N n j)
  have hpS := Bethe.discreteBaseSolution_mem_S_n hN hn
  
  
  rw [cor34_coordinate_infinity_eq_det, (by
                                           ext i j
                                           simp [cor34_baseCoordinateMatrix, Matrix.mul_apply, Matrix.diagonal]; ring : cor34_baseCoordinateMatrix (N := N) (n := n) =
      Matrix.diagonal (fun i  => z i ^ (n + 1)) * Matrix.vandermonde z), Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (BetheAnsatz.z_ne_zero _)
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr (by
                                                    intro i j hij
                                                    have hi := hpS.1 i
                                                    have hj := hpS.1 j
                                                    
                                                    have hargs := Complex.exp_inj_of_neg_pi_lt_of_le_pi
                                                      (by simpa using hi.1) (by simpa using hi.2.le)
                                                      (by simpa using hj.1) (by simpa using hj.2.le)  hij 
                                                    
                                                    exact hpS.2.1.injective (by
                                                                               simp_all))

/-- A continuous normalized Bethe wave is nonzero near `ε=0`, because its source coordinate has
the nonzero Vandermonde limit. -/
theorem cor34_eventually_normalizedCoordinate_ne_zero {N n : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hn : 2 * n ≤ N) :
    ∀ᶠ ε in 𝓝 0,
      cor34_normalizedCoordinate ε (p ε) cor34_sourceEvenPositions ≠ 0 := by
  
  
  
  exact (cor34_normalizedCoordinate_tendsto hp cor34_sourceEvenPositions).eventually_ne (by
                              grind [cor34_coordinate_infinity_eq_det, cor34_coordinate_infinity_nonzero])

end PottsDiscontinuity.SixVertex
