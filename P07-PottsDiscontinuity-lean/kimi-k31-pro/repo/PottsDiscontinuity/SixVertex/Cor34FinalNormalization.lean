module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BethePF
public import PottsDiscontinuity.SixVertex.Cor34FinalEigen

/-! # Corollary 3.4: normalize Theorem 3.1 for the infinite-anisotropy branch -/

@[expose] public section

open Matrix
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

private theorem cor34_final_normalizedTransferBlock_scale {N n : ℕ} {ε : ℝ}
    (hε : ε < 0) :
    cor34_normalizedTransferBlock N n ε =
      (-ε / 2) ^ n • transferBlock N (Real.sqrt (2 - 2 / ε)) n := by
  rw [cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε]
  have hbase : ((-2 / ε : ℝ)⁻¹) = -ε / 2 := by
    field
  have hpow : ((-2 / ε : ℝ) ^ n)⁻¹ = (-ε / 2) ^ n := by
    rw [← inv_pow, hbase]
  rw [hpow]

private theorem cor34_final_normalizedBlockWave_scale {N n : ℕ} {ε : ℝ}
    (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedBlockWave (N := N) ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n) •
        BetheAnsatz.blockWave (N := N) (1 / ε) p := by
  funext x
  change cor34_normalizedCoordinate ε p (BetheAnsatz.positions x) = _
  rw [cor34_normalizedCoordinate_eq_scaled_coordinateWave ε p
    (BetheAnsatz.positions x) (ne_of_lt hε)]
  rfl

theorem cor34_final_normalizedRegularEigenvalue_scale {n : ℕ} {ε : ℝ}
    (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedRegularEigenvalue ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) p :=
  cor34_normalizedRegularEigenvalue_scale ε hε p


theorem cor34_final_normalizedZeroEigenvalue_scale {N n : ℕ} (l : Fin n)
    {ε : ℝ} (hInv : 1 / ε < -1) (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedZeroEigenvalue (N := N) ε p l =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) p l := by
  have hεlo : -1 < ε := by
    have h := (div_lt_iff_of_neg hε).1 hInv
    nlinarith
  exact cor34_normalizedZeroEigenvalue_scale l ε hεlo hε p

private theorem cor34_final_scale_eigen_equation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {v : ι → ℂ} {μ a b : ℂ}
    (hEig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (a • A.map (algebraMap ℝ ℂ)) *ᵥ (b • v) = (a * μ) • (b • v) := by
  ext i
  have hi := congrFun hEig i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi ⊢
  have hi' : (∑ j, (A i j : ℂ) * v j) = μ * v i := by
    assumption
  calc
    (∑ j, (a * A i j) * (b * v j)) =
        a * b * ∑ j, A i j * v j := by
          calc
            _ = ∑ j, (a * b) * (A i j * v j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = _ := by rw [Finset.mul_sum]
    _ = a * b * (μ * v i) := by rw [hi']
    _ = (a * μ) * (b * v i) := by ring

/-- The normalized even-branch coordinate wave satisfies the normalized block eigen-equation
at every physical parameter. -/
theorem cor34_final_even_normalized_eigen {N n : ℕ} {ε : ℝ}
    (hε : ε < 0) (hInv : 1 / ε < -1)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hn : Even n)
    (hBE : Bethe.DiscreteBetheEquation (1 / ε) N n p) :
    (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
        cor34_normalizedBlockWave ε p =
      cor34_normalizedRegularEigenvalue ε p • cor34_normalizedBlockWave ε p := by
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hcSq : c ^ 2 = 2 - 2 / ε := by
    dsimp [c]
    have hdiv : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
    exact Real.sq_sqrt (by linarith)
  have hc : 2 < c := by
    have hconv : 2 / ε = 2 * (1 / ε) := by ring
    have hparam : 4 < 2 - 2 / ε := by rw [hconv]; nlinarith [hInv]
    have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith [hparam])
    nlinarith [hcSq, hparam]
  have hAni : BetheAnsatz.anisotropy c = 1 / ε := by
    unfold BetheAnsatz.anisotropy
    rw [hcSq]
    ring
  have hraw := cor34_final_even_block_eigen hc hAni p hp hn hBE
  have hmatrixR := cor34_final_normalizedTransferBlock_scale (N := N) (n := n) hε
  have hmatrixC :
      (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) =
        (((-ε / 2 : ℝ) : ℂ) ^ n) •
          (transferBlock N c n).map (algebraMap ℝ ℂ) := by
    rw [hmatrixR]
    ext x y
    simp [c, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hwave := cor34_final_normalizedBlockWave_scale (N := N) (n := n) hε p
  rw [hmatrixC, hwave]
  have hscale := cor34_final_normalizedRegularEigenvalue_scale hε p
  rw [hscale]
  exact cor34_final_scale_eigen_equation hraw

/-- The normalized odd zero-root coordinate wave satisfies the normalized block
eigen-equation at every physical parameter. -/
theorem cor34_final_odd_normalized_eigen {N n q : ℕ} {ε : ℝ}
    (hε : ε < 0) (hInv : 1 / ε < -1)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q)
    (hBE : Bethe.DiscreteBetheEquation (1 / ε) N n p) :
    (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
        cor34_normalizedBlockWave ε p =
      cor34_normalizedZeroEigenvalue (N := N) ε p
          (⟨q - 1, by omega⟩ : Fin n) • cor34_normalizedBlockWave ε p := by
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hcSq : c ^ 2 = 2 - 2 / ε := by
    dsimp [c]
    have hdiv : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
    exact Real.sq_sqrt (by linarith)
  have hc : 2 < c := by
    have hconv : 2 / ε = 2 * (1 / ε) := by ring
    have hparam : 4 < 2 - 2 / ε := by rw [hconv]; nlinarith [hInv]
    have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith [hparam])
    nlinarith [hcSq, hparam]
  have hAni : BetheAnsatz.anisotropy c = 1 / ε := by
    unfold BetheAnsatz.anisotropy
    rw [hcSq]
    ring
  have hraw := cor34_final_odd_block_eigen hc hAni p hp hnq hBE
  have hmatrixR := cor34_final_normalizedTransferBlock_scale (N := N) (n := n) hε
  have hmatrixC :
      (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) =
        (((-ε / 2 : ℝ) : ℂ) ^ n) •
          (transferBlock N c n).map (algebraMap ℝ ℂ) := by
    rw [hmatrixR]
    ext x y
    simp [c, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hwave := cor34_final_normalizedBlockWave_scale (N := N) (n := n) hε p
  rw [hmatrixC, hwave]
  have hscale := cor34_final_normalizedZeroEigenvalue_scale
    (N := N) (n := n) (⟨q - 1, by omega⟩ : Fin n) hInv hε p
  rw [hscale]
  exact cor34_final_scale_eigen_equation hraw

end PottsDiscontinuity.SixVertex
