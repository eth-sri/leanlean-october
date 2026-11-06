module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BethePF
public import PottsDiscontinuity.SixVertex.Cor34FinalEigen

/-! # Corollary 3.4: normalize Theorem 3.1 for the infinite-anisotropy branch -/

@[expose] public section

open Matrix


namespace PottsDiscontinuity.SixVertex

section

variable {N n : ℕ} {ε : ℝ} (hε : ε < 0)
include hε

private theorem cor34_final_normalizedTransferBlock_scale  :
    cor34_normalizedTransferBlock N n ε =
      (-ε / 2) ^ n • transferBlock N (Real.sqrt (2 - 2 / ε)) n := by
  rw [cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε]
  have hbase :  (-2 / ε )⁻¹  = -ε / 2 := by
    field_simp 
  
  rw [(by
         rw [← inv_pow, hbase] : ((-2 / ε ) ^ n)⁻¹ = (-ε / 2) ^ n)]

private theorem cor34_final_normalizedBlockWave_scale  (p : Fin n → ℝ) :
    cor34_normalizedBlockWave (N := N) ε p =
       ((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n  •
        BetheAnsatz.blockWave (N := N) (1 / ε) p := by
  funext x
  change cor34_normalizedCoordinate ε p (BetheAnsatz.positions x) = _
  rw [cor34_normalizedCoordinate_eq_scaled_coordinateWave ε p
    (BetheAnsatz.positions x) (ne_of_lt hε)]
  rfl

end

theorem cor34_final_normalizedRegularEigenvalue_scale {n : ℕ} {ε : ℝ}
    (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedRegularEigenvalue ε p =
       ((-ε / 2 : ℝ) : ℂ) ^ n  *
        BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) p := cor34_normalizedRegularEigenvalue_scale ε hε p



theorem cor34_final_normalizedZeroEigenvalue_scale {N n : ℕ} (l : Fin n)
    {ε : ℝ} (hInv : 1 / ε < -1) (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedZeroEigenvalue (N := N) ε p l =
       ((-ε / 2 : ℝ) : ℂ) ^ n  *
        BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) p l := by
  apply cor34_normalizedZeroEigenvalue_scale l ε ?_ hε p
  have heq : ε * (1 / ε) = 1 := by field_simp [ne_of_lt hε]
  nlinarith 

private theorem cor34_final_scale_eigen_equation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {v : ι → ℂ} {μ a b : ℂ}
    (hEig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (a • A.map (algebraMap ℝ ℂ)) *ᵥ  b • v  = (a * μ) •  b • v  := by
  ext i
  have hi := congrFun hEig i
  
  have hi' :  ∑ j, (A i j : ℂ) * v j  = μ * v i := hi
  calc
     ∑ j,  a * A i j  * (b * v j)  =
        a * b * ∑ j, A i j * v j := by
          calc
            _ = ∑ j,  a * b  * (A i j * v j) := by
              grind
            _ = _ := by rw [Finset.mul_sum]
    _ = a * b * (μ * v i) := by rw [hi']
    _ =  a * μ  * (b * v i) := by ring

/-- The normalized even-branch coordinate wave satisfies the normalized block eigen-equation
at every physical parameter. -/
theorem cor34_final_even_normalized_eigen {N n : ℕ} {ε : ℝ}
    (hε : ε < 0) (hInv : 1 / ε < -1)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hn : Even n)
    (hBE : Bethe.DiscreteBetheEquation (1 / ε) N n p) :
    (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
        cor34_normalizedBlockWave ε p =
      cor34_normalizedRegularEigenvalue ε p • cor34_normalizedBlockWave ε p := by
  let c  := Real.sqrt (2 - 2 / ε)
  have hcSq : c ^ 2 = 2 - 2 / ε := by
    grind
  have hc : 2 < c := by
    have hconv : 2 / ε = 2 * (1 / ε) := by ring
     
    have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith )
    nlinarith 
  
  have hraw := cor34_final_even_block_eigen hc (by
                                                  grind [BetheAnsatz.anisotropy]) p hp hn hBE
  have hmatrixR := cor34_final_normalizedTransferBlock_scale (N := N) (n := n) hε
  
  
  rw [(by
         
         
         all_goals aesop :
      (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) =
         ((-ε / 2 : ℝ) : ℂ) ^ n  •
          (transferBlock N c n).map (algebraMap ℝ ℂ)),  cor34_final_normalizedBlockWave_scale (N := N) (n := n) hε p ]
  
  rw [ cor34_final_normalizedRegularEigenvalue_scale hε p ]
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
  let c  := Real.sqrt (2 - 2 / ε)
  have hcSq : c ^ 2 = 2 - 2 / ε := by
    grind
  have hc : 2 < c := by
    have hconv : 2 / ε = 2 * (1 / ε) := by ring
     
    have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith )
    nlinarith 
  
  have hraw := cor34_final_odd_block_eigen hc (by
                                                 grind [BetheAnsatz.anisotropy]) p hp hnq hBE
  have hmatrixR := cor34_final_normalizedTransferBlock_scale (N := N) (n := n) hε
  
  
  rw [(by
         
         
         all_goals aesop :
      (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) =
         ((-ε / 2 : ℝ) : ℂ) ^ n  •
          (transferBlock N c n).map (algebraMap ℝ ℂ)),  cor34_final_normalizedBlockWave_scale (N := N) (n := n) hε p ]
  
  rw [ cor34_final_normalizedZeroEigenvalue_scale
         (N := N) (n := n)  ⟨q - 1, by omega⟩  hInv hε p ]
  exact cor34_final_scale_eigen_equation hraw

end PottsDiscontinuity.SixVertex
