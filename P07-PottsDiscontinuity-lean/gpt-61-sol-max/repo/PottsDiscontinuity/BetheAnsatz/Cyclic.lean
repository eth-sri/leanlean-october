module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.Scattering

/-!
# Cyclic permutation of the coordinate Bethe amplitudes

Companion paper, Lemma `lem:ratios`, equation (11). The cyclic permutation is
`finRotate`: it sends the last index to zero and each other index to its successor.
-/

@[expose] public section

open Finset Complex

namespace PottsDiscontinuity.BetheAnsatz

section

variable (n : ℕ) (f : Fin (n + 1) → Fin (n + 1) → ℂ)


private theorem pair_product_succ  :
     ∏ i, ∏ j ∈ Ioi i, f i j  =
      (∏ j : Fin n, f 0 j.succ) *  ∏ i : Fin n, ∏ j ∈ Ioi i, f i.succ j.succ  := by
  rw [Fin.prod_univ_succ]
  simp_all

private theorem pair_product_last  :
     ∏ i, ∏ j ∈ Ioi i, f i j  =
      (∏ i : Fin n, ∏ j ∈ Ioi i, f i.castSucc j.castSucc) *
         ∏ i : Fin n, f i.castSucc (Fin.last n)  := by
  have hi : ∀ i : Fin n,  ∏ j ∈ Ioi i.castSucc, f i.castSucc j  =
      (∏ j ∈ Ioi i, f i.castSucc j.castSucc) * f i.castSucc (Fin.last n) := by
    intro i
    rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter, Fin.prod_univ_castSucc]
    simp only [Fin.castSucc_lt_last, ↓reduceIte, Fin.castSucc_lt_castSucc_iff]
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  have hl : Ioi (Fin.last n) = ∅ := by
    grind
  rw [Fin.prod_univ_castSucc]
  simp only [hl, Finset.prod_empty, mul_one]
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]

/-- Moving the first index to the end reverses exactly its pair factors. -/
theorem pair_product_rotate  :
    (∏ i, ∏ j ∈ Ioi i, f (finRotate (n + 1) i) (finRotate (n + 1) j)) *
       ∏ j : Fin n, f 0 j.succ  =
      (∏ i, ∏ j ∈ Ioi i, f i j) *  ∏ j : Fin n, f j.succ 0  := by
  have hr : ∀ i : Fin n, finRotate (n + 1) i.castSucc = i.succ := fun i =>
    finRotate_of_lt i.isLt
  rw [pair_product_last, pair_product_succ]
  simp_rw [hr, finRotate_last]
  ring

end

/-- Cyclic amplitude relation before imposing BE. The phase sum is over all root labels. -/
theorem amplitude_rotate_phase {n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) :
    amplitude Δ p (σ * finRotate (n + 1)) =
      (-1 : ℂ) ^ n * Complex.exp (I * ((∑ k, Bethe.theta Δ (p (σ 0)) (p k) : ℝ) : ℂ)) *
        amplitude Δ p σ := by
  let f  := fun i j =>
    z (p (σ i)) * scattering Δ (p (σ i)) (p (σ j))
  let U := ∏ j : Fin n, f 0 j.succ
  let V := ∏ j : Fin n, f j.succ 0
  have hU : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ =>
    mul_ne_zero (z_ne_zero _) (scattering_ne_zero hΔ _ _)
  have hs :  ∑ j : Fin n, Bethe.theta Δ (p (σ 0)) (p (σ j.succ))  =
      ∑ k, Bethe.theta Δ (p (σ 0)) (p k) := by
    calc
      _ = ∑ j : Fin (n + 1), Bethe.theta Δ (p (σ 0)) (p (σ j)) := by
        rw [Fin.sum_univ_succ, Bethe.theta_self, zero_add]
      _ = _ := Equiv.sum_comp σ  fun k => Bethe.theta Δ (p (σ 0)) (p k) 
  have he : Complex.exp (I *   ∑ k, Bethe.theta Δ (p (σ 0)) (p k)  ) = V / U := by
    rw [← hs]
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    simp_rw [exp_I_theta_eq_scattering hΔ]
    rw [Finset.prod_div_distrib]
  have hsign :   Equiv.Perm.sign (σ * finRotate (n + 1))   =
        Equiv.Perm.sign σ   * (-1 : ℂ) ^ n := by
    simp 
  
  apply mul_right_cancel₀ hU
  rw [he]
  calc
    amplitude Δ p (σ * finRotate (n + 1)) * U = (-1 ) ^ n * amplitude Δ p σ * V := (by
                                                                                      have hp := pair_product_rotate n f
                                                                                      unfold amplitude
                                                                                      rw [hsign]
                                                                                      change    ((Equiv.Perm.sign σ ) )  * (-1 ) ^ n  *
                                                                                        (∏ i, ∏ j ∈ Ioi i, f (finRotate (n + 1) i) (finRotate (n + 1) j))  * U =
                                                                                        (-1 ) ^ n * ( ((Equiv.Perm.sign σ ) )  *  ∏ i, ∏ j ∈ Ioi i, f i j ) * V
                                                                                      grind)
    _ =  (-1 ) ^ n * (V / U) * amplitude Δ p σ  * U := by field_simp

/-- The cyclic amplitude relation from BE, valid also for one particle. -/
theorem amplitude_rotate {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N Δ p)
    (σ : Equiv.Perm (Fin (n + 1))) :
    amplitude Δ p (σ * finRotate (n + 1)) =
      (z (p (σ 0)) ^ N)⁻¹ * amplitude Δ p σ := by
  have hp : z (p (σ 0)) ^ N = (-1 ) ^ n *
      Complex.exp (-(I *   ∑ k, Bethe.theta Δ (p (σ 0)) (p k)  )) := by
    calc
      _ = Complex.exp (I *  N  *  p (σ 0) ) := by
        rw [z, ← Complex.exp_nat_mul]
        
        ring
      _ = _ := by bound
  have hi := congrArg (fun w  => w⁻¹) hp
  simp only [mul_inv_rev, Complex.exp_neg, inv_inv] at hi
  
  rw [(by
         rw [← inv_pow]
         norm_num : ((-1 ) ^ n)⁻¹ = (-1 : ℂ) ^ n)] at hi
  have he : (-1 ) ^ n *
      Complex.exp (I *   ∑ k, Bethe.theta Δ (p (σ 0)) (p k)  ) =
      (z (p (σ 0)) ^ N)⁻¹ := by simpa only [mul_comm] using hi.symm
  rw [amplitude_rotate_phase hΔ p σ, he]

end PottsDiscontinuity.BetheAnsatz
