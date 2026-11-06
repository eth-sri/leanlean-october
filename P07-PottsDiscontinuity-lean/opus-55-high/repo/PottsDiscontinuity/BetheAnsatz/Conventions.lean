module

public import PottsDiscontinuity.BetheAnsatz.Defs
public import PottsDiscontinuity.SixVertex.TransferMatrix

/-!
# Coordinates, nonzero amplitudes, and the full-matrix/block bridge

The paper's positions `1,...,N` are our increasing `Fin N` positions plus one.
The resulting uniform phase is exactly `exp(i ∑j p_j)`, independently of the state.
The block-extension identity below is linear algebra for arbitrary vectors; it does not
assert the Bethe Ansatz for an unproved particle sector.
-/

public section

open Finset Complex Matrix

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

section
variable {n : ℕ} (p : Fin n → ℝ)
theorem planeWave_add_one (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℤ) :
    planeWave p σ (fun k => x k + 1) = (∏ j, z (p j)) * planeWave p σ x := by
  have h : ∀ k, Complex.exp (I * (p (σ k) : ℂ) * ((x k + 1 : ℤ) : ℂ)) =
      z (p (σ k)) * Complex.exp (I * (p (σ k) : ℂ) * (x k : ℂ)) := by
    intro k
    rw [z, ← Complex.exp_add]
    congr 1
    grind
  unfold planeWave
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun j => z (p j))]

theorem prod_z_eq_exp_sum  :
    (∏ j, z (p j)) = Complex.exp (I * ((∑ j, p j : ℝ) : ℂ)) := by
  simp only [z]
  rw [← Complex.exp_sum]
  push_cast
  rw [Finset.mul_sum]
end

section
variable {n : ℕ}
/-- Adding one to every coordinate multiplies the wave by `exp(i ∑j p_j)`.
This is the exact normalization relating zero-based and one-based positions. -/
theorem coordinateWave_add_one (Δ : ℝ) (p : Fin n → ℝ)
    (x : Fin n → ℤ) :
    coordinateWave Δ p (fun k => x k + 1) =
      Complex.exp (I * ((∑ j, p j : ℝ) : ℂ)) * coordinateWave Δ p x := by
  unfold coordinateWave
  simp_rw [planeWave_add_one]
  rw [← prod_z_eq_exp_sum, Finset.mul_sum]
  grind

end

/-- Evaluation of the full matrix on a zero-extended vector agrees with the block action. -/
theorem mulVec_extendByZero_apply {N n : ℕ} (c : ℝ) (v : State N n → ℂ)
    (x : State N n) :
    ((transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ extendByZero v) x.1 =
      ((transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ v) x := by
  apply Finset.sum_congr_set {y : Finset (Fin N) | y.card = n}
  · intro y hy
    change y.card = n at hy
    simp only [Matrix.map_apply, transferBlock_apply, extendByZero, hy, ↓reduceDIte]
  · simp_all

end PottsDiscontinuity.BetheAnsatz
