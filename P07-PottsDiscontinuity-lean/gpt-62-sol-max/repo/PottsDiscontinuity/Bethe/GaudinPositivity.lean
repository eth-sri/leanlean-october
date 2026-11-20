module

public import PottsDiscontinuity.Bethe.DiscreteJacobian
public import PottsDiscontinuity.Bethe.Theorem23Counting

/-! The odd part of the Poisson kernel is positive semidefinite. In rapidity
coordinates the symmetric Bethe Jacobian is its sum with the positive
counting-function diagonal, up to a positive column rescaling. -/

@[expose] public section

open Finset Matrix Set

namespace PottsDiscontinuity.Bethe

private noncomputable def oddXiMatrix {ι : Type*} (μ : ℝ) (a : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => Xi μ (a i - a j) - Xi μ (a i + a j)

private theorem hasSum_oddXi {μ : ℝ} (hμ : 0 < μ) (x y : ℝ) :
    HasSum (fun k : ℕ => 4 * Real.exp (-μ) ^ (k + 1) *
      Real.sin ((↑(k + 1) : ℝ) * x) * Real.sin ((↑(k + 1) : ℝ) * y))
      (Xi μ (x - y) - Xi μ (x + y)) := by
  convert (hasSum_Xi_cos hμ (x - y)).sub (hasSum_Xi_cos hμ (x + y)) using 1
  · ext k
    rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add]
    ring
  · ring

private theorem oddXiMatrix_posSemidef {ι : Type*} [Fintype ι] {μ : ℝ} (hμ : 0 < μ) (a : ι → ℝ) :
    (oddXiMatrix μ a).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · apply IsHermitian.ext
    intro i j
    simp only [oddXiMatrix, of_apply, star_trivial]
    rw [show a j - a i = -(a i - a j) by ring, add_comm (a j) (a i)]
    simp only [Xi, Real.cos_neg]
  · intro v
    let b (k : ℕ) (i : ι) := Real.sin ((↑(k + 1) : ℝ) * a i)
    let c (k : ℕ) := 4 * Real.exp (-μ) ^ (k + 1)
    have hi (i : ι) := (hasSum_sum (s := (univ : Finset ι))
      (fun j _ => (hasSum_oddXi hμ (a i) (a j)).mul_right (v j))).mul_left (v i)
    change 0 ≤ ∑ i, star (v i) * ∑ j, (Xi μ (a i - a j) - Xi μ (a i + a j)) * v j
    simp only [star_trivial]
    apply HasSum.nonneg _ (hasSum_sum (fun i _ => hi i))
    intro k
    change 0 ≤ ∑ i, v i * ∑ j, (c k * b k i * b k j) * v j
    have hid : (∑ i, v i * ∑ j, c k * b k i * b k j * v j) =
        c k * (∑ i, b k i * v i) ^ 2 := by
      calc
        _ = ∑ i, (c k * (b k i * v i)) * (∑ j, b k j * v j) := by
          simp_rw [mul_sum]
          exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
        _ = _ := by rw [← sum_mul, ← mul_sum, pow_two]; ring
    rw [hid]
    positivity

private theorem matrixA_counting {Δ : ℝ} {N n : ℕ} (p : Fin n → ℝ) (i j : Fin (n / 2)) :
    discreteBetheMatrixA Δ N n p i j =
      (if i = j then 2 * Real.pi * betheCountingDerivative Δ N n p (p (discreteHalfIndex n i)) else 0) +
      (thetaPartialSecond Δ (p (discreteHalfIndex n i)) (p (discreteHalfIndex n j)) -
        thetaPartialSecond Δ (p (discreteHalfIndex n i)) (p (Fin.rev (discreteHalfIndex n j)))) / N := by
  simp [discreteBetheMatrixA, betheCountingDerivative, thetaPartialFirst, d1Theta, mul_div_cancel₀]

/-- Positive density at the roots suffices for an invertible finite Jacobian. -/
theorem det_BetheMatrix_ne_zero_of_counting_pos {Δ : ℝ} (hΔ : Δ < -1) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (hpos : ∀ x ∈ Icc (-Real.pi) Real.pi, 0 < betheCountingDerivative Δ N n p x) :
    (discreteBetheMatrixA Δ N n p).det ≠ 0 := by
  let lam := lamOf Δ
  have hlam := lamOf_pos hΔ
  let r := discreteHalfIndex n
  have hex (i : Fin (n / 2)) : ∃ a, kMap lam a = p (r i) := by
    obtain ⟨a, _, ha⟩ := (bijOn_kMap hlam).surjOn (Ioo_subset_Icc_self (hp.1 (r i)))
    exact ⟨a, ha⟩
  choose a ha using hex
  let w := fun i => Xi lam (a i)
  let d := fun i => 2 * Real.pi * betheCountingDerivative Δ N n p (p (r i)) * w i
  have hw (i : Fin (n / 2)) : 0 < w i := Xi_pos hlam _
  have hD : (diagonal d).PosDef := .diagonal fun i =>
    mul_pos (mul_pos (by positivity) (hpos _ (Ioo_subset_Icc_self (hp.1 (r i))))) (hw i)
  have hl (i j : Fin (n / 2)) :
      thetaPartialSecond Δ (p (r i)) (p (r j)) = Xi (2 * lam) (a i - a j) / w j := by
    rw [← ha i, ← ha j]
    exact deriv_theta_right_kMap hlam (cosh_lamOf hΔ) _ _
  have hr (i j : Fin (n / 2)) :
      thetaPartialSecond Δ (p (r i)) (p (Fin.rev (r j))) = Xi (2 * lam) (a i + a j) / w j := by
    rw [hp.2.2 (r j), ← ha i, ← ha j, ← kMap_neg]
    simpa [thetaPartialSecond, w, Xi] using
          deriv_theta_right_kMap hlam (cosh_lamOf hΔ) (a i) (-a j)
  have hsym : discreteBetheMatrixA Δ N n p * diagonal w =
      diagonal d + (N : ℝ)⁻¹ • oddXiMatrix (2 * lam) a := by
    ext i j
    rw [mul_diagonal, matrixA_counting, hl i j, hr i j]
    by_cases h : i = j
    · subst j
      simp only [ite_true, diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, oddXiMatrix, of_apply, d, r]
      rw [add_mul, div_sub_div_same, div_right_comm, div_mul_cancel₀ _ (hw i).ne', div_eq_inv_mul]
    · simp only [h, ite_false, zero_add, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, oddXiMatrix, of_apply,
        diagonal_apply_ne _ h]
      rw [div_sub_div_same, div_right_comm, div_mul_cancel₀ _ (hw j).ne', div_eq_inv_mul]
  have hP := hD.add_posSemidef ((oddXiMatrix_posSemidef (by linarith : 0 < 2 * lam) a).smul
    (by positivity : 0 ≤ (N : ℝ)⁻¹))
  rw [← hsym] at hP
  have hd := hP.det_pos.ne'
  rw [det_mul] at hd
  exact (mul_ne_zero_iff.mp hd).1

end PottsDiscontinuity.Bethe
