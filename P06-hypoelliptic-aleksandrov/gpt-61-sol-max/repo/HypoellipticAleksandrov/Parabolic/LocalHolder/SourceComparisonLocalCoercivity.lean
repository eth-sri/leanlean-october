module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Coercivity of the local value-energy flux

A scalar Young inequality absorbs the coefficient and cutoff error row into half of
the elliptic gradient energy, leaving only a multiple of the squared solution value.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Matrix
open scoped BigOperators MatrixOrder

private theorem error_row_young (lam a b : ℝ) (hlam : 0 < lam) :
    -(lam / 2) * b ^ 2 ≤ a * b + a ^ 2 / (2 * lam) := by
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * lam by positivity)).mp

  field_simp
  nlinarith only [(sq_nonneg (lam * b + a))]

variable {d : ℕ}

/-- A bounded error row is absorbed into half of the weighted elliptic energy. -/
theorem local_value_energy_flux_coercivity
    (lam ρ q K : ℝ) (hlam : 0 < lam) (hK : 0 ≤ K)
    (A : PDE.Mat d) (G B : PDE.Vec d)
    (hA : lam • (1 : PDE.Mat d) ≤ A) (hB : ∀ j, |B j| ≤ K) :
    (lam / 2) * ρ ^ 2 * (∑ j, G j ^ 2) ≤
      ρ ^ 2 * (∑ i, ∑ j, A i j * G j * G i) +
        q * ρ * (∑ j, B j * G j) + (d : ℝ) * K ^ 2 * q ^ 2 / (2 * lam) := by
  have hquad := mul_le_mul_of_nonneg_left (vecDot_mulVec_lower_of_loewner hA G)
    (sq_nonneg ρ)
  have hprincipal : lam * ρ ^ 2 * (∑ j, G j ^ 2) ≤
      ρ ^ 2 * (∑ i, ∑ j, A i j * G j * G i) := by
    have hl : ρ ^ 2 * (lam * PDE.vecNormSq G) = lam * ρ ^ 2 * (∑ j, G j ^ 2) := by
      unfold PDE.vecNormSq PDE.vecDot
      simp only [← pow_two]
      ring
    have hr : ρ ^ 2 * PDE.vecDot G (A *ᵥ G) =
        ρ ^ 2 * (∑ i, ∑ j, A i j * G j * G i) := by
      simp only [PDE.vecDot, Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hl, hr] at hquad
    exact hquad
  have hentry (j : Fin d) : -(lam / 2) * ρ ^ 2 * G j ^ 2 ≤
      q * ρ * (B j * G j) + K ^ 2 * q ^ 2 / (2 * lam) := by




    exact (show -(lam / 2) * ρ ^ 2 * G j ^ 2 ≤
        q * ρ * (B j * G j) + (q * B j) ^ 2 / (2 * lam) by
        convert (error_row_young lam (q * B j) (ρ * G j) hlam) using 1 <;> ring).trans (add_le_add le_rfl (by
        apply div_le_div_of_nonneg_right ?_ (by positivity)
        calc
          _ = q ^ 2 * B j ^ 2 := mul_pow _ _ _
          _ ≤ q ^ 2 * K ^ 2 := mul_le_mul_of_nonneg_left (by
              simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 (hB j)) (sq_nonneg q)
          _ = _ := mul_comm _ _))

  have herror : -(lam / 2) * ρ ^ 2 * (∑ j, G j ^ 2) ≤
      q * ρ * (∑ j, B j * G j) + (d : ℝ) * K ^ 2 * q ^ 2 / (2 * lam) := by
    convert (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hentry j)) using 1 <;>
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc,
      mul_assoc]
    ring
  linarith only [hprincipal, herror]

/-- The expanded cutoff flux has its exact principal-plus-error-row decomposition. -/
theorem local_value_energy_flux_eq  (ρ q : ℝ)
    (A D : PDE.Mat d) (G R : PDE.Vec d) :
    (∑ i, ∑ j, (A i j * G j * (ρ ^ 2 * G i + 2 * ρ * R i * q) +
      D i j * G j * q * ρ ^ 2)) =
      ρ ^ 2 * (∑ i, ∑ j, A i j * G j * G i) +
        q * ρ * (∑ j, (∑ i, (2 * A i j * R i + ρ * D i j)) * G j) := by
  have hrow : (∑ j, (∑ i, (2 * A i j * R i + ρ * D i j)) * G j) =
      ∑ i, ∑ j, (2 * A i j * R i + ρ * D i j) * G j := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  rw [hrow]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end HypoellipticAleksandrov.Parabolic.LocalHolder
