module

public import PottsDiscontinuity.Bethe.Theorem23Counting
public import PottsDiscontinuity.Bethe.RatioProducts

/-! # The zero-root prefactor: positivity and its leading asymptotic

Source: Section 3.2 of arXiv:1611.09877v2, proof of (1.7) for odd `r`: the prefactor (A) of
`Λ_r(N) / Λ₀(N)` and its asymptotic `(A) = (c²/2) · 2πρ(0) N + o(N)`. The prefactor is a multiple
of the counting derivative at zero plus an explicit `O(1/N)` correction.
-/

@[expose] public section

open Set Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

/-- The full real coefficient of the erased product in the zero-root formula. -/
noncomputable def ratioZeroCoefficient {n : ℕ} (Δ c : ℝ) (N : ℕ)
    (q : Fin n → ℝ) (l : Fin n) : ℝ :=
  2 + c ^ 2 * ((N : ℝ) - 1) + c ^ 2 * ∑ j ∈ univ.erase l, d1Theta Δ 0 (q j)

theorem ratio_eigenvalueZero_eq_coefficient {N n : ℕ} {q : Fin n → ℝ}
    {c : ℝ} (hc : 2 < c) (hq : q ∈ S_n n) (l : Fin n) (hl : q l = 0) :
    BetheAnsatz.eigenvalueZero N c q l =
      ((ratioZeroCoefficient (BetheAnsatz.anisotropy c) c N q l *
        ∏ j ∈ univ.erase l, ‖BetheAnsatz.M c (BetheAnsatz.z (q j))‖ : ℝ) : ℂ) := ratio_eigenvalueZero hc hq l hl

/-- Exact source `(A)(B)` factorization, before any asymptotics. -/
theorem ratio_odd_eigenvalue_quotient {N m n : ℕ}
    {p : Fin m → ℝ} {q : Fin n → ℝ} {c : ℝ} (hc : 2 < c)
    (hp : p ∈ S_n m) (hq : q ∈ S_n n) (l : Fin n) (hl : q l = 0) :
    BetheAnsatz.eigenvalueZero N c q l / BetheAnsatz.eigenvalueRegular c p =
      (((ratioZeroCoefficient (BetheAnsatz.anisotropy c) c N q l / 2) *
        ((∏ j ∈ univ.erase l, ‖BetheAnsatz.M c (BetheAnsatz.z (q j))‖) /
          ∏ j, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖) : ℝ) : ℂ) := by
  rw [ratio_eigenvalueZero_eq_coefficient hc hq l hl, ratio_eigenvalueRegular hc hp]
  push_cast
  ring

/-- The normalized prefactor is determined by the density at the origin. -/
theorem ratio_odd_A_tendsto {ι : Type*} {f : Filter ι} {Δ : ℝ}
    (c : ℝ) (N n : ι → ℕ) (q : ∀ i, Fin (n i) → ℝ) (hN : ∀ i, 0 < N i)
    (hNlim : Tendsto (fun i => (N i : ℝ)) f atTop)
    (hD : Tendsto (fun i => betheCountingDerivative Δ (N i) (n i) (q i) 0) f (𝓝 (rho Δ 0)))
    (l : ∀ i, Fin (n i)) (hl : ∀ i, q i (l i) = 0) :
    Tendsto (fun i => ratioZeroCoefficient Δ c (N i) (q i) (l i) / (2 * N i)) f
      (𝓝 (c ^ 2 * Real.pi * rho Δ 0)) := by
  have ht := (hD.const_mul (c ^ 2 * Real.pi)).add
    ((tendsto_inv_atTop_zero.comp hNlim).const_mul ((2 - c ^ 2 - c ^ 2 * d1Theta Δ 0 0) / 2))
  simp only [mul_zero, add_zero] at ht
  apply ht.congr
  intro i
  have hNi : (N i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
  have he := sum_erase_add (s := (univ : Finset (Fin (n i))))
    (fun j => d1Theta Δ 0 (q i j)) (mem_univ (l i))
  rw [hl i] at he
  unfold betheCountingDerivative ratioZeroCoefficient
  rw [← he]
  simp only [Function.comp_apply]
  field_simp
  ring

end PottsDiscontinuity.Bethe
