module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteAnalysis
public import PottsDiscontinuity.Bethe.DiscreteCore

/-!
# Finite matrices in the discrete Bethe argument

The entries below are the source's displayed symmetric-coordinate matrix and its
gap rescaling.  The estimates here concern only the off-diagonal sign; the later
comparison of its diagonal entries with `2π` uses the excluded `ρ` estimates.
-/

@[expose] public noncomputable section

open scoped BigOperators
open Set

namespace PottsDiscontinuity.Bethe

section
variable (Δ x y : ℝ)
/-- First partial derivative of the Bethe phase. -/
def thetaPartialFirst  : ℝ :=
  deriv (fun s => theta Δ s y) x

/-- Second partial derivative of the Bethe phase. -/
def thetaPartialSecond  : ℝ :=
  deriv (fun t => theta Δ x t) y
end

/-- Chain rule for the phase along an affine path in both variables. -/
theorem hasDerivAt_theta_affine {Δ : ℝ} (hΔ : Δ < -1) (x y a b : ℝ) :
    HasDerivAt (fun t => theta Δ (x + t * a) (y + t * b))
      (a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y) 0 := by
  have hF := (analyticAt_theta_xy hΔ x y).differentiableAt.hasFDerivAt
  have h₁ := (analyticAt_theta_left hΔ x y).differentiableAt.hasDerivAt.unique (hF.comp_hasDerivAt (f := fun s : ℝ => ((s, y) : ℝ × ℝ)) x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  have h₂ := (analyticAt_theta_right hΔ x y).differentiableAt.hasDerivAt.unique (hF.comp_hasDerivAt (f := fun t : ℝ => ((x, t) : ℝ × ℝ)) y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  refine (hF.comp_hasDerivAt_of_eq (f := fun t : ℝ => ((x + t * a, y + t * b) : ℝ × ℝ)) 0 ((((hasDerivAt_id' 0).mul_const a).const_add x).prodMk (((hasDerivAt_id' 0).mul_const b).const_add y)) (by simp)).congr_deriv ?_
  rw [show thetaPartialFirst Δ x y = _ from h₁, show thetaPartialSecond Δ x y = _ from h₂, show ((1 : ℝ) * a, 1 * b) = a • ((1 : ℝ), (0 : ℝ)) + b • (0, 1) by simp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

section
variable (n : ℕ)
/-- The `j`th coordinate among the first `⌊n/2⌋` coordinates, regarded as a `Fin n`. -/
def discreteHalfIndex (j : Fin (n / 2)) : Fin n :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.div_le_self n 2)⟩

/-- The next full index after a first-half coordinate. -/
def discreteHalfNextIndex (j : Fin (n / 2)) : Fin n :=
  ⟨j.val + 1, by omega⟩
end

/-- Every first-half coordinate lies strictly before its reflected coordinate. -/
theorem discreteHalfIndex_lt_rev {n : ℕ} (j : Fin (n / 2)) :
    discreteHalfIndex n j < Fin.rev (discreteHalfIndex n j) := by
  grind [discreteHalfIndex, Fin.rev]

/-- Basis vector `e_j-e_(n+1-j)` for the symmetric subspace. -/
def discreteSymBasis (n : ℕ) (j : Fin (n / 2)) : Fin n → ℝ := fun ell =>
  if ell = discreteHalfIndex n j then 1
  else if ell = Fin.rev (discreteHalfIndex n j) then -1 else 0

section
variable {n : ℕ}
/-- The basis vector has the required two point support. -/
theorem sum_discreteSymBasis_mul (j : Fin (n / 2)) (f : Fin n → ℝ) :
    (∑ ell : Fin n, discreteSymBasis n j ell * f ell) =
      f (discreteHalfIndex n j) - f (Fin.rev (discreteHalfIndex n j)) := by
  have hab := ne_of_lt (discreteHalfIndex_lt_rev j)
  rw [Fintype.sum_eq_add _ _ hab fun x hx => by simp [discreteSymBasis, hx]]
  simp [discreteSymBasis, hab.symm]
  ring

/-- A first-half basis vector is one at its own coordinate and zero at all other
first-half coordinates. -/
theorem discreteSymBasis_at_half (i k : Fin (n / 2)) :
    discreteSymBasis n k (discreteHalfIndex n i) = if i = k then 1 else 0 := by
  unfold discreteSymBasis
  split_ifs <;> simp_all [Fin.ext_iff, discreteHalfIndex, Fin.rev] <;> omega

/-- Each symmetric coordinate basis vector belongs to `R_n_sym`. -/
theorem discreteSymBasis_mem_R_n_sym (k : Fin (n / 2)) :
    discreteSymBasis n k ∈ R_n_sym n := by
  intro j
  unfold discreteSymBasis
  split_ifs <;> simp_all [Fin.ext_iff, discreteHalfIndex, Fin.rev] <;> omega
end

/-- The source's explicit symmetric-coordinate matrix `A` for `d(I-T)`. -/
def discreteBetheMatrixA (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := fun i k =>
  if i = k then
    1 + (∑ ell ∈ Finset.univ.erase (discreteHalfIndex n i),
      thetaPartialFirst Δ (p (discreteHalfIndex n i)) (p ell)) / (N : ℝ) -
      thetaPartialSecond Δ (p (discreteHalfIndex n i))
        (p (Fin.rev (discreteHalfIndex n i))) / (N : ℝ)
  else
    (thetaPartialSecond Δ (p (discreteHalfIndex n i)) (p (discreteHalfIndex n k)) -
      thetaPartialSecond Δ (p (discreteHalfIndex n i))
        (p (Fin.rev (discreteHalfIndex n k)))) / (N : ℝ)

/-- The source's gap matrix `B`, with diagonal entries `N (p_(j+1)-p_j)`. -/
def discreteBetheMatrixB (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := Matrix.diagonal fun j =>
      (N : ℝ) * (p (discreteHalfNextIndex n j) - p (discreteHalfIndex n j))

section
variable (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ)
/-- The rescaled matrix `Ã = A B` from the source. -/
def discreteBetheMatrixATilde  :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ :=
  discreteBetheMatrixA Δ N n p * discreteBetheMatrixB N n p

/-- The residual `I-T` whose differential is used in Theorem 2.3. -/
def discreteBetheResidual  :
    Fin n → ℝ := fun j => p j - discreteBetheMap Δ N n p j
end

/-- Affine path through `p` in direction `v`. -/
def discreteBetheAffinePath {n : ℕ} (p v : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun j => p j + t * v j

/-- Directional derivative formula for the residual `I-T`. -/
theorem hasDerivAt_discreteBetheResidual_path {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (p v : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t => discreteBetheResidual Δ N n (discreteBetheAffinePath p v t) i)
      (v i + (∑ ell : Fin n,
        (v i * thetaPartialFirst Δ (p i) (p ell) +
          v ell * thetaPartialSecond Δ (p i) (p ell))) / (N : ℝ)) 0 := by
  refine ((((hasDerivAt_id' 0).mul_const (v i)).const_add (p i)).sub_const (2 * Real.pi * discreteBetheIndex n i / N)).add
    ((HasDerivAt.fun_sum (u := Finset.univ) fun ell _ => hasDerivAt_theta_affine hΔ (p i) (p ell) (v i) (v ell)).div_const N) |>.congr_of_eventuallyEq ?_ |>.congr_deriv (by simp)
  filter_upwards with t
  simp [discreteBetheResidual, discreteBetheAffinePath, discreteBetheMap]
  ring

/-- On the diagonal, the two partial derivatives of `Θ` cancel. -/
theorem thetaPartial_diag_sum {Δ x : ℝ} (hΔ : Δ < -1) :
    thetaPartialFirst Δ x x + thetaPartialSecond Δ x x = 0 := by
  simpa [thetaPartialFirst, thetaPartialSecond] using deriv_theta_diag hΔ x

section
variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ
/-- The explicit source matrix `A` is the derivative of `I-T` in symmetric
coordinates: its `k`th column is the directional derivative along
`e_k-e_(n+1-k)`, read at the `i`th first-half coordinate. -/
theorem hasDerivAt_discreteBetheResidual_basis {N n : ℕ} (p : Fin n → ℝ) (i k : Fin (n / 2)) :
    HasDerivAt
      (fun t => discreteBetheResidual Δ N n
        (discreteBetheAffinePath p (discreteSymBasis n k) t)
        (discreteHalfIndex n i))
      (discreteBetheMatrixA Δ N n p i k) 0 := by
  refine (hasDerivAt_discreteBetheResidual_path hΔ p _ _).congr_deriv ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_discreteSymBasis_mul, discreteSymBasis_at_half, discreteBetheMatrixA]
  split_ifs with hik
  · subst hik
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (discreteHalfIndex n i))]
    grind [thetaPartial_diag_sum]
  · simp

/-- The second derivative of the phase difference is the difference of the two
second partial derivatives. -/
theorem deriv_discreteBetheG_right (x y : ℝ) :
    deriv (fun t => discreteBetheG Δ x t) y =
      thetaPartialSecond Δ x y - thetaPartialSecond Δ (-x) y :=
  deriv_fun_sub (analyticAt_theta_right hΔ x y).differentiableAt (analyticAt_theta_right hΔ (-x) y).differentiableAt
end

/-- The derivative of `G` in the second coordinate is nonnegative on the
negative square. -/
theorem discreteBetheG_deriv_nonneg_neg {Δ x y : ℝ} (hΔ : Δ < -1)
    (hx : x ∈ Icc (-Real.pi) 0) (hy : y ∈ Icc (-Real.pi) 0) :
    0 ≤ deriv (fun t => discreteBetheG Δ x t) y := by
  let lam := lamOf Δ
  have hlam := lamOf_pos hΔ
  have hneg {z : ℝ} (hz : z ∈ Icc (-Real.pi) 0) : ∃ γ ∈ Icc (-Real.pi) 0, kMap lam γ = z := by
    obtain ⟨γ, hγ, hk⟩ := (bijOn_kMap hlam).2.2 (⟨hz.1, by linarith [hz.2, Real.pi_pos]⟩ : z ∈ Icc (-Real.pi) Real.pi)
    refine ⟨γ, ⟨hγ.1, not_lt.1 fun h => ?_⟩, hk⟩
    have := strictMono_kMap hlam h
    rw [hk, kMap_zero] at this
    linarith [hz.2]
  obtain ⟨α, hαneg, hkx⟩ := hneg hx
  obtain ⟨β, hβneg, hky⟩ := hneg hy
  have hsα := Real.sin_nonpos_of_nonpos_of_neg_pi_le hαneg.2 hαneg.1
  have hsβ := Real.sin_nonpos_of_nonpos_of_neg_pi_le hβneg.2 hβneg.1
  have hcos : Real.cos (-α - β) ≤ Real.cos (α - β) := by
    rw [Real.cos_sub, Real.cos_sub]
    simp
    nlinarith
  have hkernel := Xi_le_of_cos_le (by linarith : 0 < 2 * lam) hcos
  have hchain : HasDerivAt
      (fun t => discreteBetheG Δ (kMap lam α) (kMap lam t))
      (deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β) * Xi lam β) β := by
    refine HasDerivAt.comp (h₂ := fun z => discreteBetheG Δ (kMap lam α) z) β ?_ (hasDerivAt_kMap hlam β)
    rw [deriv_discreteBetheG_right hΔ]
    exact (analyticAt_theta_right hΔ _ _).differentiableAt.hasDerivAt.sub (analyticAt_theta_right hΔ _ _).differentiableAt.hasDerivAt
  have hcoeff := hchain.unique (hasDerivAt_discreteBetheG_kMap hΔ α β)
  have hpos := Xi_pos hlam β
  rw [← hkx, ← hky]
  nlinarith

/-- When `p∈S_n`, its first-half coordinates are negative. -/
theorem discreteS_n_half_coord_neg {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (j : Fin (n / 2)) : p (discreteHalfIndex n j) < 0 := by
  rcases hp with ⟨_, hmono, hsym⟩
  have hlt := hmono (discreteHalfIndex_lt_rev j)
  rw [hsym (discreteHalfIndex n j)] at hlt
  linarith

section
variable {Δ : ℝ}
/-- Off-diagonal entries of `Ã=AB` telescope to the derivative of `G`. -/
theorem discreteBetheMatrixATilde_offdiag_eq (hΔ : Δ < -1) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) (hN : 0 < N)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    discreteBetheMatrixATilde Δ N n p i k =
      (p (discreteHalfNextIndex n k) - p (discreteHalfIndex n k)) *
        deriv (fun y => discreteBetheG Δ (p (discreteHalfIndex n i)) y)
          (p (discreteHalfIndex n k)) := by
  have hNne : (N : ℝ) ≠ 0 := by positivity
  rw [discreteBetheMatrixATilde, Matrix.mul_apply]
  simp [discreteBetheMatrixB, Matrix.diagonal_apply]
  rw [discreteBetheMatrixA, ite_eq_right hik, (hp (discreteHalfIndex n k))]
  simp only [thetaPartialSecond]
  rw [deriv_theta_right_neg, deriv_discreteBetheG_right hΔ]
  grind [thetaPartialSecond]

/-- The off-diagonal entries of `Ã` are nonnegative at every configuration in `S_n`. -/
theorem discreteBetheMatrixATilde_offdiag_nonneg {N n : ℕ}
    (hΔ : Δ < -1) (hN : 0 < N) (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    0 ≤ discreteBetheMatrixATilde Δ N n p i k := by
  rw [discreteBetheMatrixATilde_offdiag_eq hΔ p hp.2.2 hN i k hik]
  have hgap := (sub_pos.mpr (hp.2.1 (show discreteHalfIndex n k < discreteHalfNextIndex n k by tauto))).le
  have hG := discreteBetheG_deriv_nonneg_neg hΔ ⟨(hp.1 _).1.le, (discreteS_n_half_coord_neg hp i).le⟩
    ⟨(hp.1 _).1.le, (discreteS_n_half_coord_neg hp k).le⟩
  positivity
end

end PottsDiscontinuity.Bethe
