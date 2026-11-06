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

@[expose] public section

open scoped BigOperators
open Set

namespace PottsDiscontinuity.Bethe

/-- First partial derivative of the Bethe phase. -/
noncomputable def thetaPartialFirst (Δ x y : ℝ) : ℝ :=
  deriv (fun s => theta Δ s y) x

/-- Second partial derivative of the Bethe phase. -/
noncomputable def thetaPartialSecond (Δ x y : ℝ) : ℝ :=
  deriv (fun t => theta Δ x t) y

private theorem hasDerivAt_affine_zero (z c : ℝ) : HasDerivAt (fun t : ℝ => z + t * c) c 0 := by
  convert (hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id' (0 : ℝ)).mul_const c) using 1; ring

/-- Chain rule for the phase along an affine path in both variables. -/
theorem hasDerivAt_theta_affine {Δ : ℝ} (hΔ : Δ < -1) (x y a b : ℝ) :
    HasDerivAt (fun t => theta Δ (x + t * a) (y + t * b))
      (a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y) 0 := by
  let F : ℝ × ℝ → ℝ := fun z => theta Δ z.1 z.2
  have hF : HasFDerivAt F (fderiv ℝ F (x, y)) (x, y) :=
    (analyticAt_theta_xy hΔ x y).differentiableAt.hasFDerivAt
  have h₁eq : thetaPartialFirst Δ x y = fderiv ℝ F (x, y) (1, 0) :=
    (analyticAt_theta_left hΔ x y).differentiableAt.hasDerivAt.unique
      (HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, y) : ℝ × ℝ)) x hF
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  have h₂eq : thetaPartialSecond Δ x y = fderiv ℝ F (x, y) (0, 1) :=
    (analyticAt_theta_right hΔ x y).differentiableAt.hasDerivAt.unique
      (HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((x, t) : ℝ × ℝ)) y hF
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  have hfd : fderiv ℝ F (x, y) (a, b) =
      a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y := by
    rw [show (a, b) = a • (1, 0) + b • (0, 1) by ext <;> simp, map_add, map_smul, map_smul,
      ← h₁eq, ← h₂eq]
    simp [smul_eq_mul]
  have hF0 : HasFDerivAt F (fderiv ℝ F (x, y)) (x + 0 * a, y + 0 * b) := by simpa using hF
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((x + t * a, y + t * b) : ℝ × ℝ))
    0 hF0 ((hasDerivAt_affine_zero x a).prodMk (hasDerivAt_affine_zero y b))
  rwa [hfd] at hcomp

/-- The `j`th coordinate among the first `⌊n/2⌋` coordinates, regarded as a `Fin n`. -/
def discreteHalfIndex (n : ℕ) (j : Fin (n / 2)) : Fin n :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.div_le_self n 2)⟩

/-- The next full index after a first-half coordinate. -/
def discreteHalfNextIndex (n : ℕ) (j : Fin (n / 2)) : Fin n :=
  ⟨j.val + 1, by have := discreteHalfIndex n j |>.isLt; omega⟩

/-- Every first-half coordinate lies strictly before its reflected coordinate. -/
theorem discreteHalfIndex_lt_rev {n : ℕ} (j : Fin (n / 2)) :
    discreteHalfIndex n j < Fin.rev (discreteHalfIndex n j) := by
  change (discreteHalfIndex n j).val < (Fin.rev (discreteHalfIndex n j)).val
  simp only [discreteHalfIndex, Fin.val_mk, Fin.val_rev]; omega

/-- Basis vector `e_j-e_(n+1-j)` for the symmetric subspace. -/
def discreteSymBasis (n : ℕ) (j : Fin (n / 2)) : Fin n → ℝ := fun ell =>
  if ell = discreteHalfIndex n j then 1
  else if ell = Fin.rev (discreteHalfIndex n j) then -1 else 0

/-- The basis vector has the required two point support. -/
theorem sum_discreteSymBasis_mul {n : ℕ} (j : Fin (n / 2)) (f : Fin n → ℝ) :
    (∑ ell : Fin n, discreteSymBasis n j ell * f ell) =
      f (discreteHalfIndex n j) - f (Fin.rev (discreteHalfIndex n j)) := by
  let a := discreteHalfIndex n j
  have hab : a ≠ Fin.rev a := ne_of_lt (discreteHalfIndex_lt_rev j)
  rw [show (∑ ell : Fin n, discreteSymBasis n j ell * f ell) =
      ∑ ell : Fin n, ((if ell = a then f a else 0) + (if ell = Fin.rev a then -f (Fin.rev a) else 0)) from
    Finset.sum_congr rfl fun ell _ => by
      by_cases h₁ : ell = a <;> by_cases h₂ : ell = Fin.rev a <;>
        simp [discreteSymBasis, a, hab, hab.symm, h₁, h₂],
    Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', a, sub_eq_add_neg]

/-- A first-half basis vector is one at its own coordinate and zero at all other
first-half coordinates. -/
theorem discreteSymBasis_at_half {n : ℕ} (i k : Fin (n / 2)) :
    discreteSymBasis n k (discreteHalfIndex n i) = if i = k then 1 else 0 := by
  let ri := discreteHalfIndex n i
  let rk := discreteHalfIndex n k
  have hinj : ri = rk ↔ i = k := ⟨fun h => Fin.ext (congrArg (Fin.val : Fin n → ℕ) h), fun h => by subst h; rfl⟩
  have hnot : ri ≠ Fin.rev rk := fun h => by
    have h₁ : ri < rk := by simpa [ri, rk, congrArg Fin.rev h] using discreteHalfIndex_lt_rev i
    have h₂ : rk < ri := by simpa [ri, rk, h] using discreteHalfIndex_lt_rev k
    exact lt_asymm h₁ h₂
  simp [discreteSymBasis, ri, rk, hinj, hnot]

/-- Each symmetric coordinate basis vector belongs to `R_n_sym`. -/
theorem discreteSymBasis_mem_R_n_sym {n : ℕ} (k : Fin (n / 2)) :
    discreteSymBasis n k ∈ R_n_sym n := by
  let a := discreteHalfIndex n k
  have haa : a ≠ Fin.rev a := ne_of_lt (discreteHalfIndex_lt_rev k)
  intro j
  by_cases h₁ : j = a
  · subst j; simp [discreteSymBasis, a, haa.symm]
  · by_cases h₂ : j = Fin.rev a
    · subst j; simp [discreteSymBasis, a, haa.symm]
    · have hr₁ : Fin.rev j ≠ a := fun h => h₂ (by simpa using congrArg Fin.rev h)
      have hr₂ : Fin.rev j ≠ Fin.rev a := fun h => h₁ (by simpa using congrArg Fin.rev h)
      simp [discreteSymBasis, a, h₁, h₂, hr₁, hr₂]

/-- The source's explicit symmetric-coordinate matrix `A` for `d(I-T)`. -/
noncomputable def discreteBetheMatrixA (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
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
noncomputable def discreteBetheMatrixB (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := Matrix.diagonal fun j =>
      (N : ℝ) * (p (discreteHalfNextIndex n j) - p (discreteHalfIndex n j))

/-- The rescaled matrix `Ã = A B` from the source. -/
noncomputable def discreteBetheMatrixATilde (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ :=
  discreteBetheMatrixA Δ N n p * discreteBetheMatrixB N n p

/-- The residual `I-T` whose differential is used in Theorem 2.3. -/
noncomputable def discreteBetheResidual (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Fin n → ℝ := fun j => p j - discreteBetheMap Δ N n p j

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
  have hcoord := (hasDerivAt_affine_zero (p i) (v i)).sub_const
    (2 * Real.pi * discreteBetheIndex n i / (N : ℝ))
  have hsum := (HasDerivAt.fun_sum (u := Finset.univ) fun ell _ =>
    hasDerivAt_theta_affine hΔ (p i) (p ell) (v i) (v ell)).div_const (N : ℝ)
  convert hcoord.add hsum using 1
  funext t
  simp [discreteBetheResidual, discreteBetheAffinePath, discreteBetheMap]
  ring

/-- On the diagonal, the two partial derivatives of `Θ` cancel. -/
theorem thetaPartial_diag_sum {Δ x : ℝ} (hΔ : Δ < -1) :
    thetaPartialFirst Δ x x + thetaPartialSecond Δ x x = 0 := by
  simpa [thetaPartialFirst, thetaPartialSecond] using deriv_theta_diag hΔ x

/-- The explicit source matrix `A` is the derivative of `I-T` in symmetric
coordinates: its `k`th column is the directional derivative along
`e_k-e_(n+1-k)`, read at the `i`th first-half coordinate. -/
theorem hasDerivAt_discreteBetheResidual_basis {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (p : Fin n → ℝ) (i k : Fin (n / 2)) :
    HasDerivAt
      (fun t => discreteBetheResidual Δ N n
        (discreteBetheAffinePath p (discreteSymBasis n k) t)
        (discreteHalfIndex n i))
      (discreteBetheMatrixA Δ N n p i k) 0 := by
  let ri := discreteHalfIndex n i
  let rk := discreteHalfIndex n k
  let v := discreteSymBasis n k
  convert hasDerivAt_discreteBetheResidual_path (N := N) (n := n) hΔ p v ri using 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    show (∑ ell : Fin n, v ell * thetaPartialSecond Δ (p ri) (p ell)) =
      thetaPartialSecond Δ (p ri) (p rk) - thetaPartialSecond Δ (p ri) (p (Fin.rev rk)) from
      sum_discreteSymBasis_mul k _,
    show v ri = if i = k then 1 else 0 from discreteSymBasis_at_half i k]
  by_cases hik : i = k
  · subst k
    simp only [ite_true, one_mul, discreteBetheMatrixA,
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ri)]
    linear_combination -(thetaPartial_diag_sum (Δ := Δ) (x := p ri) hΔ) / (N : ℝ)
  · simp [discreteBetheMatrixA, hik, ri, rk]

/-- The second derivative of the phase difference is the difference of the two
second partial derivatives. -/
theorem deriv_discreteBetheG_right {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    deriv (fun t => discreteBetheG Δ x t) y =
      thetaPartialSecond Δ x y - thetaPartialSecond Δ (-x) y :=
  deriv_fun_sub (analyticAt_theta_right hΔ x y).differentiableAt
    (analyticAt_theta_right hΔ (-x) y).differentiableAt

/-- The derivative of `G` in the second coordinate is nonnegative on the
negative square. -/
theorem discreteBetheG_deriv_nonneg_neg {Δ x y : ℝ} (hΔ : Δ < -1)
    (hx : x ∈ Icc (-Real.pi) 0) (hy : y ∈ Icc (-Real.pi) 0) :
    0 ≤ deriv (fun t => discreteBetheG Δ x t) y := by
  let lam := lamOf Δ
  have hlam : 0 < lam := lamOf_pos hΔ
  obtain ⟨α, hα, hkx⟩ := (bijOn_kMap hlam).2.2 ⟨hx.1, hx.2.trans Real.pi_pos.le⟩
  obtain ⟨β, hβ, hky⟩ := (bijOn_kMap hlam).2.2 ⟨hy.1, hy.2.trans Real.pi_pos.le⟩
  have hneg {γ z : ℝ} (hγ : γ ∈ Icc (-Real.pi) Real.pi) (hz : z ≤ 0) (hk : kMap lam γ = z) :
      Real.sin γ ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by_contra fun h => by
        have := (strictMono_kMap hlam) (lt_of_not_ge h)
        rw [hk, kMap_zero] at this; linarith) hγ.1
  have hcos : Real.cos (-α - β) ≤ Real.cos (α - β) := by
    have := mul_nonneg_of_nonpos_of_nonpos (hneg hα hx.2 hkx) (hneg hβ hy.2 hky)
    linarith [show Real.cos (α - β) - Real.cos (-α - β) = 2 * Real.sin α * Real.sin β by
      rw [Real.cos_sub, Real.cos_sub]; simp [Real.cos_neg, Real.sin_neg]; ring]
  have hkernel := Xi_le_of_cos_le (by linarith : 0 < 2 * lam) hcos
  have hchain : HasDerivAt (fun t => discreteBetheG Δ (kMap lam α) (kMap lam t))
      (deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β) * Xi lam β) β := by
    have hout : HasDerivAt (fun z => discreteBetheG Δ (kMap lam α) z)
        (deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β)) (kMap lam β) := by
      rw [deriv_discreteBetheG_right hΔ]
      exact (analyticAt_theta_right hΔ (kMap lam α) (kMap lam β)).differentiableAt.hasDerivAt.sub
        (analyticAt_theta_right hΔ (-kMap lam α) (kMap lam β)).differentiableAt.hasDerivAt
    exact hout.comp β (hasDerivAt_kMap hlam β)
  have hcoeff : deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β) * Xi lam β =
      Xi (2 * lam) (α - β) - Xi (2 * lam) (-α - β) :=
    hchain.unique (hasDerivAt_discreteBetheG_kMap hΔ α β)
  rw [← hkx, ← hky]
  nlinarith [Xi_pos hlam β]

/-- When `p∈S_n`, its first-half coordinates are negative. -/
theorem discreteS_n_half_coord_neg {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (j : Fin (n / 2)) : p (discreteHalfIndex n j) < 0 := by
  rcases hp with ⟨_, hmono, hsym⟩
  have hlt := hmono (discreteHalfIndex_lt_rev j)
  rw [hsym (discreteHalfIndex n j)] at hlt
  linarith

/-- Off-diagonal entries of `Ã=AB` telescope to the derivative of `G`. -/
theorem discreteBetheMatrixATilde_offdiag_eq {Δ : ℝ} (hΔ : Δ < -1) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) (hN : 0 < N)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    discreteBetheMatrixATilde Δ N n p i k =
      (p (discreteHalfNextIndex n k) - p (discreteHalfIndex n k)) *
        deriv (fun y => discreteBetheG Δ (p (discreteHalfIndex n i)) y)
          (p (discreteHalfIndex n k)) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [discreteBetheMatrixATilde, Matrix.mul_apply]
  simp [discreteBetheMatrixB, Matrix.diagonal_apply]
  rw [discreteBetheMatrixA, ite_eq_right hik, hp (discreteHalfIndex n k)]
  simp only [thetaPartialSecond]
  rw [deriv_theta_right_neg, deriv_discreteBetheG_right hΔ]
  simp only [thetaPartialSecond]
  field_simp [hNne]

/-- The off-diagonal entries of `Ã` are nonnegative at every configuration in `S_n`. -/
theorem discreteBetheMatrixATilde_offdiag_nonneg {Δ : ℝ} {N n : ℕ}
    (hΔ : Δ < -1) (hN : 0 < N) (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    0 ≤ discreteBetheMatrixATilde Δ N n p i k := by
  rw [discreteBetheMatrixATilde_offdiag_eq hΔ p hp.2.2 hN i k hik]
  exact mul_nonneg
    (sub_nonneg.mpr (hp.2.1 (by simp only [discreteHalfIndex, discreteHalfNextIndex, Fin.mk_lt_mk]; omega)).le)
    (discreteBetheG_deriv_nonneg_neg hΔ
      ⟨(hp.1 _).1.le, (discreteS_n_half_coord_neg hp i).le⟩
      ⟨(hp.1 _).1.le, (discreteS_n_half_coord_neg hp k).le⟩)

end PottsDiscontinuity.Bethe
