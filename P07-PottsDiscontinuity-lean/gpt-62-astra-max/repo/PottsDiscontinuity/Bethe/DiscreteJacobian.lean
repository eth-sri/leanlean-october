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

/-- Chain rule for the phase along an affine path in both variables. -/
theorem hasDerivAt_theta_affine {Δ : ℝ} (hΔ : Δ < -1) (x y a b : ℝ) :
    HasDerivAt (fun t => theta Δ (x + t * a) (y + t * b))
      (a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y) 0 := by
  let F : ℝ × ℝ → ℝ := fun z => theta Δ z.1 z.2
  have hF :=
    (analyticAt_theta_xy hΔ x y).differentiableAt.hasFDerivAt
  have h₁eq : thetaPartialFirst Δ x y = fderiv ℝ F (x, y) (1, 0) := (analyticAt_theta_left hΔ x y).differentiableAt.hasDerivAt.unique (HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, y))
      x hF ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  have h₂eq : thetaPartialSecond Δ x y = fderiv ℝ F (x, y) (0, 1) := (analyticAt_theta_right hΔ x y).differentiableAt.hasDerivAt.unique (HasFDerivAt.comp_hasDerivAt
      y hF ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  have hfd : fderiv ℝ F (x, y) (a, b) =
      a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y := by
    calc
      _ =
          fderiv ℝ F (x, y) (a • (1, 0) + b • (0, 1)) := by simp
      _ = a • fderiv ℝ F (x, y) (1, 0) + b • fderiv ℝ F (x, y) (0, 1) := by
        grind [map_add, map_smul]
      _ = _ := by
        grind [smul_eq_mul]
  have hxa : HasDerivAt (fun t : ℝ => x + t * a) a 0 := by
    have hm := (hasDerivAt_id 0).mul_const a
    simp_all
  have hyb : HasDerivAt (fun t : ℝ => y + t * b) b 0 := by
    have hm := (hasDerivAt_id 0).mul_const b
    simp_all
  have hcomp := HasFDerivAt.comp_hasDerivAt 0 (by simpa using hF) (hxa.prodMk hyb)
  rw [hfd] at hcomp
  exact hcomp

section
variable {n : ℕ} (j : Fin (n / 2))

include j in
/-- The `j`th coordinate among the first `⌊n/2⌋` coordinates, regarded as a `Fin n`. -/
def discreteHalfIndex : Fin n :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.div_le_self n 2)⟩

include j in
/-- The next full index after a first-half coordinate. -/
def discreteHalfNextIndex : Fin n :=
  ⟨j.val + 1, by omega⟩

/-- Every first-half coordinate lies strictly before its reflected coordinate. -/
theorem discreteHalfIndex_lt_rev :
    discreteHalfIndex j < Fin.rev (discreteHalfIndex j) := by
  grind [discreteHalfIndex, Fin.val_mk, Fin.val_rev]

include j in
/-- Basis vector `e_j-e_(n+1-j)` for the symmetric subspace. -/
def discreteSymBasis : Fin n → ℝ := fun ell =>
  if ell = discreteHalfIndex j then 1
  else if ell = Fin.rev (discreteHalfIndex j) then -1 else 0

/-- The basis vector has the required two point support. -/
theorem sum_discreteSymBasis_mul (f : Fin n → ℝ) :
    (∑ ell, discreteSymBasis j ell * f ell) =
      f (discreteHalfIndex j) - f (Fin.rev (discreteHalfIndex j)) := by
  classical
  let a := discreteHalfIndex j
  let b := Fin.rev a
  have hpoint (ell : Fin n) : discreteSymBasis j ell * f ell =
      (if ell = a then f a else 0) + (if ell = b then -f b else 0) := by
    by_cases h₁ : ell = a <;> simp_all [discreteSymBasis, a, b, (ne_of_lt (discreteHalfIndex_lt_rev j))]
  calc
    _ = ∑ ell,
          ((if ell = a then f a else 0) + (if ell = b then -f b else 0)) :=
      by grind
    _ = (∑ ell, if ell = a then f a else 0) +
          ∑ ell, if ell = b then -f b else 0 := Finset.sum_add_distrib
    _ = _ := by simp [Finset.sum_ite_eq', a, b]; ring

/-- A first-half basis vector is one at its own coordinate and zero at all other
first-half coordinates. -/
theorem discreteSymBasis_at_half (i k : Fin (n / 2)) :
    discreteSymBasis k (discreteHalfIndex i) = if i = k then 1 else 0 := by
  classical
  let ri := discreteHalfIndex i
  let rk := discreteHalfIndex k
  have hinj : ri = rk ↔ i = k := by
    constructor
    · intro h
      have hv := congrArg Fin.val h
      exact Fin.ext hv
    · rintro rfl
      rfl
  have hnot : ri ≠ Fin.rev rk := by
    grind [discreteHalfIndex_lt_rev]
  simp_all [discreteSymBasis, ri, rk]

/-- Each symmetric coordinate basis vector belongs to `R_n_sym`. -/
theorem discreteSymBasis_mem_R_n_sym (k : Fin (n / 2)) :
    discreteSymBasis k ∈ R_n_sym n := by
  classical
  let a := discreteHalfIndex k
  have haa := ne_of_lt (discreteHalfIndex_lt_rev k)
  intro j
  have hvalA : discreteSymBasis k a = 1 := by
    simp [discreteSymBasis, a]
  have hvalRev : discreteSymBasis k (Fin.rev a) = -1 := by
    by_cases h : Fin.rev a = a
    · grind
    · simp [discreteSymBasis, a, h]
  by_cases h₁ : j = a
  · grind
  · by_cases h₂ : j = Fin.rev a
    · grind
    · have hr₁ : Fin.rev j ≠ a := by
        grind
      have hr₂ : Fin.rev j ≠ Fin.rev a := by
        grind
      simp [discreteSymBasis, a, h₁, h₂, hr₁, hr₂]

end

section
variable (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ)
include N p

include Δ in
/-- The source's explicit symmetric-coordinate matrix `A` for `d(I-T)`. -/
noncomputable def discreteBetheMatrixA :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := fun i k =>
  if i = k then
    1 + (∑ ell ∈ Finset.univ.erase (discreteHalfIndex i),
      thetaPartialFirst Δ (p (discreteHalfIndex i)) (p ell)) / N -
      thetaPartialSecond Δ (p (discreteHalfIndex i))
        (p (Fin.rev (discreteHalfIndex i))) / N
  else
    (thetaPartialSecond Δ (p (discreteHalfIndex i)) (p (discreteHalfIndex k)) -
      thetaPartialSecond Δ (p (discreteHalfIndex i))
        (p (Fin.rev (discreteHalfIndex k)))) / N

/-- The source's gap matrix `B`, with diagonal entries `N (p_(j+1)-p_j)`. -/
noncomputable def discreteBetheMatrixB :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := Matrix.diagonal fun j =>
      N * (p (discreteHalfNextIndex j) - p (discreteHalfIndex j))

include Δ in
/-- The rescaled matrix `Ã = A B` from the source. -/
noncomputable def discreteBetheMatrixATilde :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ :=
  discreteBetheMatrixA Δ N n p * discreteBetheMatrixB N n p

include Δ in
/-- The residual `I-T` whose differential is used in Theorem 2.3. -/
noncomputable def discreteBetheResidual :
    Fin n → ℝ := fun j => p j - discreteBetheMap Δ N n p j

end

/-- Affine path through `p` in direction `v`. -/
def discreteBetheAffinePath {n : ℕ} (p v : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun j => p j + t * v j

variable {Δ : ℝ} (hΔ : Δ < -1) {N n : ℕ} (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) (hN : 0 < N)
    (i k : Fin (n / 2))

include hΔ in
/-- Directional derivative formula for the residual `I-T`. -/
theorem hasDerivAt_discreteBetheResidual_path (p v : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t => discreteBetheResidual Δ N n (discreteBetheAffinePath p v t) i)
      (v i + (∑ ell,
        (v i * thetaPartialFirst Δ (p i) (p ell) +
          v ell * thetaPartialSecond Δ (p i) (p ell))) / N) 0 := by
  have hcoord (j : Fin n) : HasDerivAt (fun t : ℝ => p j + t * v j) (v j) 0 := by
    have hm := (hasDerivAt_id 0).mul_const (v j)
    simp_all
  have hterm (ell : Fin n) :=
    hasDerivAt_theta_affine hΔ (p i) (p ell) (v i) (v ell)
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ ell,
        theta Δ (p i + t * v i) (p ell + t * v ell))
      (∑ ell,
        (v i * thetaPartialFirst Δ (p i) (p ell) +
          v ell * thetaPartialSecond Δ (p i) (p ell))) 0 := HasDerivAt.fun_sum fun ell x => hterm ell
  let c := 2 * Real.pi * discreteBetheIndex i / N
  have hbase : HasDerivAt (fun t : ℝ => p i + t * v i - c) (v i) 0 := by
    have hsub := (hcoord i).sub (hasDerivAt_const 0 c)
    have heq : (fun t : ℝ => p i + t * v i - c) =
        (fun t : ℝ => p i + t * v i) - fun _ : ℝ => c := by
      funext t
      rfl
    grind
  have hres := hbase.add (hsum.div_const N)
  have hfun : (fun t : ℝ =>
      discreteBetheResidual Δ N n (discreteBetheAffinePath p v t) i) =
      (fun t => p i + t * v i - c) +
        (fun t => (∑ ell,
          theta Δ (p i + t * v i) (p ell + t * v ell)) / N) := by
    funext t
    simp [discreteBetheResidual, discreteBetheAffinePath, discreteBetheMap, c]
    ring
  grind

/-- On the diagonal, the two partial derivatives of `Θ` cancel. -/
theorem thetaPartial_diag_sum {Δ x : ℝ} (hΔ : Δ < -1) :
    thetaPartialFirst Δ x x + thetaPartialSecond Δ x x = 0 := deriv_theta_diag hΔ x

include hΔ in
/-- The explicit source matrix `A` is the derivative of `I-T` in symmetric
coordinates: its `k`th column is the directional derivative along
`e_k-e_(n+1-k)`, read at the `i`th first-half coordinate. -/
theorem hasDerivAt_discreteBetheResidual_basis :
    HasDerivAt
      (fun t => discreteBetheResidual Δ N n
        (discreteBetheAffinePath p (discreteSymBasis k) t)
        (discreteHalfIndex i))
      (discreteBetheMatrixA Δ N n p i k) 0 := by
  let ri := discreteHalfIndex i
  let rk := discreteHalfIndex k
  let v := discreteSymBasis k
  have hgeneral := hasDerivAt_discreteBetheResidual_path (N := N) hΔ p v ri
  have hv : v ri = if i = k then 1 else 0 := discreteSymBasis_at_half i k
  let firstAt := thetaPartialFirst Δ (p ri)
  have hsum1 : (∑ ell,
      v ri * firstAt (p ell)) =
      v ri * ∑ ell, firstAt (p ell) := by
    simp_all
  let second := thetaPartialSecond Δ (p ri)
  have hsum2 : (∑ ell,
      v ell * second (p ell)) =
      second (p rk) -
        second (p (Fin.rev rk)) := by
    exact sum_discreteSymBasis_mul k
      _
  have hcoef : v ri +
      (∑ ell,
        (v ri * firstAt (p ell) +
          v ell * second (p ell))) / N =
      discreteBetheMatrixA Δ N n p i k := by
    rw [Finset.sum_add_distrib, hsum1, hsum2, hv]
    by_cases hik : i = k
    · subst k
      rw [discreteBetheMatrixA, ite_eq_left rfl]
      have hsplit :
          (∑ ell, firstAt (p ell)) =
            firstAt (p ri) +
              ∑ ell ∈ Finset.univ.erase ri,
                firstAt (p ell) := by
        simp_all
      grind [thetaPartial_diag_sum]
    · simp only [ite_eq_right hik, zero_add]
      rw [discreteBetheMatrixA, ite_eq_right hik]
      ring
  grind

include hΔ in
/-- The second derivative of the phase difference is the difference of the two
second partial derivatives. -/
theorem deriv_discreteBetheG_right (x y : ℝ) :
    deriv (fun t => discreteBetheG Δ x t) y =
      thetaPartialSecond Δ x y - thetaPartialSecond Δ (-x) y := by
  change deriv (fun t => theta Δ x t - theta Δ (-x) t) y = _
  rw [deriv_fun_sub (analyticAt_theta_right hΔ x y).differentiableAt ((analyticAt_theta_right hΔ _ y).differentiableAt)]
  rfl

/-- The derivative of `G` in the second coordinate is nonnegative on the
negative square. -/
theorem discreteBetheG_deriv_nonneg_neg {Δ x y : ℝ} (hΔ : Δ < -1)
    (hx : x ∈ Icc (-Real.pi) 0) (hy : y ∈ Icc (-Real.pi) 0) :
    0 ≤ deriv (fun t => discreteBetheG Δ x t) y := by
  let lam := lamOf Δ
  have hlam := lamOf_pos hΔ
  obtain ⟨α, hα, hkx⟩ := (bijOn_kMap hlam).2.2 ⟨hx.1, le_trans hx.2 Real.pi_pos.le⟩
  obtain ⟨β, hβ, hky⟩ := (bijOn_kMap hlam).2.2 ⟨hy.1, le_trans hy.2 Real.pi_pos.le⟩
  have hαneg : α ∈ Icc (-Real.pi) 0 := by
    constructor
    · exact hα.1
    · by_contra h
      have hka := (strictMono_kMap hlam) (lt_of_not_ge h)
      rw [hkx, kMap_zero] at hka
      grind
  have hβneg : β ∈ Icc (-Real.pi) 0 := by
    constructor
    · exact hβ.1
    · by_contra h
      have hkb := (strictMono_kMap hlam) (lt_of_not_ge h)
      rw [hky, kMap_zero] at hkb
      grind
  have hsα := Real.sin_nonpos_of_nonpos_of_neg_pi_le hαneg.2 hαneg.1
  have hsβ := Real.sin_nonpos_of_nonpos_of_neg_pi_le hβneg.2 hβneg.1
  have hcos : Real.cos (-α - β) ≤ Real.cos (α - β) := by
    have htrig : Real.cos (α - β) - Real.cos (-α - β) =
        2 * Real.sin α * Real.sin β := by
      grind [Real.cos_sub, Real.cos_neg, Real.sin_neg]
    nlinarith
  have hkernel := Xi_le_of_cos_le (by linarith : 0 < 2 * lam) hcos
  have hchain : HasDerivAt
      (fun t => discreteBetheG Δ (kMap lam α) (kMap lam t))
      (deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β) * Xi lam β) β := by
    have hout : HasDerivAt (fun z => discreteBetheG Δ (kMap lam α) z)
        (deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β))
        (kMap lam β) := by
      rw [deriv_discreteBetheG_right hΔ _ _]
      exact ((analyticAt_theta_right hΔ _ _).differentiableAt.hasDerivAt).sub ((analyticAt_theta_right hΔ _ _).differentiableAt.hasDerivAt)
    exact hout.comp β (hasDerivAt_kMap hlam β)
  have hcoeff := hchain.unique (hasDerivAt_discreteBetheG_kMap hΔ α β)
  have hpos := Xi_pos hlam β
  rw [← hkx, ← hky]
  nlinarith

/-- When `p∈S_n`, its first-half coordinates are negative. -/
theorem discreteS_n_half_coord_neg {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (j : Fin (n / 2)) : p (discreteHalfIndex j) < 0 := by
  rcases hp with ⟨_, hmono, hsym⟩
  have hlt := hmono (discreteHalfIndex_lt_rev j)
  simp_all [hsym _]

include hΔ hp hN in
/-- Off-diagonal entries of `Ã=AB` telescope to the derivative of `G`. -/
theorem discreteBetheMatrixATilde_offdiag_eq (hik : i ≠ k) :
    discreteBetheMatrixATilde Δ N n p i k =
      (p (discreteHalfNextIndex k) - p (discreteHalfIndex k)) *
        deriv (fun y => discreteBetheG Δ (p (discreteHalfIndex i)) y)
          (p (discreteHalfIndex k)) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [discreteBetheMatrixATilde, Matrix.mul_apply]
  simp [discreteBetheMatrixB, Matrix.diagonal_apply]
  rw [discreteBetheMatrixA, ite_eq_right hik]
  have hsym := hp (discreteHalfIndex k)
  grind [thetaPartialSecond, deriv_theta_right_neg, deriv_discreteBetheG_right hΔ]

/-- The off-diagonal entries of `Ã` are nonnegative at every configuration in `S_n`. -/
theorem discreteBetheMatrixATilde_offdiag_nonneg
    (hΔ : Δ < -1) (hN : 0 < N) (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    0 ≤ discreteBetheMatrixATilde Δ N n p i k := by
  rw [discreteBetheMatrixATilde_offdiag_eq hΔ p hp.2.2 hN i k hik]
  have hgap : 0 ≤ p (discreteHalfNextIndex k) - p (discreteHalfIndex k) := le_of_lt (sub_pos.mpr (hp.2.1 (by simp [discreteHalfIndex, discreteHalfNextIndex, Fin.mk_lt_mk])))
  have hG :=
    discreteBetheG_deriv_nonneg_neg hΔ ⟨le_of_lt ((hp.1 _).1), le_of_lt (discreteS_n_half_coord_neg hp i)⟩
      ⟨le_of_lt ((hp.1 _).1), le_of_lt (discreteS_n_half_coord_neg hp k)⟩
  positivity

end PottsDiscontinuity.Bethe
