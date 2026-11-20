module

public import Mathlib
public import PottsDiscontinuity.Bethe.ThetaK
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
  have h₁ :=
    (analyticAt_theta_left hΔ x y).differentiableAt.hasDerivAt
  have h₂ :=
    (analyticAt_theta_right hΔ x y).differentiableAt.hasDerivAt
  have h₁path :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h₂path :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h₁eq : thetaPartialFirst Δ x y = fderiv ℝ F (x, y) (1, 0) := by
    exact h₁.unique (HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, y) : ℝ × ℝ))
      x hF h₁path)
  have h₂eq : thetaPartialSecond Δ x y = fderiv ℝ F (x, y) (0, 1) := by
    exact h₂.unique (HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((x, t) : ℝ × ℝ))
      y hF h₂path)
  have hfd : fderiv ℝ F (x, y) (a, b) =
      a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y := by
    calc
      fderiv ℝ F (x, y) (a, b) =
          fderiv ℝ F (x, y) (a • (1, 0) + b • (0, 1)) := by simp
      _ = a • fderiv ℝ F (x, y) (1, 0) + b • fderiv ℝ F (x, y) (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y := by
        simp_all
  have hxa : HasDerivAt (fun t : ℝ => x + t * a) a 0 := by
    have hm := (hasDerivAt_id 0).mul_const a
    simp_all
  have hyb : HasDerivAt (fun t : ℝ => y + t * b) b 0 := by
    have hm := (hasDerivAt_id 0).mul_const b
    simp_all
  have hpath := hxa.prodMk hyb
  have hF0 : HasFDerivAt F (fderiv ℝ F (x, y)) (x + 0 * a, y + 0 * b) := by
    simpa using hF
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ =>
      ((x + t * a, y + t * b) : ℝ × ℝ)) 0 hF0 hpath
  rw [hfd] at hcomp
  assumption

section

variable (n : ℕ) (j : Fin (n / 2))

/-- The `j`th coordinate among the first `⌊n/2⌋` coordinates, regarded as a `Fin n`. -/
def discreteHalfIndex : Fin n :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.div_le_self n 2)⟩


end

/-- Every first-half coordinate lies strictly before its reflected coordinate. -/
theorem discreteHalfIndex_lt_rev {n : ℕ} (j : Fin (n / 2)) :
    discreteHalfIndex n j < Fin.rev (discreteHalfIndex n j) := by
  grind only [discreteHalfIndex, Fin.val_rev]

/-- Basis vector `e_j-e_(n+1-j)` for the symmetric subspace. -/
def discreteSymBasis (n : ℕ) (j : Fin (n / 2)) : Fin n → ℝ := fun ell =>
  if ell = discreteHalfIndex n j then 1
  else if ell = Fin.rev (discreteHalfIndex n j) then -1 else 0

/-- The basis vector has the required two point support. -/
theorem sum_discreteSymBasis_mul {n : ℕ} (j : Fin (n / 2)) (f : Fin n → ℝ) :
    (∑ ell : Fin n, discreteSymBasis n j ell * f ell) =
      f (discreteHalfIndex n j) - f (Fin.rev (discreteHalfIndex n j)) := by
  classical
  let a := discreteHalfIndex n j
  let b := Fin.rev a
  have hab : a ≠ b := (ne_of_lt (discreteHalfIndex_lt_rev j))
  have hpoint (ell : Fin n) : discreteSymBasis n j ell * f ell =
      (if ell = a then f a else 0) + (if ell = b then -f b else 0) := by
    by_cases h₁ : ell = a
    · subst ell
      simp [discreteSymBasis, a, hab]
    grind [discreteSymBasis]
  calc
    _ = ∑ ell : Fin n,
          ((if ell = a then f a else 0) + (if ell = b then -f b else 0)) :=
      Finset.sum_congr rfl (fun ell _ => hpoint ell)
    _ = (∑ ell : Fin n, if ell = a then f a else 0) +
          ∑ ell : Fin n, if ell = b then -f b else 0 := Finset.sum_add_distrib
    _ = f a - f b := by simp [Finset.sum_ite_eq', a, b]; ring

/-- A first-half basis vector is one at its own coordinate and zero at all other
first-half coordinates. -/
theorem discreteSymBasis_at_half {n : ℕ} (i k : Fin (n / 2)) :
    discreteSymBasis n k (discreteHalfIndex n i) = if i = k then 1 else 0 := by
  classical
  let ri := discreteHalfIndex n i
  let rk := discreteHalfIndex n k
  have hinj : ri = rk ↔ i = k := by
    constructor
    · intro h
      have hv := congrArg Fin.val h
      change i.val = k.val at hv
      omega
    grind
  grind only [discreteSymBasis, Fin.rev, discreteHalfIndex_lt_rev]

/-- Each symmetric coordinate basis vector belongs to `R_n_sym`. -/
theorem discreteSymBasis_mem_R_n_sym {n : ℕ} (k : Fin (n / 2)) :
    discreteSymBasis n k ∈ R_n_sym n := by
  classical
  let a := discreteHalfIndex n k
  have haa : a ≠ Fin.rev a := ne_of_lt (discreteHalfIndex_lt_rev k)
  change ∀ j, discreteSymBasis n k (Fin.rev j) = -discreteSymBasis n k j
  intro j
  have hvalA : discreteSymBasis n k a = 1 := by
    simp [discreteSymBasis, a]
  have hvalRev : discreteSymBasis n k (Fin.rev a) = -1 := by
    by_cases h : Fin.rev a = a
    · simp_all
    · simp [discreteSymBasis, a, h]
  by_cases h₁ : j = a
  · simp_all
  · by_cases h₂ : j = Fin.rev a
    · simp_all
    · have hr₁ : Fin.rev j ≠ a := by
        grind
      have hr₂ : Fin.rev j ≠ Fin.rev a := by
        simp_all
      simp [discreteSymBasis, a, h₁, h₂, hr₁]

/-- The counting-function diagonal and the second-variable response in the
    symmetric-coordinate Jacobian. -/
noncomputable def discreteBetheMatrixA (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := fun i k =>
  let r := discreteHalfIndex n
  (if i = k then 1 + (∑ ell, thetaPartialFirst Δ (p (r i)) (p ell)) / (N : ℝ) else 0) +
    (thetaPartialSecond Δ (p (r i)) (p (r k)) -
      thetaPartialSecond Δ (p (r i)) (p (Fin.rev (r k)))) / (N : ℝ)

section

variable (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ)

/-- The residual `I-T` whose differential is used in Theorem 2.3. -/
noncomputable def discreteBetheResidual :
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
  have hcoord (j : Fin n) : HasDerivAt (fun t : ℝ => p j + t * v j) (v j) 0 := by
    have hm := (hasDerivAt_id 0).mul_const (v j)
    simp_all
  have hterm (ell : Fin n) : HasDerivAt
      (fun t : ℝ => theta Δ (p i + t * v i) (p ell + t * v ell))
      (v i * thetaPartialFirst Δ (p i) (p ell) +
        v ell * thetaPartialSecond Δ (p i) (p ell)) 0 :=
    hasDerivAt_theta_affine hΔ (p i) (p ell) (v i) (v ell)
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ ell : Fin n,
        theta Δ (p i + t * v i) (p ell + t * v ell))
      (∑ ell : Fin n,
        (v i * thetaPartialFirst Δ (p i) (p ell) +
          v ell * thetaPartialSecond Δ (p i) (p ell))) 0 := by
    simpa using (HasDerivAt.fun_sum (u := Finset.univ)
      (fun ell _ => hterm ell))
  let c : ℝ := 2 * Real.pi * discreteBetheIndex n i / (N : ℝ)
  have hbase : HasDerivAt (fun t : ℝ => p i + t * v i - c) (v i) 0 := by
    simp_all
  have hsumdiv := hsum.div_const (N : ℝ)
  have hres := hbase.add hsumdiv
  have hfun : (fun t : ℝ =>
      discreteBetheResidual Δ N n (discreteBetheAffinePath p v t) i) =
      (fun t => p i + t * v i - c) +
        (fun t => (∑ ell : Fin n,
          theta Δ (p i + t * v i) (p ell + t * v ell)) / (N : ℝ)) := by
    funext t
    simp [discreteBetheResidual, discreteBetheAffinePath, discreteBetheMap, c]
    ring
  rw [hfun]
  exact hres

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
  have hgeneral := hasDerivAt_discreteBetheResidual_path (N := N) (n := n) hΔ p v ri
  have hv : v ri = if i = k then 1 else 0 := by
    simpa using discreteSymBasis_at_half i k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_discreteSymBasis_mul, hv] at hgeneral
  convert hgeneral using 1
  dsimp [discreteBetheMatrixA, ri, rk]
  split_ifs <;> ring

end PottsDiscontinuity.Bethe
