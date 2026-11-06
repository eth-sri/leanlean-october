module

public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.Bethe.DiscreteCore

/-!
# Symmetric products in the two Bethe eigenvalue formulas

Source: Section 3.2 of arXiv:1611.09877v2 (proof of Theorem 1.3): the formula
`Λ₀(N) = 2 ∏ |M(e^{i p_j})|` in the proof of (1.6), and the factorization of
`Λ_r(N) / Λ₀(N)` in the proof of (1.7) for odd `r`. These are scalar identities; no claim
identifying a scalar with a transfer-matrix eigenvalue is needed here.
-/

public section

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

theorem ratio_z_neg (x : ℝ) : z (-x) = conj (z x) := by
  rw [z, z, ← Complex.exp_conj]
  simp

section
variable (c x : ℝ)
theorem ratio_M_neg  : M c (z (-x)) = conj (M c (z x)) := by
  simp [M, ratio_z_neg]

theorem ratio_L_eq_M_neg  : L c (z x) = M c (z (-x)) := by
  have hz := z_ne_zero x
  have hneg : z (-x) = (z x)⁻¹ := by
    simp only [z, Complex.ofReal_neg, mul_neg, Complex.exp_neg]
  grind [z, L, M]
end

theorem ratio_M_ne_zero {c : ℝ} (hc : 2 < c) (x : ℝ) : M c (z x) ≠ 0 := by
  by_cases hx : z x = 1
  · simp_all [M]
  · exact M_ne_zero hc hx

/-- Pairing complex conjugates yields a positive real product; fixed points
are allowed exactly when their factor is already its nonnegative modulus. -/
theorem ratio_prod_eq_prod_norm {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ) (g : ι → ι)
    (hmem : ∀ i ∈ s, g i ∈ s) (hinv : ∀ i ∈ s, g (g i) = i)
    (hconj : ∀ i ∈ s, f (g i) = conj (f i))
    (hne : ∀ i ∈ s, f i ≠ 0)
    (hfix : ∀ i ∈ s, g i = i → f i = (‖f i‖ : ℂ)) :
    (∏ i ∈ s, f i) = ((∏ i ∈ s, ‖f i‖ : ℝ) : ℂ) := by
  have hnorm (i : ι) (hi : i ∈ s) : (‖f i‖ : ℂ) ≠ 0 := by
    simp_all
  have hprod : ∏ i ∈ s, f i / (‖f i‖ : ℂ) = 1 := by
    apply Finset.prod_involution (fun i _ => g i)
    · intro i hi
      rw [hconj i hi, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj', pow_two]
      simp_all
    · grind
    · omega
    omega
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.mpr hnorm)] at hprod
  simp_all

section
variable {n : ℕ} {p : Fin n → ℝ} {c : ℝ} (hc : 2 < c) (hp : p ∈ S_n n)
include hc hp
/-- The product of `M` factors for a symmetric ordered configuration is
positive real, including when the total definition is evaluated at zero. -/
theorem ratio_symmetric_M_product  :
    (∏ j, M c (z (p j))) = ((∏ j, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
  apply ratio_prod_eq_prod_norm univ _ Fin.rev
  · simp
  · simp
  · intro i hi
    rw [show p (Fin.rev i) = -p i from hp.2.2 i, ratio_M_neg]
  · simp_all [ratio_M_ne_zero]
  · intro i hi hfix
    have hs := hp.2.2 i
    rw [hfix] at hs
    have hz : p i = 0 := by linarith
    simp_all [M]

/-- The regular expression, for the even-root branch of the source. -/
theorem ratio_eigenvalueRegular  :
    eigenvalueRegular c p = ((2 * ∏ j, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
  have hL : (∏ j, L c (z (p j))) = ∏ j, M c (z (p j)) := by
    calc
      _ = ∏ j, M c (z (p (Fin.rev j))) := by
        apply prod_congr rfl
        intro j hj
        rw [show p (Fin.rev j) = -p j from hp.2.2 j, ratio_L_eq_M_neg]
      _ = _ := Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun j => M c (z (p j)))
  rw [eigenvalueRegular, hL, ratio_symmetric_M_product hc hp]
  push_cast
  ring

/-- Pairing after removing the zero root gives the modulus product appearing
in the odd branch, without an extra factor of two. -/
theorem ratio_zero_erased_M_product (l : Fin n) (hl : p l = 0) :
    (∏ j ∈ univ.erase l, M c (z (p j))) =
      ((∏ j ∈ univ.erase l, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
  have hlrev : Fin.rev l = l := hp.2.1.injective (by rw [hp.2.2 l, hl, neg_zero])
  apply ratio_prod_eq_prod_norm (univ.erase l) _ Fin.rev
  · grind
  · simp
  · intro j hj
    rw [show p (Fin.rev j) = -p j from hp.2.2 j, ratio_M_neg]
  · simp_all [ratio_M_ne_zero]
  grind
end

/-- Exact real form of the source zero-root expression. -/
theorem ratio_eigenvalueZero {N n : ℕ} {p : Fin n → ℝ}
    {c : ℝ} (hc : 2 < c) (hp : p ∈ S_n n) (l : Fin n) (hl : p l = 0) :
    eigenvalueZero N c p l =
      (((2 + c ^ 2 * ((N : ℝ) - 1) + c ^ 2 *
        ∑ j ∈ univ.erase l, deriv (fun t => theta (anisotropy c) t (p j)) 0) *
        ∏ j ∈ univ.erase l, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
  have hd (j : Fin n) :=
    (analyticAt_theta_left (anisotropy_lt_neg_one hc) 0 (p j)).differentiableAt.hasDerivAt.ofReal_comp.deriv
  simp_all [eigenvalueZero, ratio_zero_erased_M_product]

end PottsDiscontinuity.Bethe
