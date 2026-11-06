/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The coefficient `ℓ¹`-norm of integer multivariate polynomials

`MvPolynomial.l1Norm f` is the sum of the absolute values of the coefficients of an integer
polynomial `f`, as a natural number.

## Main results

* `MvPolynomial.l1Norm_add_le`, `MvPolynomial.l1Norm_mul_le`, `MvPolynomial.l1Norm_sum_le`,
  `MvPolynomial.l1Norm_prod_le`, `MvPolynomial.l1Norm_pow_le`: the norm is subadditive and
  submultiplicative.
* `MvPolynomial.l1Norm_det_le`: the norm of a determinant is at most `n! * L ^ n` when every
  entry has norm at most `L`.
* `MvPolynomial.l1Norm_rename_le`: renaming variables does not increase the norm.
* `MvPolynomial.l1Norm_coeff_le_l1Norm_sumAlgEquiv_symm`: a coefficient of a polynomial with
  polynomial coefficients has norm at most that of the flattened polynomial.
-/

@[expose] public section

namespace MvPolynomial

variable {σ : Type*}

/-- The sum of the absolute values of all coefficients of an integer polynomial. -/
def l1Norm (f : MvPolynomial σ ℤ) : ℕ :=
  f.support.sum fun m => (f.coeff m).natAbs

/-- The zero polynomial has `ℓ¹`-norm zero. -/
@[simp] lemma l1Norm_zero : l1Norm (0 : MvPolynomial σ ℤ) = 0 := by
  simp [l1Norm]

/-- Each coefficient of `f` has absolute value at most the `ℓ¹`-norm of `f`. -/
lemma natAbs_coeff_le_l1Norm (f : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    (f.coeff m).natAbs ≤ l1Norm f := by
  classical
  by_cases hm : m ∈ f.support
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (f.coeff j).natAbs) hm
  · simp [notMem_support_iff.mp hm]

/-- The `ℓ¹`-norm of the monomial `monomial m c` is the absolute value of `c`. -/
@[simp] lemma l1Norm_monomial (m : σ →₀ ℕ) (c : ℤ) :
    l1Norm (monomial m c) = c.natAbs := by
  classical
  by_cases hc : c = 0 <;> simp [l1Norm, hc, support_monomial]

/-- The `ℓ¹`-norm of the constant polynomial `C c` is the absolute value of `c`. -/
@[simp] lemma l1Norm_C (c : ℤ) :
    l1Norm (C c : MvPolynomial σ ℤ) = c.natAbs :=
  l1Norm_monomial 0 c

/-- The constant polynomial `1` has `ℓ¹`-norm one. -/
@[simp] lemma l1Norm_one : l1Norm (1 : MvPolynomial σ ℤ) = 1 := by
  simpa using l1Norm_C (σ := σ) 1

/-- The `ℓ¹`-norm is subadditive. -/
lemma l1Norm_add_le (f g : MvPolynomial σ ℤ) :
    l1Norm (f + g) ≤ l1Norm f + l1Norm g := by
  classical
  have h (p : MvPolynomial σ ℤ) (hs : p.support ⊆ f.support ∪ g.support) :
      l1Norm p = ∑ m ∈ f.support ∪ g.support, (p.coeff m).natAbs :=
    Finset.sum_subset hs fun m _ hm => by simp [notMem_support_iff.mp hm]
  rw [h (f + g) support_add, h f Finset.subset_union_left, h g Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by simpa using Int.natAbs_add_le (f.coeff m) (g.coeff m)

/-- The `ℓ¹`-norm of a finite sum is at most the sum of the `ℓ¹`-norms of the summands. -/
lemma l1Norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (l1Norm_add_le (f i) (∑ j ∈ s, f j)).trans (Nat.add_le_add_left ih _)

/-- The `ℓ¹`-norm is submultiplicative. -/
lemma l1Norm_mul_le (f g : MvPolynomial σ ℤ) :
    l1Norm (f * g) ≤ l1Norm f * l1Norm g := by
  classical
  rw [show f * g = ∑ m ∈ f.support, ∑ n ∈ g.support,
      monomial m (f.coeff m) * monomial n (g.coeff n) by
    conv_lhs => rw [f.as_sum, g.as_sum]
    rw [Finset.sum_mul]; simp only [Finset.mul_sum]]
  refine ((l1Norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => l1Norm_sum_le _ _)).trans_eq ?_
  simp only [monomial_mul_monomial, l1Norm_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, l1Norm]

/-- The `ℓ¹`-norm of a finite product is at most the product of the `ℓ¹`-norms of the factors. -/
lemma l1Norm_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1Norm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (l1Norm_mul_le (f i) (∏ j ∈ s, f j)).trans (Nat.mul_le_mul_left _ ih)

/-- The `ℓ¹`-norm of `f ^ n` is at most the `n`-th power of the `ℓ¹`-norm of `f`. -/
lemma l1Norm_pow_le {σ : Type*} (f : MvPolynomial σ ℤ) (n : ℕ) :
    l1Norm (f ^ n) ≤ l1Norm f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (l1Norm_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

/-- If every entry of a square matrix `M` of integer polynomials has `ℓ¹`-norm at most `L`, then the
determinant of `M` has `ℓ¹`-norm at most `n! * L ^ n`, where `n` is the size of `M`. -/
lemma l1Norm_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℤ)) (L : ℕ)
    (hM : ∀ i j, l1Norm (M i j) ≤ L) :
    l1Norm M.det ≤ (Fintype.card ι).factorial * L ^ Fintype.card ι := by
  classical
  rw [Matrix.det_apply]
  refine (l1Norm_sum_le _ _).trans
    ((Finset.sum_le_sum fun p _ => (?_ : _ ≤ L ^ Fintype.card ι)).trans_eq
      (by simp [Fintype.card_perm]))
  have hu : l1Norm (p.sign • ∏ i, M (p i) i) = l1Norm (∏ i, M (p i) i) := by
    rcases Int.units_eq_one_or p.sign with h | h <;> { rw [h]; simp [l1Norm] }
  rw [hu]
  exact (l1Norm_prod_le _ _).trans
    (by simpa using Finset.prod_le_prod fun i (_ : i ∈ Finset.univ) => hM (p i) i)

/-- Extracting one outer coefficient never increases the total coefficient
sum after flattening the two variable families. -/
theorem l1Norm_coeff_le_l1Norm_sumAlgEquiv_symm {σ τ : Type*}
    (f : MvPolynomial σ (MvPolynomial τ ℤ)) (m : σ →₀ ℕ) :
    l1Norm (f.coeff m) ≤ l1Norm ((sumAlgEquiv ℤ σ τ).symm f) := by
  classical
  let e : (τ →₀ ℕ) → (σ ⊕ τ →₀ ℕ) :=
    fun n => Finsupp.sumFinsuppAddEquivProdFinsupp.symm (m, n)
  have hc (n : τ →₀ ℕ) : ((sumAlgEquiv ℤ σ τ).symm f).coeff (e n) = (f.coeff m).coeff n := by
    simp [e, sumAlgEquiv, AddMonoidAlgebra.curryAlgEquiv,
      AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv]; rfl
  have hinj : Function.Injective e := fun _ _ h =>
    congrArg Prod.snd (Finsupp.sumFinsuppAddEquivProdFinsupp.symm.injective h)
  have hs : (f.coeff m).support.image e ⊆ ((sumAlgEquiv ℤ σ τ).symm f).support := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    rw [mem_support_iff, hc]
    exact mem_support_iff.mp hn
  have hsum : l1Norm (f.coeff m) =
      ∑ a ∈ (f.coeff m).support.image e, (((sumAlgEquiv ℤ σ τ).symm f).coeff a).natAbs := by
    rw [Finset.sum_image fun _ _ _ _ h => hinj h]
    simp only [hc, l1Norm]
  rw [hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => Nat.zero_le _

/-- One original coefficient variable multiplying an integer parameter
polynomial has no coefficient-norm cost beyond that parameter polynomial. -/
theorem l1Norm_sumAlgEquiv_symm_C_X_mul_map_C_le {σ τ : Type*}
    (p : MvPolynomial σ ℤ) (i : τ) :
    l1Norm ((sumAlgEquiv ℤ σ τ).symm
      (C (X i) * map (C : ℤ →+* MvPolynomial τ ℤ) p)) ≤ l1Norm p := by
  classical
  have hmap : (sumAlgEquiv ℤ σ τ).symm (map (C : ℤ →+* MvPolynomial τ ℤ) p) =
      rename Sum.inl p :=
    (AlgEquiv.symm_apply_eq _).mpr
      (DFunLike.congr_fun (sumAlgEquiv_comp_rename_inl (R := ℤ) (S₁ := σ) (S₂ := τ)) p).symm
  rw [map_mul, sumAlgEquiv_symm_C_X, hmap]
  refine (l1Norm_mul_le _ _).trans ?_
  rw [X, l1Norm_monomial, Int.natAbs_one, one_mul,
    show rename Sum.inl p = ∑ m ∈ p.support, monomial (m.mapDomain Sum.inl) (p.coeff m) by
      conv_lhs => rw [p.as_sum]
      simp only [map_sum, rename_monomial]]
  exact (l1Norm_sum_le _ _).trans_eq (by simp only [l1Norm_monomial]; rfl)

end MvPolynomial
