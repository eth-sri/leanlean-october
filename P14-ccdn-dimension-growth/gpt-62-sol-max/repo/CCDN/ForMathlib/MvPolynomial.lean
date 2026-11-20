/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Degrees, homogeneous components and dimensions of homogeneous submodules

## Main results

* `MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_left`: multiplication by a
  homogeneous polynomial of degree `d` shifts homogeneous components by `d`.
* `MvPolynomial.finrank_homogeneousSubmodule`: over a field, the homogeneous polynomials of
  degree `n` in finitely many variables `σ` form a space of dimension
  `(Fintype.card σ + n - 1).choose n`.
* `MvPolynomial.finrank_homogeneousSubmodule_fin`: the same count for `n + 1` variables, in the
  form `(n + M).choose M`.
* `Sym.equivNatSumLeOfFintype`, `Finsupp.degreeLeEquivSym`: exponent vectors of degree at most
  `n` on `α` are multisets of size `n` on `Option α`.
* `MvPolynomial.finrank_restrictTotalDegree`: over a field, the polynomials of total degree at
  most `N` in finitely many variables `σ` form a space of dimension
  `(Fintype.card σ + N).choose N`.
* `MvPolynomial.degreeOf_aeval_le`: substituting polynomials of degree at most `D` in a variable
  `i` into `f` gives degree at most `D * f.totalDegree` in `i`. Since each matrix entry occurs to
  degree at most one in every maximal minor, substituting maximal minors preserves a degree bound
  in every individual matrix coordinate.
* `MvPolynomial.totalDegree_map_of_injective`: mapping coefficients along an injective ring
  homomorphism preserves the total degree.
* `MvPolynomial.totalDegree_pos_of_ne_zero_of_not_isUnit`: over a field, a nonzero nonunit has
  positive total degree.
* `MvPolynomial.homogeneousComponent_totalDegree_ne_zero`: the homogeneous component of top
  degree of a nonzero polynomial is nonzero.
-/

@[expose] public section

namespace Sym

variable (α : Type*) [DecidableEq α] [Fintype α] (n : ℕ)

/-- Multisets of size `n` on `Option α` correspond to functions `α → ℕ` with sum at most `n`;
the multiplicity of `none` records the slack. -/
noncomputable def equivNatSumLeOfFintype : Sym (Option α) n ≃ {P : α → ℕ // ∑ i, P i ≤ n} :=
  (equivNatSumOfFintype (Option α) n).trans
    (show {P : Option α → ℕ // ∑ i, P i = n} ≃ {P : α → ℕ // ∑ i, P i ≤ n} from
    { toFun q := ⟨fun i ↦ q.val (some i), by
        have h := q.property
        rw [Fintype.sum_option] at h
        change ∑ i, q.val (some i) ≤ n
        omega⟩
      invFun p := ⟨fun j ↦ j.elim (n - ∑ i, p.val i) p.val, by
        simp only [Fintype.sum_option, Option.elim_none, Option.elim_some]
        exact Nat.sub_add_cancel p.property⟩
      left_inv q := by
        apply Subtype.ext
        funext j
        cases j with
        | none =>
          have h := q.property
          rw [Fintype.sum_option] at h
          dsimp
          omega
        | some j => rfl
      right_inv p := rfl })

end Sym

namespace Finsupp

/-- Exponents of degree `n` correspond to multisets of cardinality `n`. -/
noncomputable def degreeEqEquivSym (σ : Type*) [DecidableEq σ] [Fintype σ] (n : ℕ) :
    {p : σ →₀ ℕ // p.degree = n} ≃ Sym σ n :=
  (equivFunOnFinite.subtypeEquiv (fun p => by simp [degree_eq_sum])).trans
    (Sym.equivNatSumOfFintype σ n).symm

lemma card_degree_eq (σ : Type*) [Fintype σ] (n : ℕ) :
    Nat.card {p : σ →₀ ℕ // p.degree = n} = (Fintype.card σ + n - 1).choose n := by
  classical
  rw [Nat.card_congr (degreeEqEquivSym σ n), Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]

/-- Exponent vectors of degree at most `n` on a finite type `α` correspond to multisets of
size `n` on `Option α`. -/
noncomputable def degreeLeEquivSym (α : Type*) [DecidableEq α] [Fintype α] (n : ℕ) :
    {P : α →₀ ℕ // P.degree ≤ n} ≃ Sym (Option α) n :=
  (equivFunOnFinite.subtypeEquiv fun P ↦ by simp [degree_eq_sum]).trans
    (Sym.equivNatSumLeOfFintype α n).symm

end Finsupp

namespace MvPolynomial

variable {σ K : Type*}

section TotalDegree

/-- Substitution of polynomials of degree at most `n` multiplies total degree by at most `n`. -/
theorem eval₂Hom_totalDegree_le_mul {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (g : σ → MvPolynomial τ S) {n : ℕ} (hg : ∀ j, (g j).totalDegree ≤ n)
    (f : MvPolynomial σ R) :
    (eval₂Hom (C.comp φ) g f).totalDegree ≤ n * f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial, RingHom.comp_apply]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  calc
    _ ≤ ∑ j ∈ e.support, (g j ^ e j).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ j ∈ e.support, e j * n := Finset.sum_le_sum fun j _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg j))
    _ = n * e.degree := by
      change ∑ j ∈ e.support, e j * n = n * ∑ j ∈ e.support, e j
      rw [← Finset.sum_mul, Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (le_totalDegree he)


variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Mapping coefficients never increases the total degree. -/
theorem totalDegree_map_le (f : R →+* S) (p : MvPolynomial σ R) :
    (map f p).totalDegree ≤ p.totalDegree :=
  Finset.sup_mono (support_map_subset _ _)

/-- Mapping coefficients along an injective ring homomorphism preserves the total degree. -/
theorem totalDegree_map_of_injective {f : R →+* S} (hf : Function.Injective f)
    (p : MvPolynomial σ R) : (map f p).totalDegree = p.totalDegree := by
  simp only [totalDegree, support_map_of_injective p hf]

/-- Over a field, a nonzero polynomial which is not a unit has positive total degree. -/
theorem totalDegree_pos_of_ne_zero_of_not_isUnit [Field K] {f : MvPolynomial σ K} (hf : f ≠ 0)
    (hu : ¬IsUnit f) : 0 < f.totalDegree := by
  refine Nat.pos_of_ne_zero fun hd ↦ hu ?_
  rw [totalDegree_eq_zero_iff_eq_C.mp hd] at hf ⊢
  exact (isUnit_iff_ne_zero.mpr fun h ↦ hf (by rw [h, map_zero])).map C

/-- Over a field, an irreducible polynomial has positive total degree. -/
theorem totalDegree_pos_of_irreducible [Field K] {f : MvPolynomial σ K} (hf : Irreducible f) :
    0 < f.totalDegree :=
  totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit

/-- The homogeneous component of top degree of a nonzero polynomial is nonzero. -/
theorem homogeneousComponent_totalDegree_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    (fun s => s.degree)
  have hdeg : m.degree = p.totalDegree := hd.symm
  intro h
  have hc := congrArg (fun g : MvPolynomial σ R => g.coeff m) h
  rw [coeff_homogeneousComponent, ite_eq_left hdeg] at hc
  exact (mem_support_iff.mp hm) hc

end TotalDegree

/-- Multiplication by a homogeneous polynomial of degree `d` shifts homogeneous components
by `d`. -/
theorem homogeneousComponent_mul_of_isHomogeneous_left [CommRing K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (u : MvPolynomial σ K) (k : ℕ) :
    homogeneousComponent (d + k) (f * u) = f * homogeneousComponent k u := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  have ht := DirectSum.coe_decompose_mul_add_of_left_mem
    (homogeneousSubmodule σ K) (j := k) hf (b := u)
  simpa only [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] using ht

/-- The homogeneous polynomials of degree `n` in finitely many variables `σ` form a space of
dimension `(Fintype.card σ + n - 1).choose n`, the number of monomials of degree `n`. -/
theorem finrank_homogeneousSubmodule [Field K] [Fintype σ] (n : ℕ) :
    Module.finrank K (homogeneousSubmodule σ K n) = (Fintype.card σ + n - 1).choose n := by
  classical
  have he : homogeneousSubmodule σ K n = restrictSupport K {p | p.degree = n} := by
    rw [homogeneousSubmodule_eq_finsupp_supported]
    rfl
  rw [he, Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  exact Finsupp.card_degree_eq σ n

/-- The polynomials of total degree at most `N` in finitely many variables `σ` form a space of
dimension `(Fintype.card σ + N).choose N`, the number of monomials of degree at most `N`. -/
theorem finrank_restrictTotalDegree [Field K] [Fintype σ] (N : ℕ) :
    Module.finrank K (restrictTotalDegree σ K N) = (Fintype.card σ + N).choose N := by
  classical
  have he : restrictTotalDegree σ K N = restrictSupport K {p | p.degree ≤ N} := rfl
  rw [he, Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  change Nat.card {p : σ →₀ ℕ // p.degree ≤ N} = _
  rw [Nat.card_congr (Finsupp.degreeLeEquivSym σ N), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_option]
  congr 1
  omega

/-- The homogeneous polynomials of degree `M` in `n + 1` variables form a space of dimension
`(n + M).choose M`. -/
theorem finrank_homogeneousSubmodule_fin [Field K] (n M : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (n + 1)) K M) = (n + M).choose M := by
  rw [finrank_homogeneousSubmodule, Fintype.card_fin]
  congr 1
  omega

end MvPolynomial

@[expose] public section
namespace CCDN

open MvPolynomial in
/-- Substituting homogeneous linear forms commutes with taking homogeneous components: the
degree-`N` component of `aeval a p` is `aeval a` of the degree-`N` component of `p`. -/
lemma homogeneousComponent_aeval_linear {K σ τ : Type*} [CommSemiring K]
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (N : ℕ) (p : MvPolynomial σ K) :
    homogeneousComponent N (aeval a p) = aeval a (homogeneousComponent N p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp_all
  | monomial e c =>
    have h := isHomogeneous_monomial c (rfl : e.degree = e.degree)
    have h' : (aeval a (monomial e c)).IsHomogeneous e.degree := by
      simpa using h.aeval a ha
    rw [homogeneousComponent_of_mem h, homogeneousComponent_of_mem h']
    split_ifs <;> simp


open MvPolynomial in
/-- Substituting affine linear polynomials does not increase total degree. -/
theorem linear_eval₂_totalDegree_le {R S σ τ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : σ → MvPolynomial τ S) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (f : MvPolynomial σ R) :
    (eval₂Hom (C.comp φ) g f).totalDegree ≤ f.totalDegree := by
  simpa only [one_mul] using eval₂Hom_totalDegree_le_mul φ g hg f


/-- A multivariate polynomial over a field whose image under a field homomorphism is irreducible
is itself irreducible. -/
lemma mvPolynomial_irreducible_of_field_map
    {F K σ : Type*} [Field F] [Field K] (φ : F →+* K)
    (f : MvPolynomial σ F) (hf : Irreducible (MvPolynomial.map φ f)) : Irreducible f := by
  have hunit (q : MvPolynomial σ F) (hq : IsUnit (MvPolynomial.map φ q)) : IsUnit q := by
    obtain ⟨hc, hd⟩ := MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hq
    have he :=
      MvPolynomial.totalDegree_map_of_injective φ.injective q
    apply MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr
    refine ⟨isUnit_iff_ne_zero.mpr ?_, he ▸ hd⟩
    intro hz
    apply hc.ne_zero
    rw [MvPolynomial.coeff_map, hz, map_zero]
  refine ⟨fun h => hf.not_isUnit (h.map (MvPolynomial.map φ)), ?_⟩
  intro g h he
  have hh := hf.isUnit_or_isUnit (by rw [he, map_mul])
  exact hh.imp (hunit g) (hunit h)

open MvPolynomial

/-- Evaluating the composite `g ∘ τ` of a polynomial map `τ` and a polynomial `g` at `z` is
evaluating `g` at `τ(z)`. -/
lemma eval_polynomial_coordinate_map {R σ τ : Type*} [CommSemiring R]
    (q : σ → MvPolynomial τ R) (f : MvPolynomial σ R) (z : τ → R) :
    eval z (aeval q f) = eval (fun j => eval z (q j)) f :=
  (eval_assoc q z f).symm

/-- If `x ≡ y` coordinatewise modulo `q`, then `f(x) ≡ f(y)` modulo `q` for every integer polynomial
`f`. -/
lemma dvd_eval_sub_of_dvd_coordinates {σ : Type*} (q : ℤ)
    (x y : σ → ℤ) (hxy : ∀ j, q ∣ x j - y j) (f : MvPolynomial σ ℤ) :
    q ∣ eval x f - eval y f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg =>
    simpa only [eval_add, add_sub_add_comm] using dvd_add hf hg
  | mul_X f j hf =>
    rw [eval_mul, eval_mul, eval_X, eval_X]
    have he : eval x f * x j - eval y f * y j =
        (eval x f - eval y f) * x j + eval y f * (x j - y j) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hf _) (dvd_mul_of_dvd_right (hxy j) _)

end CCDN
