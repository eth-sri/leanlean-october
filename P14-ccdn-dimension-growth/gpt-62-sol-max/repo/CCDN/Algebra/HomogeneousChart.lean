/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousMonomials
public import CCDN.Height.PrimitiveIntegerPolynomial
public import Mathlib.Data.Finsupp.Fin
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Restriction to x₀=1 is injective on forms of a fixed homogeneous degree.
Explicit homogenization supplies its inverse on bounded-degree polynomials. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Restriction of a polynomial in `n + 1` variables to the slice `x₀ = h`: the ring homomorphism
sending `X 0` to `C h` and `X i.succ` to `X i`. -/
def homogeneousSlice {R : Type*} [CommRing R] (n : ℕ) (h : R) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  eval₂Hom C (Fin.cons (C h) X)

/-- The dehomogenization at the first coordinate: the ring homomorphism sending `X 0` to `1` and
`X i.succ` to `X i`, which restricts a polynomial in `n + 1` variables to the affine chart
`x₀ = 1`. -/
def affineChart {K : Type*} [CommRing K] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K :=
  eval₂Hom C (Fin.cons 1 X)

@[simp] lemma homogeneousSlice_one {R : Type*} [CommRing R] (n : ℕ) :
    homogeneousSlice (R := R) n 1 = affineChart n := by
  simp [homogeneousSlice, affineChart]

/-- The degree splits into the first exponent and the degree of the tail. -/
lemma exponent_degree_split {n : ℕ} (m : Fin (n + 1) →₀ ℕ) :
    m.sum (fun _ e => e) = m 0 + m.tail.sum (fun _ e => e) := by
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ,
    Finsupp.sum_fintype _ _ (by simp)]
  rfl

private lemma tail_injective_on_degree {n M : ℕ} {m k : Fin (n + 1) →₀ ℕ}
    (hm : m.sum (fun _ e => e) = M) (hk : k.sum (fun _ e => e) = M)
    (he : m.tail = k.tail) : m = k := by
  have h0 : m 0 = k 0 := by
    rw [exponent_degree_split] at hm hk
    aesop
  simpa using congrArg₂ Finsupp.cons h0 he

section

variable {K : Type*} [CommRing K]
include K

/-- The restriction of the monomial `monomial m c` to the slice `x₀ = h` is the monomial with
exponent `chartExponent m` and coefficient `c * h ^ m 0`. -/
lemma homogeneousSlice_monomial {n : ℕ}
    (h : K) (m : Fin (n + 1) →₀ ℕ) (c : K) :
    homogeneousSlice n h (monomial m c) = monomial m.tail (c * h ^ m 0) := by
  change eval₂ C (Fin.cons (C h) X) (monomial m c) = _
  rw [eval₂_monomial, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, map_mul, map_pow, Finsupp.tail_apply]
  ring

/-- The affine chart of a monomial forgets the degree of the first variable. -/
lemma affineChart_monomial {n : ℕ} (m : Fin (n + 1) →₀ ℕ) (c : K) :
    affineChart n (monomial m c) = monomial m.tail c := by
  simpa using homogeneousSlice_monomial (1 : K) m c

/-- For `f` homogeneous of degree `M`, the coefficient of `affineChart n f` at the chart exponent of
a degree-`M` exponent `m` is the coefficient of `f` at `m`. -/
lemma affineChart_homogeneous_coefficient {n M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M)
    (m : Fin (n + 1) →₀ ℕ) (hm : m.degree = M) :
    (affineChart n f).coeff m.tail = f.coeff m := by
  classical
  conv_lhs => rw [f.as_sum, map_sum, coeff_sum]
  simp_rw [affineChart_monomial, coeff_monomial]
  rw [Finset.sum_eq_single m, ite_eq_left rfl]
  · intro k hk hkm
    have hd : k.degree = M := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hf (mem_support_iff.mp hk)
    exact ite_eq_right fun e => hkm (tail_injective_on_degree hd hm e)
  · intro h
    simp [notMem_support_iff.mp h]

/-- Two homogeneous polynomials of the same degree with equal affine charts are equal. -/
lemma affineChart_injective_on_homogeneous {n M : ℕ}
    {f g : MvPolynomial (Fin (n + 1)) K} (hf : f.IsHomogeneous M) (hg : g.IsHomogeneous M)
    (he : affineChart n f = affineChart n g) : f = g := by
  ext m
  by_cases hm : m.degree = M
  · rw [← affineChart_homogeneous_coefficient f hf m hm,
      ← affineChart_homogeneous_coefficient g hg m hm, he]
  · rw [hf.coeff_eq_zero hm, hg.coeff_eq_zero hm]

lemma affineChart_ne_zero_of_homogeneous {n d : ℕ} {f : MvPolynomial (Fin (n + 1)) K}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) : affineChart n f ≠ 0 := fun hz =>
  hf0 (affineChart_injective_on_homogeneous hf (isHomogeneous_zero _ _ _) (by simpa using hz))

/-- Restriction to the affine chart `x₀ = 1` does not increase the total degree. -/
lemma affineChart_totalDegree_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) : (affineChart n f).totalDegree ≤ f.totalDegree := by
  exact linear_eval₂_totalDegree_le (.id K) _ (Fin.cases (by simp) (by simpa using fun i => (isHomogeneous_X K i).totalDegree_le)) f

end

/-- The exponent in `n + 1` variables obtained from `m` by prepending `M - |m|` as the exponent of
the first variable, where `|m|` is the degree of `m`; it has degree `M` when `|m| ≤ M`. -/
def homogenizedExponent {n : ℕ} (M : ℕ) (m : Fin n →₀ ℕ) : Fin (n + 1) →₀ ℕ :=
  m.cons (M - m.sum (fun _ e => e))

@[simp] private lemma tail_homogenizedExponent {n : ℕ} (d : ℕ) (m : Fin n →₀ ℕ) :
    (homogenizedExponent d m).tail = m := Finsupp.tail_cons ..

private lemma homogenizedExponent_degree {n M : ℕ} (m : Fin n →₀ ℕ)
    (hm : m.sum (fun _ e => e) ≤ M) :
    (homogenizedExponent M m).sum (fun _ e => e) = M := by
  rw [exponent_degree_split, tail_homogenizedExponent]
  change M - m.sum (fun _ e => e) + m.sum (fun _ e => e) = M
  omega

private lemma homogenizedExponent_injective {n : ℕ} (d : ℕ) :
    Function.Injective (homogenizedExponent (n := n) d) :=
  fun x y h => by simpa using congrArg Finsupp.tail h

/-- Scaled homogenization in degree `d`: the monomial `x^m` becomes
`h ^ |m| * x₀ ^ (d - |m|) * x^m`. With `h = 1` this is the usual homogenization,
which is a section of `affineChart` (see `affineChart_scaledHomogenize_one`). -/
def scaledHomogenize {R : Type*} [CommRing R] {n : ℕ} (d : ℕ) (h : R)
    (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n + 1)) R :=
  ∑ m ∈ f.support, monomial (homogenizedExponent d m) (h ^ m.sum (fun _ e => e) * f.coeff m)

section

variable {R : Type*} [CommRing R]
include R

/-- The coefficient of `scaledHomogenize d h f` at `homogenizedExponent d m` is
`h ^ |m| * f.coeff m`, where `|m|` is the degree of `m`. -/
lemma scaledHomogenize_coefficient {n : ℕ}
    (d : ℕ) (h : R) (f : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ) :
    (scaledHomogenize d h f).coeff (homogenizedExponent d m) =
      h ^ m.sum (fun _ e => e) * f.coeff m := by
  classical
  by_cases hm : m ∈ f.support <;>
    simp_all [scaledHomogenize, coeff_monomial, (homogenizedExponent_injective d).eq_iff]

/-- If `f` has total degree at most `d`, then its scaled homogenization in degree `d` is homogeneous
of degree `d`. -/
lemma scaledHomogenize_homogeneous {n d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ d) :
    (scaledHomogenize d h f).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro m hm
  exact isHomogeneous_monomial _ (homogenizedExponent_degree m ((le_totalDegree hm).trans hf))

/-- Homogenization in degree `d`, that is scaled homogenization with `h = 1`, is a right inverse of
the affine chart `x₀ = 1`. -/
lemma affineChart_scaledHomogenize_one {n : ℕ}
    (d : ℕ) (f : MvPolynomial (Fin n) R) : affineChart n (scaledHomogenize d 1 f) = f := by
  simp [scaledHomogenize, map_sum, affineChart_monomial, tail_homogenizedExponent, one_pow, one_mul]

/-- If `f` has total degree at most `d`, then restricting the scaled homogenization
`scaledHomogenize d h f` to the slice `x₀ = h` gives `C (h ^ d) * f`. -/
lemma homogeneousSlice_scaledHomogenize {n d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ d) :
    homogeneousSlice n h (scaledHomogenize d h f) = C (h ^ d) * f := by
  classical
  rw [scaledHomogenize, map_sum]
  conv_rhs => rw [f.as_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [homogeneousSlice_monomial, tail_homogenizedExponent, C_mul_monomial]
  congr 1
  change (h ^ m.sum (fun _ e => e) * f.coeff m) * h ^ (d - m.sum (fun _ e => e)) = h ^ d * f.coeff m
  calc
    _ = (h ^ m.sum (fun _ e => e) * h ^ (d - m.sum (fun _ e => e))) * f.coeff m := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le ((le_totalDegree hm).trans hf)]

end

/-- Evaluating the restriction of `f` to the slice `x₀ = h` at `x` is evaluating `f` at the point
`Fin.cons h x`. -/
lemma homogeneousSlice_eval {R : Type*} [CommRing R] {n : ℕ}
    (h : R) (f : MvPolynomial (Fin (n + 1)) R) (x : Fin n → R) :
    eval x (homogeneousSlice n h f) = eval (Fin.cons h x) f := by
  change eval x (eval₂ C (Fin.cons (C h) X) f) = _
  rw [← eval_assoc]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma homogeneousSlice_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (h : R) (f : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.map φ (homogeneousSlice n h f) =
      homogeneousSlice n (φ h) (MvPolynomial.map φ f) := by
  simp only [homogeneousSlice, coe_eval₂Hom, map_eval₂]
  congr 1
  funext i
  exact Fin.cases (by simp) (by simp) i

lemma affineChart_map {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (φ : K →+* L) (f : MvPolynomial (Fin (n + 1)) K) :
    affineChart n (MvPolynomial.map φ f) = MvPolynomial.map φ (affineChart n f) := by
  simpa using (homogeneousSlice_map φ 1 f).symm

lemma affineChart_eval {K : Type*} [CommRing K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (x : Fin n → K) :
    eval x (affineChart n f) = eval (Fin.cons 1 x) f := by
  simpa using homogeneousSlice_eval 1 f x

/-- Evaluation at `(h,x)` of a scaled homogenization equals `h^d` times the original value. -/
theorem scaledHomogenize_eval {R : Type*} [CommRing R] {n d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ d) (x : Fin n → R) :
    eval (Fin.cons h x) (scaledHomogenize d h f) = h ^ d * eval x f := by
  rw [← homogeneousSlice_eval, homogeneousSlice_scaledHomogenize _ _ hf, eval_mul, eval_C]

/-- Over a domain, the scaled homogenization of a nonzero polynomial with a nonzero scaling
factor `h` is nonzero. -/
lemma scaledHomogenize_ne_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (d : ℕ) {h : R} (hh : h ≠ 0) {f : MvPolynomial (Fin n) R} (hf : f ≠ 0) :
    scaledHomogenize d h f ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  intro hz
  have hc := scaledHomogenize_coefficient d h f m
  simp_all

/-- Divisibility of affine charts lifts to homogeneous divisibility when the
first equation retains its degree on the chart. -/
theorem homogeneous_dvd_of_affineChart_dvd {K : Type*} [CommRing K] [IsDomain K]
    {n d M : ℕ} {f g : MvPolynomial (Fin (n + 1)) K}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hg : g.IsHomogeneous M)
    (hdchart : (affineChart n f).totalDegree = d)
    (hdiv : affineChart n f ∣ affineChart n g) : f ∣ g := by
  have hcf := affineChart_ne_zero_of_homogeneous hf hf0
  by_cases hg0 : g = 0
  · simp [hg0]
  have hcg := affineChart_ne_zero_of_homogeneous hg hg0
  obtain ⟨q, hq⟩ := hdiv
  have hq0 : q ≠ 0 := by simp_all
  have hdeg : d + q.totalDegree ≤ M := by
    have hh := (affineChart_totalDegree_le g).trans hg.totalDegree_le
    rw [hq, totalDegree_mul_of_isDomain hcf hq0, hdchart] at hh
    exact hh
  have hdM : d ≤ M := by omega
  refine ⟨scaledHomogenize (M - d) 1 q, ?_⟩
  apply affineChart_injective_on_homogeneous hg
  · simpa only [Nat.add_sub_of_le hdM] using
      hf.mul (scaledHomogenize_homogeneous 1 q (show q.totalDegree ≤ M - d by omega))
  · rw [map_mul, affineChart_scaledHomogenize_one]
    exact hq

/-- Dehomogenize after moving the chosen pivot to coordinate zero. -/
def affineChartAt {K : Type*} [CommRing K] {n : ℕ} (k : Fin (n + 1))
    (f : MvPolynomial (Fin (n + 1)) K) : MvPolynomial (Fin n) K :=
  affineChart n (rename (Equiv.swap 0 k) f)

lemma affineChartAt_eval {K : Type*} [CommRing K] {n : ℕ} (k : Fin (n + 1))
    (f : MvPolynomial (Fin (n + 1)) K) (a : Fin n → K) :
    eval a (affineChartAt k f) = eval (Fin.cons 1 a ∘ Equiv.swap 0 k) f := by
  rw [affineChartAt, affineChart_eval, eval_rename]

@[simp] lemma map_affineChartAt {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (φ : K →+* L) (k : Fin (n + 1)) (f : MvPolynomial (Fin (n + 1)) K) :
    map φ (affineChartAt k f) = affineChartAt k (map φ f) := by
  rw [affineChartAt, ← affineChart_map, map_rename, affineChartAt]

end
end CCDN
