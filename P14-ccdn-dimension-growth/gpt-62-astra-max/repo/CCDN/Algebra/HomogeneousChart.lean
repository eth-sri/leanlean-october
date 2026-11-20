/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousMonomials
public import CCDN.Height.PrimitiveIntegerPolynomial
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Restriction to x₀=1 is injective on forms of a fixed homogeneous degree.
Explicit homogenization supplies its inverse on bounded-degree polynomials. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K R : Type*} [CommRing R] {L : Type*} [CommRing K] {n M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (m : Fin (n + 1) →₀ ℕ) (d : ℕ) (h : R)

/-- The dehomogenization at the first coordinate: the ring homomorphism sending `X 0` to `1` and
`X i.succ` to `X i`, which restricts a polynomial in `n + 1` variables to the affine chart
`x₀ = 1`. -/
def affineChart (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K :=
  eval₂Hom C (Fin.cons 1 X)

/-- The exponent in `n` variables obtained from an exponent `m` in `n + 1` variables by forgetting
the exponent of the first variable. -/
def chartExponent : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m i.succ)

/-- The entry of `chartExponent m` at `i` is the entry of `m` at `i.succ`. -/
@[simp] lemma chartExponent_apply (i : Fin n) :
    chartExponent m i = m i.succ := rfl

/-- The degree of an exponent `m` in `n + 1` variables is the exponent of the first variable plus
the degree of `chartExponent m`. -/
lemma exponent_degree_split :
    m.sum (fun _ e => e) = m 0 + (chartExponent m).sum (fun _ e => e) := by
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ,
    Finsupp.sum_fintype _ _ (by simp)]
  rfl

private lemma chartExponent_injective_on_degree {m k : Fin (n + 1) →₀ ℕ}
    (hm : m.sum (fun _ e => e) = M) (hk : k.sum (fun _ e => e) = M)
    (he : chartExponent m = chartExponent k) : m = k := by
  have h0 : m 0 = k 0 := by
    grind [exponent_degree_split]
  ext i
  refine Fin.cases h0 (fun j => ?_) i
  exact congrArg (fun t => t j) he

/-- The affine chart of the monomial `monomial m c` is the monomial
`monomial (chartExponent m) c`. -/
lemma affineChart_monomial (c : K) :
    affineChart n (monomial m c) = monomial (chartExponent m) c := by
  change eval₂ C (Fin.cons 1 X) (monomial m c) = _
  rw [eval₂_monomial, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
  simp

/-- For `f` homogeneous of degree `M`, the coefficient of `affineChart n f` at the chart exponent of
a degree-`M` exponent `m` is the coefficient of `f` at `m`. -/
lemma affineChart_homogeneous_coefficient (hf : f.IsHomogeneous M)
    (j : Fin ((n + M).choose M)) :
    (affineChart n f).coeff (chartExponent (homogeneousMonomials n M j)) =
      f.coeff (homogeneousMonomials n M j) := by
  classical
  have hinj : Function.Injective (fun j => chartExponent (homogeneousMonomials n M j)) := by
    intro j k he
    solve_by_elim [homogeneousMonomials_injective, chartExponent_injective_on_degree, homogeneousMonomials_degree]
  conv_lhs => rw [homogeneous_eq_sum_coeff f hf]
  simp [affineChart_monomial, hinj.eq_iff]

/-- Two homogeneous polynomials of the same degree with equal affine charts are equal. -/
lemma affineChart_injective_on_homogeneous
    {f g : MvPolynomial (Fin (n + 1)) K} (hf : f.IsHomogeneous M) (hg : g.IsHomogeneous M)
    (he : affineChart n f = affineChart n g) : f = g := by
  have hc : ∀ j, f.coeff (homogeneousMonomials n M j) = g.coeff (homogeneousMonomials n M j) := by
    intro j
    rw [← affineChart_homogeneous_coefficient f hf j,
      ← affineChart_homogeneous_coefficient g hg j, he]
  rw [homogeneous_eq_sum_coeff f hf, homogeneous_eq_sum_coeff g hg]
  simp only [hc]

/-- Restriction to the affine chart `x₀ = 1` does not increase the total degree. -/
lemma affineChart_totalDegree_le : (affineChart n f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [affineChart_monomial]
  have h := le_totalDegree hm
  rw [exponent_degree_split] at h
  apply (totalDegree_monomial_le _ _).trans
  change (chartExponent m).sum (fun _ e => e) ≤ f.totalDegree
  omega

section

variable (M : ℕ) (m : Fin n →₀ ℕ)

/-- The exponent in `n + 1` variables obtained from `m` by prepending `M - |m|` as the exponent of
the first variable, where `|m|` is the degree of `m`; it has degree `M` when `|m| ≤ M`. -/
def homogenizedExponent : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons (M - m.sum (fun _ e => e)) m)

/-- Forgetting the first entry of `homogenizedExponent M m` recovers `m`. -/
@[simp] lemma chartExponent_homogenizedExponent :
    chartExponent (homogenizedExponent M m) = m := by
  ext i
  rfl

end

private lemma homogenizedExponent_degree (m : Fin n →₀ ℕ)
    (hm : m.sum (fun _ e => e) ≤ M) :
    (homogenizedExponent M m).sum (fun _ e => e) = M := by
  rw [exponent_degree_split, chartExponent_homogenizedExponent]
  change M - m.sum (fun _ e => e) + m.sum (fun _ e => e) = M
  omega

private lemma homogenizedExponent_injective :
    Function.Injective (homogenizedExponent (n := n) d) := by
  intro m k h
  simpa using congrArg chartExponent h

section

variable (f : MvPolynomial (Fin n) R)

/-- Scaled homogenization in degree `d`: the monomial `x^m` becomes
`h ^ |m| * x₀ ^ (d - |m|) * x^m`. With `h = 1` this is the usual homogenization,
which is a section of `affineChart` (see `affineChart_scaledHomogenize_one`). -/
def scaledHomogenize : MvPolynomial (Fin (n + 1)) R :=
  ∑ m ∈ f.support, monomial (homogenizedExponent d m) (h ^ m.sum (fun _ e => e) * f.coeff m)

/-- The coefficient of `scaledHomogenize d h f` at `homogenizedExponent d m` is
`h ^ |m| * f.coeff m`, where `|m|` is the degree of `m`. -/
lemma scaledHomogenize_coefficient (m : Fin n →₀ ℕ) :
    (scaledHomogenize d h f).coeff (homogenizedExponent d m) =
      h ^ m.sum (fun _ e => e) * f.coeff m := by
  classical
  by_cases hm : m ∈ f.support
  simp [scaledHomogenize, (homogenizedExponent_injective d).eq_iff, hm]
  simp [scaledHomogenize, (homogenizedExponent_injective d).eq_iff, hm, (notMem_support_iff.mp hm)]

/-- If `f` has total degree at most `d`, then its scaled homogenization in degree `d` is homogeneous
of degree `d`. -/
lemma scaledHomogenize_homogeneous {d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ d) :
    (scaledHomogenize d h f).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro m hm
  exact isHomogeneous_monomial _ (homogenizedExponent_degree m ((le_totalDegree hm).trans hf))

/-- Homogenization in degree `d`, that is scaled homogenization with `h = 1`, is a right inverse of
the affine chart `x₀ = 1`. -/
lemma affineChart_scaledHomogenize_one : affineChart n (scaledHomogenize d 1 f) = f := by
  classical
  simp only [scaledHomogenize, map_sum, affineChart_monomial, chartExponent_homogenizedExponent,
    one_pow, one_mul]
  exact f.as_sum.symm

end

/-- The affine chart `x₀ = 1` commutes with mapping the coefficients along a ring
homomorphism `φ`. -/
lemma affineChart_map [CommRing L] {n : ℕ}
    (φ : K →+* L) (f : MvPolynomial (Fin (n + 1)) K) :
    affineChart n (MvPolynomial.map φ f) = MvPolynomial.map φ (affineChart n f) := by
  have he : (affineChart n).comp (MvPolynomial.map φ) =
      (MvPolynomial.map φ).comp (affineChart n) := by
    apply MvPolynomial.ringHom_ext
    simp [affineChart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [affineChart]
  exact RingHom.congr_fun he f

/-- Evaluating the affine chart of `f` at `x` is evaluating `f` at the point `Fin.cons 1 x`. -/
lemma affineChart_eval (x : Fin n → K) :
    eval x (affineChart n f) = eval (Fin.cons 1 x) f := by
  change eval x (eval₂ C (Fin.cons 1 X) f) = _
  rw [← eval_assoc]
  have he : (eval x) ∘ Fin.cons (1 : MvPolynomial (Fin n) K) X = Fin.cons 1 x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [he]

/-- Divisibility of affine charts lifts to homogeneous divisibility when the
first equation retains its degree on the chart. -/
theorem homogeneous_dvd_of_affineChart_dvd [IsDomain K]
    {n d M : ℕ} {f g : MvPolynomial (Fin (n + 1)) K}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hg : g.IsHomogeneous M)
    (hdchart : (affineChart n f).totalDegree = d)
    (hdiv : affineChart n f ∣ affineChart n g) : f ∣ g := by
  have hcf : affineChart n f ≠ 0 := by
    intro hz
    solve_by_elim [affineChart_injective_on_homogeneous, isHomogeneous_zero, map_zero]
  by_cases hcg : affineChart n g = 0
  · have hg0 := affineChart_injective_on_homogeneous hg (isHomogeneous_zero _ _ M)
      (by exact hcg)
    simp [hg0]
  obtain ⟨q, hq⟩ := hdiv
  have hq0 : q ≠ 0 := by grind
  have hdeg := by
    have hh := (affineChart_totalDegree_le g).trans hg.totalDegree_le
    rw [hq, totalDegree_mul_of_isDomain hcf hq0, hdchart] at hh
    exact hh
  have hdM : d ≤ M := by omega
  refine ⟨scaledHomogenize (M - d) 1 q, ?_⟩
  apply affineChart_injective_on_homogeneous hg
  simpa [*] using hf.mul (scaledHomogenize_homogeneous 1 q (show q.totalDegree ≤ M - d by omega))
  simp_all [affineChart_scaledHomogenize_one]

end
end CCDN
