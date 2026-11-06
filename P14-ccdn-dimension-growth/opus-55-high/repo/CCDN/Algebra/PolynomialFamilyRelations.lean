/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Defs
import CCDN.Algebra.PolynomialKernelOrigin
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
Relations among a finite family of algebra-valued polynomials can be
encoded by a finite scalar polynomial matrix. Persistent dependence therefore
gives a polynomial relation nonzero at the origin, even when the target
algebra is infinite-dimensional over the scalar field.

Apply a linear functional to the coefficients of a univariate polynomial.
This commutes with evaluation over the scalar field and multiplication by
scalar polynomials, allowing polynomial relations to be encoded by matrices.
-/

namespace CCDN
noncomputable section
open Polynomial

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] (φ : A →ₗ[K] K)

def coefficientLinearUnivariate
    (p : Polynomial A) : Polynomial K :=
  ∑ n ∈ p.support, monomial n (φ (p.coeff n))

lemma coefficientLinearUnivariate_coeff
    (p : Polynomial A) (n : ℕ) :
    (coefficientLinearUnivariate φ p).coeff n = φ (p.coeff n) := by
  by_cases hn : n ∈ p.support
  · simp [coefficientLinearUnivariate, coeff_monomial, hn]
  · have hz := notMem_support_iff.mp hn
    simp [coefficientLinearUnivariate, coeff_monomial, hn, hz]

/-- Coefficientwise application of a linear functional. -/
def coefficientLinearUnivariateMap
    : Polynomial A →ₗ[K] Polynomial K where
  toFun := coefficientLinearUnivariate φ
  map_add' p q := by ext n; simp [coefficientLinearUnivariate_coeff]
  map_smul' c p := by ext n; simp [coefficientLinearUnivariate_coeff]

lemma coefficientLinearUnivariate_scalar_mul
    (p : Polynomial K) (q : Polynomial A) :
    coefficientLinearUnivariate φ (p.map (algebraMap K A) * q) =
      p * coefficientLinearUnivariate φ q := by
  ext n
  rw [coefficientLinearUnivariate_coeff, coeff_mul, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [coeff_map, coefficientLinearUnivariate_coeff]
  simpa [Algebra.smul_def] using φ.map_smul (p.coeff t.1) (q.coeff t.2)

lemma coefficientLinearUnivariate_eval
    (p : Polynomial A) (t : K) :
    (coefficientLinearUnivariate φ p).eval t = φ (p.eval (algebraMap K A t)) := by
  rw [coefficientLinearUnivariate, Polynomial.eval_finsetSum]
  conv_rhs => rw [p.as_sum_support, Polynomial.eval_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [eval_monomial, eval_monomial, ← map_pow]
  have hh := φ.map_smul (t ^ n) (p.coeff n)
  simpa [Algebra.smul_def, mul_comm] using hh.symm

end

section
open Polynomial Matrix

lemma exists_finite_detecting_functionals {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (S : Submodule K V) [Module.Finite K S] :
    ∃ φ : Fin (Module.finrank K S) → V →ₗ[K] K,
      ∀ x ∈ S, (∀ i, φ i x = 0) → x = 0 := by
  obtain ⟨T, hT⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  let b := Module.finBasis K S
  refine ⟨fun i => (b.coord i).comp T, ?_⟩
  intro x hx hzero
  have hTx := congrArg (fun f => f ⟨x, hx⟩) hT
  have ht : T x = 0 := by
    apply b.repr.injective
    ext i
    simp_all
  have hz := hTx.symm.trans ht
  exact congrArg Subtype.val hz

/-- If the evaluations of a polynomial family are dependent over K at every
integer parameter, the family has a polynomial relation whose coefficient
vector does not vanish at zero. -/
theorem polynomial_family_relation_nonzero_at_zero {K A κ : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A] [Fintype κ] [DecidableEq κ]
    (g : κ → Polynomial A)
    (hdep : ∀ k : ℕ, ∃ c : κ → K, c ≠ 0 ∧ ∑ j, c j • (g j).eval (k : A) = 0) :
    ∃ v : κ → Polynomial K,
      (∑ j, (v j).map (algebraMap K A) * g j) = 0 ∧ ∃ j, (v j).eval 0 ≠ 0 := by
  classical
  let s := Finset.univ.biUnion (fun j => (g j).support.image (fun n => (g j).coeff n))
  let S := Submodule.span K (s : Set A)
  let : Module.Finite K S := Module.Finite.span_of_finite K s.finite_toSet
  have hmem (j : κ) (n : ℕ) : (g j).coeff n ∈ S := by
    by_cases hn : n ∈ (g j).support
    · aesop
    simp_all
  obtain ⟨φ, hφ⟩ := exists_finite_detecting_functionals S
  let M : Matrix (Fin (Module.finrank K S)) κ (Polynomial K) :=
    fun i j => coefficientLinearUnivariate (φ i) (g j)
  have hM (k : ℕ) : ¬ Function.Injective (M.map (Polynomial.evalRingHom (k : K))).mulVecLin := by
    intro hi
    obtain ⟨c, hc, hrel⟩ := hdep k
    apply hc
    apply hi
    rw [map_zero]
    funext i
    change ∑ j, (coefficientLinearUnivariate (φ i) (g j)).eval (k : K) * c j = 0
    simp [coefficientLinearUnivariate_eval, map_natCast]
    calc
      _ = φ i (∑ j, c j • (g j).eval (k : A)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp [map_smul, smul_eq_mul, mul_comm]
      _ = 0 := by grind
  obtain ⟨v, hv, hv0⟩ : ∃ v : κ → Polynomial K, M *ᵥ v = 0 ∧ ∃ j, (v j).eval 0 ≠ 0 := by
    have hgen : ¬ Function.Injective
        (M.map (algebraMap (Polynomial K) (RatFunc K))).mulVecLin := by
      intro hi
      obtain ⟨k, hk⟩ : ∃ k : ℕ, Function.Injective (M.map (Polynomial.evalRingHom (k : K))).mulVecLin := by
        obtain ⟨q, C, hq, hCA⟩ := polynomial_matrix_scaled_left_inverse M hi
        obtain ⟨k, _, hk⟩ := polynomial_exists_small_nat_eval_ne_zero q hq
        refine ⟨k, ?_⟩
        let e := Polynomial.evalRingHom (k : K)
        have he : C.map e * M.map e = e q • (1 : Matrix κ κ K) := by
          rw [← Matrix.map_mul, hCA]
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
            Matrix.one_apply, apply_ite e, map_one, map_zero]
        intro x y hxy
        have hh := congrArg (fun v => (C.map e) *ᵥ v) hxy
        change (C.map e) *ᵥ ((M.map e) *ᵥ x) = (C.map e) *ᵥ ((M.map e) *ᵥ y) at hh
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, he, Matrix.smul_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at hh
        exact (smul_right_injective _ hk) hh
      exact hM k hk
    obtain ⟨w, hw, hAw⟩ := polynomial_matrix_kernel_of_not_injective M hgen
    obtain ⟨N, v, hv, hv0⟩ := polynomial_vector_remove_common_X w hw
    refine ⟨v, ?_, hv0⟩
    funext i
    apply mul_left_cancel₀ (pow_ne_zero N Polynomial.X_ne_zero)
    simp only [Pi.zero_apply, mul_zero]
    change X ^ N * (∑ j, M i j * v j) = 0
    rw [Finset.mul_sum]
    have hh := congrFun hAw i
    change ∑ j, M i j * w j = 0 at hh
    rw [← hh]
    apply Finset.sum_congr rfl
    intro j _
    rw [hv j]
    ring
  refine ⟨v, ?_, hv0⟩
  let P := ∑ j, (v j).map (algebraMap K A) * g j
  have hcoeff (n : ℕ) : P.coeff n ∈ S := by
    simp [P, Polynomial.finsetSum_coeff, coeff_mul, coeff_map]
    apply S.sum_mem
    intro j _
    apply S.sum_mem
    intro t _
    simpa [Algebra.smul_def] using S.smul_mem ((v j).coeff t.1) (hmem j t.2)
  have hfun (i : Fin (Module.finrank K S)) : coefficientLinearUnivariate (φ i) P = 0 := by
    change coefficientLinearUnivariateMap (φ i) (∑ j, (v j).map (algebraMap K A) * g j) = 0
    rw [map_sum]
    change ∑ j, coefficientLinearUnivariate (φ i) ((v j).map (algebraMap K A) * g j) = 0
    simp [coefficientLinearUnivariate_scalar_mul]
    have hh := congrFun hv i
    change ∑ j, coefficientLinearUnivariate (φ i) (g j) * v j = 0 at hh
    grind
  change P = 0
  ext n
  apply hφ _ (hcoeff n)
  intro i
  have hh := congrArg (fun p => p.coeff n) (hfun i)
  simpa [coefficientLinearUnivariate_coeff, coeff_zero] using hh

