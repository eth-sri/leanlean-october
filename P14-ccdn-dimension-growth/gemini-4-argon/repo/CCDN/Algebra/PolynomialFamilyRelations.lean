/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
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

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

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
  let L (φ : A →ₗ[K] K) (p : Polynomial A) : Polynomial K :=
    ∑ n ∈ p.support, monomial n (φ (p.coeff n))
  have hLcoeff (φ : A →ₗ[K] K) (p : Polynomial A) (n : ℕ) : (L φ p).coeff n = φ (p.coeff n) := by
    by_cases hn : n ∈ p.support <;>
      simp [L, coeff_monomial, hn, notMem_support_iff.mp]
  let s := Finset.univ.biUnion fun j => (g j).support.image fun n => (g j).coeff n
  let S := Submodule.span K (s : Set A)
  let : Module.Finite K S := Module.Finite.span_of_finite K s.finite_toSet
  have hmem (j : κ) (n : ℕ) : (g j).coeff n ∈ S := by
    by_cases hn : n ∈ (g j).support
    · exact Submodule.subset_span
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩)
    · rw [Polynomial.notMem_support_iff.mp hn]; exact S.zero_mem
  obtain ⟨T, hT⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  let b := Module.finBasis K S
  let φ : Fin (Module.finrank K S) → A →ₗ[K] K := fun i => (b.coord i).comp T
  let M : Matrix (Fin (Module.finrank K S)) κ (Polynomial K) := fun i j => L (φ i) (g j)
  have hM (k : ℕ) : ¬ Function.Injective (M.map (Polynomial.evalRingHom (k : K))).mulVecLin := by
    intro hi
    obtain ⟨c, hc, hrel⟩ := hdep k
    refine hc (hi ?_)
    rw [map_zero]
    funext i
    change ∑ j, (L (φ i) (g j)).eval (k : K) * c j = 0
    have hev (p : Polynomial A) : (L (φ i) p).eval (k : K) = φ i (p.eval (k : A)) := by
      rw [Polynomial.eval_finsetSum]
      conv_rhs => rw [p.as_sum_support, Polynomial.eval_finsetSum, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [eval_monomial, eval_monomial, ← map_natCast (algebraMap K A), ← map_pow]
      simpa [Algebra.smul_def, mul_comm] using ((φ i).map_smul ((k : K) ^ n) (p.coeff n)).symm
    simp only [hev]
    rw [show (∑ j, φ i ((g j).eval (k : A)) * c j) = φ i (∑ j, c j • (g j).eval (k : A)) by
      rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by simp [mul_comm], hrel, map_zero]
  obtain ⟨v, hv, hv0⟩ := polynomial_matrix_kernel_nonzero_at_zero M hM
  refine ⟨v, ?_, hv0⟩
  let P := ∑ j, (v j).map (algebraMap K A) * g j
  have hcoeff (n : ℕ) : P.coeff n ∈ S := by
    simp only [P, Polynomial.finsetSum_coeff, coeff_mul, coeff_map]
    exact S.sum_mem fun j _ => S.sum_mem fun t _ => by
      simpa only [Algebra.smul_def] using S.smul_mem ((v j).coeff t.1) (hmem j t.2)
  change P = 0
  ext n
  have hsmul (i : Fin (Module.finrank K S)) (j : κ) :
      L (φ i) ((v j).map (algebraMap K A) * g j) = L (φ i) (g j) * v j := by
    rw [mul_comm _ (v j)]
    ext m
    rw [hLcoeff, coeff_mul, coeff_mul, map_sum]
    exact Finset.sum_congr rfl fun t _ => by
      rw [coeff_map, hLcoeff]
      simpa [Algebra.smul_def] using (φ i).map_smul ((v j).coeff t.1) ((g j).coeff t.2)
  have hzero (i : Fin (Module.finrank K S)) : φ i (P.coeff n) = 0 := by
    have hh := congrFun hv i
    change ∑ j, L (φ i) (g j) * v j = 0 at hh
    simp only [← hsmul] at hh
    have h0 := congrArg (fun q : Polynomial K => q.coeff n) hh
    simp only [finsetSum_coeff, coeff_zero, hLcoeff] at h0
    simpa only [P, finsetSum_coeff, map_sum] using h0
  have hTx : T (P.coeff n) = (⟨P.coeff n, hcoeff n⟩ : S) :=
    congrArg (fun f : S →ₗ[K] S => f ⟨P.coeff n, hcoeff n⟩) hT
  have ht : T (P.coeff n) = 0 := b.repr.injective <| Finsupp.ext fun i => by
    simpa only [φ, map_zero, Finsupp.zero_apply, LinearMap.comp_apply,
      Module.Basis.coord_apply] using hzero i
  simpa only [coeff_zero, Submodule.coe_zero] using congrArg Subtype.val (hTx.symm.trans ht)

end
end CCDN
