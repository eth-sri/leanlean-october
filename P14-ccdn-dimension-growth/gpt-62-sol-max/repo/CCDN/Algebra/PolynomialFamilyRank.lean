/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import CCDN.Algebra.BoundedLinearSeparation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Independence of a polynomial family survives at some positive integer
parameter. Dividing a single vanishing column by `X` gives the corresponding
first-order condition for a family whose map is never injective. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

private def coefficientLinearUnivariate {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (φ : A →ₗ[K] K) (p : Polynomial A) : Polynomial K :=
  ∑ n ∈ p.support, monomial n (φ (p.coeff n))

private lemma coefficientLinearUnivariate_eval {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (φ : A →ₗ[K] K) (p : Polynomial A) (t : K) :
    (coefficientLinearUnivariate φ p).eval t = φ (p.eval (algebraMap K A t)) := by
  classical
  rw [coefficientLinearUnivariate, Polynomial.eval_finsetSum]
  conv_rhs => rw [p.as_sum_support, Polynomial.eval_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [eval_monomial, eval_monomial, ← map_pow]
  have hh := φ.map_smul (t ^ n) (p.coeff n)
  simpa [Algebra.smul_def, mul_comm] using hh.symm


open Matrix in
/-- A finite family independent at zero remains independent at some positive integer. -/
private theorem independent_polynomials_at_positive_nat {K A ι : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A] [Fintype ι]
    (g : ι → Polynomial A)
    (h0 : LinearIndependent K (fun j => (g j).eval 0)) :
    ∃ k : ℕ, 0 < k ∧ LinearIndependent K (fun j => (g j).eval (algebraMap K A k)) := by
  classical
  let L := Fintype.linearCombination K (fun j => (g j).eval 0)
  obtain ⟨r, hr⟩ := L.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr
    (linearIndependent_iff_injective_fintypeLinearCombination.mp h0))
  let φ (i : ι) := (LinearMap.proj i : (ι → K) →ₗ[K] K).comp r
  let M : Matrix ι ι (Polynomial K) := fun i j => coefficientLinearUnivariate (φ i) (g j)
  have he : (evalRingHom 0 : Polynomial K →+* K).mapMatrix M = 1 := by
    ext i j
    change (coefficientLinearUnivariate (φ i) (g j)).eval 0 = _
    rw [coefficientLinearUnivariate_eval, map_zero]
    have hh := DFunLike.congr_fun hr (Pi.single j 1)
    change r (L (Pi.single j 1)) = _ at hh
    simp only [L, Fintype.linearCombination_apply_single, one_smul, LinearMap.id_apply] at hh
    simp [φ, hh, Matrix.one_apply, Pi.single_apply]
  have hd : M.det ≠ 0 := by
    intro hz
    have := congrArg Matrix.det he
    rw [← RingHom.map_det, hz, map_zero, det_one] at this
    exact zero_ne_one this
  obtain ⟨k, _, hk⟩ := polynomial_exists_small_nat_eval_ne_zero (X * M.det) (mul_ne_zero X_ne_zero hd)
  rw [eval_mul, eval_X, mul_ne_zero_iff] at hk
  refine ⟨k, Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp hk.1), ?_⟩
  apply LinearIndependent.of_comp r
  have h := Matrix.linearIndependent_cols_of_det_ne_zero
    (A := (evalRingHom (k : K)).mapMatrix M) (by rw [← RingHom.map_det]; exact hk.2)
  convert h using 1
  funext j i
  exact (coefficientLinearUnivariate_eval (φ i) (g j) k).symm

set_option maxHeartbeats 800000 in
/-- If a polynomial family of linear maps loses rank at every positive integer,
a vector in the one-dimensional kernel at zero has first derivative in the image at zero. -/
theorem polynomial_family_first_order_mem_range {K V A : Type*}
    [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [CommRing A] [Algebra K A] (L : V →ₗ[K] Polynomial A) (f : V)
    (hker : ((Polynomial.lcoeff A 0).restrictScalars K ∘ₗ L).ker = Submodule.span K {f})
    (hdep : ∀ k : ℕ, 0 < k → ¬ Function.Injective (fun x => (L x).eval (algebraMap K A k))) :
    (L f).coeff 1 ∈ ((Polynomial.lcoeff A 0).restrictScalars K ∘ₗ L).range := by
  classical
  let L₀ := (Polynomial.lcoeff A 0).restrictScalars K ∘ₗ L
  have hL₀ (x : V) : L₀ x = (L x).eval 0 := coeff_zero_eq_eval_zero _
  by_contra hn
  obtain ⟨W, hW⟩ := L₀.ker.exists_isCompl
  have hinj : Function.Injective (L₀.comp W.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    have he : (x : V) ∈ L₀.ker ⊓ W := ⟨hx, x.property⟩
    rwa [hW.inf_eq_bot, Submodule.mem_bot] at he
  let b := Module.finBasis K W
  let x := fun j => (b j).val
  have hi :=
    b.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinj)
  have hf : (L f).coeff 0 = 0 := by
    change f ∈ L₀.ker
    rw [hker]
    exact Submodule.mem_span_singleton_self f
  obtain ⟨P, hP⟩ := Polynomial.X_dvd_iff.mpr hf
  let g :=
    fun j => Option.casesOn' j P (L ∘ x)
  have hp : (L f).coeff 1 = P.eval 0 := by rw [hP, coeff_X_mul, coeff_zero_eq_eval_zero]
  have hlin : LinearIndependent K (fun j => (g j).eval 0) := by
    apply linearIndependent_option.mpr
    simp only [g, Function.comp_def, Option.casesOn'_some, Option.casesOn'_none, ← hL₀]
    refine ⟨hi, ?_⟩
    intro hbad
    apply hn
    rw [hp]
    refine Submodule.span_le.mpr ?_ hbad
    rintro _ ⟨j, rfl⟩
    exact ⟨x j, rfl⟩
  obtain ⟨k, hk, hiK⟩ := independent_polynomials_at_positive_nat g hlin
  let v := fun j => Option.casesOn' j f x
  have hxspan : Submodule.span K (Set.range x) = W := by
    change Submodule.span K (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    apply top_unique
    rw [← hW.sup_eq_top, hker]
    have hw : Submodule.span K (Set.range x) ≤ Submodule.span K (Set.range v) :=
      Submodule.span_mono (Set.range_subset_iff.mpr fun j => ⟨some j, rfl⟩)
    rw [hxspan] at hw
    exact sup_le (Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨none, rfl⟩)) hw
  apply hdep k hk
  let D := ((Polynomial.aeval (algebraMap K A k)).toLinearMap.restrictScalars K).comp L
  change Function.Injective D
  have he : D f = (k : K) • P.eval (algebraMap K A k) := by
    change (L f).eval _ = _
    rw [hP, eval_mul, eval_X, Algebra.smul_def]
  apply LinearMap.injective_of_linearIndependent hv
  rw [linearIndependent_option] at hiK ⊢
  have hk0 : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simpa only [v, g, Function.comp_def, Option.casesOn'_none, Option.casesOn'_some, he,
    Submodule.smul_mem_iff _ hk0, D, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AlgHom.toLinearMap_apply, Polynomial.coe_aeval_eq_eval] using hiK

end
end CCDN
