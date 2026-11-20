/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import CCDN.Noether.BivariateTotalDegree
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Noether.ShearNormalization
import CCDN.Plane.GridHeight

/-! A single grid-root polynomial in both coordinates, with Eisenstein place off the grid. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

private theorem irreducible_of_bivariate_eisenstein {K : Type*} [Field K]
    (a : K) (f : K[X][X]) (hm : f.Monic) (hd : 0 < f.natDegree)
    (hred : f.map (evalRingHom a) = X ^ f.natDegree)
    (hsimple : (f.coeff 0).derivative.eval a ≠ 0) : Irreducible f := by
  let P := Ideal.span {X - C a}
  have hp : P.IsPrime := Ideal.isPrime_span_singleton_of_prime (prime_X_sub_C a)
  apply Polynomial.IsEisensteinAt.irreducible (𝓟 := P) _ hp hm.isPrimitive hd
  refine ⟨hm.leadingCoeff_notMem hp.ne_top, ?_, ?_⟩
  · intro i hi
    apply Ideal.mem_span_singleton.mpr
    apply dvd_iff_isRoot.mpr
    have he := congrArg (fun q : K[X] => q.coeff i) hred
    simpa [coeff_map, coeff_X_pow, ne_of_lt hi, IsRoot] using he
  · intro h
    change f.coeff 0 ∈ (Ideal.span ({X - C a} : Set K[X])) ^ 2 at h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    exact hsimple (dvd_iff_isRoot.mp (by simpa using pow_sub_one_dvd_derivative_of_pow_dvd h))

section

variable {R : Type*} [CommRing R]
include R

private lemma bivariateTotalDegree_add_le (f g : R[X][X]) :
    bivariateTotalDegree (f + g) ≤ max (bivariateTotalDegree f) (bivariateTotalDegree g) := by
  unfold bivariateTotalDegree
  rw [map_add]
  exact MvPolynomial.totalDegree_add _ _

private lemma bivariateTotalDegree_C_le (f : R[X]) :
    bivariateTotalDegree (C f) ≤ f.natDegree := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  by_cases hi : i = 0
  simp_all [le_natDegree_of_ne_zero]
  aesop

private lemma bivariateTotalDegree_map_C_le (f : R[X]) :
    bivariateTotalDegree (f.map C) ≤ f.natDegree := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  by_cases hj : j = 0
  simp_all [le_natDegree_of_ne_zero]
  aesop

end

private lemma evalRingHom_comp_C {K : Type*} [Field K] (a : K) :
    (evalRingHom a).comp C = RingHom.id K := by ext; simp

private def gridEquation {K : Type*} [Field K] (U : K[X]) (a : K) (s k : ℕ) : K[X][X] :=
  U.map C + C U * ((C (U.eval a)⁻¹ * (X ^ s - U)).map C + C ((X - C a) ^ k + (X - C a)))

private lemma gridEquation_properties {K : Type*} [Field K] {U : K[X]} {a : K} {s k : ℕ}
    (hU : IsMonicOfDegree U s) (hU0 : U.coeff 0 = 0) (ha : U.eval a ≠ 0)
    (hs : 0 < s) (hk : 2 ≤ k) (hsk : s ≤ k + 1) :
    Irreducible (gridEquation U a s k) ∧ bivariateTotalDegree (gridEquation U a s k) = s + k := by
  let D := C (U.eval a)⁻¹ * (X ^ s - U)
  let W := (X - C a) ^ k + (X - C a)
  have hD : D.natDegree < s := (natDegree_C_mul_le ..).trans_lt
    ((isMonicOfDegree_X_pow K s).natDegree_sub_lt hs.ne' hU)
  have hW : IsMonicOfDegree W k := by
    have ht : IsMonicOfDegree (X - C a) 1 := ⟨natDegree_X_sub_C a, monic_X_sub_C a⟩
    apply (show IsMonicOfDegree ((X - C a) ^ k) k by simpa using ht.pow k).add_right
    simpa using show 1 < k by omega
  have hF : IsMonicOfDegree (gridEquation U a s k) s := by
    change IsMonicOfDegree (U.map C + C U * (D.map C + C W)) s
    apply (show IsMonicOfDegree (U.map C) s from
      ⟨(hU.monic.natDegree_map C).trans hU.natDegree_eq, hU.monic.map C⟩).add_right
    exact (natDegree_C_mul_le ..).trans_lt ((natDegree_add_le ..).trans_lt
      (max_lt ((natDegree_map_le).trans_lt hD) (by simpa only [natDegree_C] using hs)))
  have hF0 : (gridEquation U a s k).coeff 0 = U * W := by
    change (U.map C + C U * (D.map C + C W)).coeff 0 = U * W
    simp [D, hU0, show 0 ≠ s by omega, coeff_X_pow]
  refine ⟨irreducible_of_bivariate_eisenstein a _ hF.monic (by simpa only [hF.natDegree_eq] using hs) ?_ ?_, ?_⟩
  · rw [hF.natDegree_eq]
    have he : C (U.eval a) * D = X ^ s - U := by simp [D, ← mul_assoc, ← C_mul, ha]
    have hW0 : W.eval a = 0 := by simp [W, show k ≠ 0 by omega]
    change (U.map C + C U * (D.map C + C W)).map (evalRingHom a) = _
    simp [Polynomial.map_add, Polynomial.map_mul, map_map, evalRingHom_comp_C, hW0, he]
  · rw [hF0]
    simp [W, derivative_mul, derivative_pow, show k ≠ 0 by omega, show k - 1 ≠ 0 by omega, ha]
  · apply le_antisymm
    · apply (bivariateTotalDegree_add_le _ _).trans
      refine max_le ((bivariateTotalDegree_map_C_le U).trans (hU.1.trans_le (by omega))) ?_
      apply (bivariateTotalDegree_mul_le _ _).trans
      refine (add_le_add ((bivariateTotalDegree_C_le U).trans hU.1.le)
        ((bivariateTotalDegree_add_le _ _).trans (max_le ?_ ?_))).trans (le_refl (s + k))
      · exact (bivariateTotalDegree_map_C_le D).trans (by omega)
      · exact (bivariateTotalDegree_C_le W).trans hW.1.le
    · have hUW := hU.mul hW
      simpa using bivariateTotalDegree_coeff_le (gridEquation U a s k) 0 (s+k) (by
        rw [hF0, ← hUW.natDegree_eq, hUW.monic.coeff_natDegree]
        exact one_ne_zero)

/-- A Cartesian square grid containing zero lies on an absolutely irreducible
curve of degree `d` if its side length is at most `(d+1)/2` and at most `d-2`. -/
theorem exists_absolutely_irreducible_plane_grid
    {K L : Type*} [Field K] [Infinite K] [Field L] (φ : K →+* L)
    (s : Finset K) (h0 : 0 ∈ s) (d : ℕ)
    (hd : s.card + 2 ≤ d) (hsize : 2 * s.card ≤ d + 1) :
    ∃ f : MvPolynomial (Fin 2) K,
      f.totalDegree = d ∧ Irreducible (MvPolynomial.map φ f) ∧
        ∀ z : Fin 2 → K, (∀ i, z i ∈ s) → MvPolynomial.eval z f = 0 := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset s
  let U := ∏ x ∈ s, (X - C x)
  have hU : IsMonicOfDegree U s.card :=
    ⟨natDegree_finsetProd_X_sub_C_eq_card s id, monic_prod_X_sub_C id s⟩
  have hroot (x : K) (hx : x ∈ s) : U.eval x = 0 := by
    rw [show U = _ from rfl, eval_prod]
    exact Finset.prod_eq_zero hx (by simp)
  have hU0 := (coeff_zero_eq_eval_zero U).trans (hroot 0 h0)
  have ha' : U.eval a ≠ 0 := by
    simp [U, eval_prod, Finset.prod_ne_zero_iff, sub_eq_zero]
    grind
  let k := d - s.card
  have hs := Finset.card_pos.mpr ⟨0, h0⟩
  let F := gridEquation U a s.card k
  let f := (bivariatePolynomialEquiv K).symm F
  have heval : (U.map φ).eval (φ a) = φ (U.eval a) := by rw [eval_map, eval₂_hom]
  have hmap : (bivariatePolynomialEquiv L) (MvPolynomial.map φ f) =
      gridEquation (U.map φ) (φ a) s.card k := by
    rw [← bivariatePolynomialEquiv_map, show (bivariatePolynomialEquiv K) f = F from
      AlgEquiv.apply_symm_apply _ _]
    have h : (Polynomial.mapRingHom φ).comp C = C.comp φ := by ext; simp
    simp only [F, gridEquation, bivariateMap, coe_mapRingHom, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, map_map, h, map_inv₀, heval]
  obtain ⟨hir, hdeg⟩ := gridEquation_properties (a := φ a)
    (⟨(hU.monic.natDegree_map φ).trans hU.1, hU.monic.map φ⟩)
    (by simp [hU0]) (by rwa [heval, ne_eq, map_eq_zero_iff φ φ.injective]) hs
    (show 2 ≤ k by omega) (show s.card ≤ k + 1 by omega)
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [← MvPolynomial.totalDegree_map_of_injective φ.injective f]
    rw [← hmap, bivariateTotalDegree, AlgEquiv.symm_apply_apply] at hdeg
    omega
  · apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)).mp
    rwa [hmap]
  · intro z hz
    have h := bivariatePolynomialEquiv_eval f (z 0) (z 1)
    rw [show (bivariatePolynomialEquiv K) f = F from AlgEquiv.apply_symm_apply _ _] at h
    have he : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
    simpa [F, gridEquation, Polynomial.map_add, Polynomial.map_mul, map_map, evalRingHom_comp_C,
      hroot (z 0) (hz 0), hroot (z 1) (hz 1), he] using h.symm

end
end CCDN
