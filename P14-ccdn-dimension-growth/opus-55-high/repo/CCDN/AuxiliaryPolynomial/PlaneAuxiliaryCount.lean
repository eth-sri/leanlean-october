/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousChart
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.Bezout

/-! Distinct-point bounds obtained from the auxiliary polynomials and
Bézout. The sharp finite-field estimate remains an explicit hypothesis. -/

namespace CCDN
section
open MvPolynomial

/-- Mapping an integer polynomial to `ℚ` preserves its total degree. -/
lemma rational_map_totalDegree {σ : Type*} (f : MvPolynomial σ ℤ) :
    (MvPolynomial.map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective Int.cast_injective _

/-- If the image of an integer polynomial in a field `F` of characteristic zero is irreducible,
then its image over `ℚ` is irreducible. -/
lemma rational_irreducible_of_charZero_map {F σ : Type*} [Field F] [CharZero F]
    (f : MvPolynomial σ ℤ) (hf : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) :
    Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  apply mvPolynomial_irreducible_of_field_map (algebraMap ℚ F)
  rw [map_map]
  have he : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = Int.castRingHom F := by aesop
  rwa [he]

/-- Bézout for distinct integer common zeros of two integer plane polynomials. -/
theorem integer_common_zeros_card_le {t : ℕ} (F G : MvPolynomial (Fin 2) ℤ)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) F))
    (hnd : ¬ MvPolynomial.map (Int.castRingHom ℚ) F ∣ MvPolynomial.map (Int.castRingHom ℚ) G)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hF : ∀ i, eval (z i) F = 0) (hG : ∀ i, eval (z i) G = 0) :
    t ≤ F.totalDegree * G.totalDegree := by
  have h := plane_common_zeros_card_le _ _ hir hnd (fun i j => (z i j : ℚ))
    (fun i j he => hinj (funext fun k => Int.cast_injective (congrFun he k)))
    (fun i => by have h := congrArg (Int.castRingHom ℚ) (hF i); rwa [map_eval, map_zero] at h)
    (fun i => by have h := congrArg (Int.castRingHom ℚ) (hG i); rwa [map_eval, map_zero] at h)
  rwa [Fintype.card_fin, rational_map_totalDegree, rational_map_totalDegree] at h

/-- The precise Bézout step for a homogeneous integer auxiliary
polynomial and a primitive equation whose chart has full degree. -/
theorem plane_chart_points_card_le_auxiliary_degree {d M t : ℕ}
    (f g : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (hg : g.IsHomogeneous M) (hprim : PrimitiveIntegerPolynomial f)
    (hdchart : (affineChart 2 f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (affineChart 2 f)))
    (hnd : ¬ f ∣ g) (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hzf : ∀ i, eval (z i) (affineChart 2 f) = 0)
    (hzg : ∀ i, eval (Fin.cons 1 (z i)) g = 0) : t ≤ d * M := by
  have h := integer_common_zeros_card_le _ _ hir (rational_affineChart_not_dvd hf hf0 hg hprim hdchart hnd) z hinj hzf (fun i => by simp_all [affineChart_eval])
  rw [hdchart] at h
  exact h.trans (Nat.mul_le_mul_left d ((affineChart_totalDegree_le g).trans hg.totalDegree_le))

/-- Enumerating the integer zeros transfers finite-family bounds to
the counting interface, including empty point sets. -/
lemma integer_zero_count_le_of_family_bound {n : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (B R : ℝ)
    (hbound : ∀ (t : ℕ) (z : Fin t → Fin n → ℤ), Function.Injective z →
      (∀ i, eval (z i) f = 0) → (∀ i, InBox (z i) B) → (t : ℝ) ≤ R) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B : ℝ) ≤ R := by
  let S := integralPoints (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → Fin n → ℤ := fun i => (e i).val
  have hinj := Subtype.val_injective.comp e.injective
  have hbox := fun i => (mem_integralPoints.mp (e i).property).1
  have h := hbound _ z hinj (by
    intro i
    apply Int.cast_injective (α := ℚ)
    have h := (mem_integralPoints.mp (e i).property).2
    change (Int.castRingHom ℚ) (eval (z i) f) = 0
    rwa [map_eval]) hbox
  simpa [Fintype.card_coe, S, count] using h

