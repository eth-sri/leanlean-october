/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredIntersection
import CCDN.Plane.LinearDeformation
import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Projection.CurveProjectionDeformation
import CCDN.Projection.PlaneRelationSpace

/-!
A degree-preserving linear plane projection admits reconstruction using
the partial derivative of its image equation. This bounds the common
denominator's degree by d-1 without normalization or a genus formula.

The constant and first-order equations of a polynomial family of plane
relations, expressed as equations in the target algebra.
-/

namespace CCDN
section
open MvPolynomial

/-- Differentiate a family of degree-d plane equations to reconstruct
any linear source function using the same derivative denominator. -/
theorem exists_derivative_reconstruction {K τ : Type*}
    [Field K] [CharZero K] [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin 2 → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdegree : HasFilteredCurveDegree I d)
    (hu : Transcendental K ((Ideal.Quotient.mk I) (a 0)))
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hfd : f.totalDegree = d)
    (hker : ∀ g, aeval a g ∈ I ↔ f ∣ g)
    (l : MvPolynomial τ K) (hl : l.totalDegree ≤ 1) :
    ∃ P : MvPolynomial (Fin 2) K, P.totalDegree ≤ d ∧
      aeval a (pderiv 1 f) * l - aeval a P ∈ I := by
  let V := restrictTotalDegree (Fin 2) K d
  let b := Module.finBasis K V
  obtain ⟨v, hv, j, hj⟩ : let V := restrictTotalDegree (Fin 2) K d
        let b := Module.finBasis K V
        ∃ v : Fin (Module.finrank K V) → Polynomial K,
          (∑ j, (v j).map (algebraMap K (MvPolynomial τ K ⧸ I)) *
            planeLinearDeformation (fun i => (Ideal.Quotient.mk I) (a i)) 1
              ((Ideal.Quotient.mk I) l) (b j).val) = 0 ∧
          ∃ j, (v j).eval 0 ≠ 0 := by
      let V := restrictTotalDegree (Fin 2) K d
      let b := Module.finBasis K V
      let ψ := planeLinearDeformation (K := K) (fun i => (Ideal.Quotient.mk I) (a i)) 1
        ((Ideal.Quotient.mk I) l)
      let g := fun j => ψ (b j).val
      apply polynomial_family_relation_nonzero_at_zero g
      intro k
      let aT : Fin 2 → MvPolynomial τ K := ![a 0, a 1 + (k : K) • l]
      have hat (i : Fin 2) : (aT i).totalDegree ≤ 1 := by
        fin_cases i
        · aesop
        · change (a 1 + (k : K) • l).totalDegree ≤ 1
          apply (totalDegree_add _ _).trans
          apply max_le (ha 1)
          exact (totalDegree_smul_le _ _).trans hl
      obtain ⟨p, hp, hpd, hkernel⟩ := exists_plane_projection_equation_degree_le
        I aT hat d hdegree 0 hu
      have hpzero : projectionCoordinateMap I aT p = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ((hkernel p).mpr (dvd_refl p))
      let pV : V := ⟨p, (mem_restrictTotalDegree _ _ _).mpr hpd⟩
      let c := fun j => b.repr pV j
      have hc : c ≠ 0 := by aesop
      have hs : ∑ j, c j • (b j).val = p := by
        have hh := congrArg Subtype.val (b.sum_repr pV)
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using hh
      refine ⟨c, hc, ?_⟩
      have hev (j : Fin (Module.finrank K V)) : (g j).eval (k : MvPolynomial τ K ⧸ I) =
          projectionCoordinateMap I aT (b j).val := by
        simpa using planeLinearDeformation_eval_quotient I a l k (b j).val
      simp [hev]
      simp_rw [← map_smul]
      rw [← map_sum, hs, hpzero]
  let r := fun i => (b i).val
  let f₀ := ∑ i, (v i).coeff 0 • r i
  let f₁ := ∑ i, (v i).coeff 1 • r i
  have hmem (m : ℕ) : (∑ i, (v i).coeff m • r i) ∈ V := by
    apply V.sum_mem
    intro i _
    exact V.smul_mem _ (b i).property
  have hd₀ := (mem_restrictTotalDegree _ _ _).mp (hmem 0)
  have hd₁ := (mem_restrictTotalDegree _ _ _).mp (hmem 1)
  have hn₀ : f₀ ≠ 0 := by
    intro hz
    have hi := b.linearIndependent.map' V.subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hh := Fintype.linearIndependent_iff.mp hi (fun i => (v i).coeff 0) hz j
    exact hj (by rwa [← Polynomial.coeff_zero_eq_eval_zero])
  let aq := fun i => (Ideal.Quotient.mk I) (a i)
  let ψ := aeval (R := K) aq
  have hψ (p : MvPolynomial (Fin 2) K) : (Ideal.Quotient.mk I) (aeval a p) = ψ p :=
    comp_aeval_apply a (Ideal.Quotient.mkₐ K I) p
  have h0 := congrArg (fun p => p.coeff 0) hv
  have h1 := congrArg (fun p => p.coeff 1) hv
  simp [Polynomial.finsetSum_coeff, Polynomial.mul_coeff_zero, Polynomial.coeff_map,
    planeLinearDeformation_coeff_zero, Polynomial.coeff_zero] at h0
  simp [Polynomial.finsetSum_coeff, Polynomial.mul_coeff_one, Polynomial.coeff_map,
    planeLinearDeformation_coeff_zero, planeLinearDeformation_coeff_one,
    Polynomial.coeff_zero, Finset.sum_add_distrib] at h1
  have h₁ : ψ f₁ + ψ (pderiv 1 f₀) * (Ideal.Quotient.mk I) l = 0 := by
    simp [ψ, f₀, f₁, r, aq, b, V]
    rw [add_comm, ← h1]
    simp [Finset.sum_mul, smul_mul_assoc]
    exact congrArg₂ _ (Finset.sum_congr rfl fun x _ => Algebra.smul_def (A := MvPolynomial τ K ⧸ I) _ _)
      (Finset.sum_congr rfl fun x _ => Algebra.smul_def (A := MvPolynomial τ K ⧸ I) _ _)
  have hz₀ := Ideal.Quotient.eq_zero_iff_mem.mp ((hψ f₀).trans (by
    simp [ψ, f₀, r, aq, b, V]
    exact (Finset.sum_congr rfl fun x _ => Algebra.smul_def _ _).trans h0))
  obtain ⟨c, hc⟩ :=
    eq_scalar_mul_of_dvd_of_totalDegree_le f f₀ hf ((hker f₀).mp hz₀) (by grind)
  have hcn : c ≠ 0 := by simp_all
  rw [hc, Derivation.map_smul, map_smul, smul_mul_assoc] at h₁
  have hs := congrArg (fun x => c⁻¹ • x) h₁
  simp [smul_add, smul_smul, inv_mul_cancel₀ hcn, one_smul, smul_zero] at hs
  let P := -(c⁻¹ • f₁)
  refine ⟨P, ?_, ?_⟩
  · exact (totalDegree_neg _).le.trans ((totalDegree_smul_le _ _).trans hd₁)
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, hψ, hψ]
    simp [P, map_neg, map_smul, sub_neg_eq_add]
    grind

