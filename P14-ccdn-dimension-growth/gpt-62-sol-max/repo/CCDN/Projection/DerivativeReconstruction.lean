/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
public import CCDN.Plane.LinearDeformation
public import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Algebra.PolynomialFamilyRank
import CCDN.Projection.HilbertProjectionDegree
import CCDN.Projection.LeadingCoordinateExtension
import CCDN.Hilbert.LinearCoordinates
import CCDN.ForMathlib.MvPolynomialDerivative
import Mathlib.Algebra.MvPolynomial.Monad
import CCDN.Projection.PlaneRelationSpace

/-!
A degree-preserving linear projection to a hypersurface admits reconstruction using
the partial derivative of its image equation. This bounds the common
denominator's degree by d-1 without normalization or a genus formula.

-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Differentiate a family of hypersurface equations to reconstruct any linear source function
using the same derivative denominator. -/
theorem exists_derivative_reconstruction {K τ : Type*}
    [Field K] [CharZero K] [Fintype τ] [LinearOrder τ] {m : ℕ}
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin (m + 2) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hi : Function.Injective (projectionCoordinateMap I (fun i : Fin (m + 1) => a i.succ)))
    (f : MvPolynomial (Fin (m + 2)) K) (hf : f ≠ 0) (hdegree : HasProjectiveDimensionDegree I m f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f})
    (l : MvPolynomial τ K) (hl : l.totalDegree ≤ 1) :
    ∃ P : MvPolynomial (Fin (m + 2)) K, aeval a (pderiv 0 f) * l - aeval a P ∈ I := by
  let V := restrictTotalDegree (Fin (m + 2)) K f.totalDegree
  let A := MvPolynomial τ K ⧸ I
  let aq := fun i => Ideal.Quotient.mk I (a i)
  have hq : aeval aq = projectionCoordinateMap I a := (comp_aeval a (Ideal.Quotient.mkₐ K I)).symm
  let D := linearDeformation (K := K) aq 0 (Ideal.Quotient.mk I l)
  let L := D.toLinearMap ∘ₗ V.subtype
  let fV : V := ⟨f, (mem_restrictTotalDegree _ _ _).mpr le_rfl⟩
  have hker' : ((Polynomial.lcoeff A 0).restrictScalars K ∘ₗ L).ker = Submodule.span K {fV} := by
    ext p
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    change (D p.val).coeff 0 = 0 ↔ _
    rw [linearDeformation_coeff_zero, hq, projectionCoordinateMap_eq_zero_iff hker]
    constructor
    · rintro hp
      obtain ⟨c, hc⟩ := eq_scalar_mul_of_dvd_of_totalDegree_le f p.val hf hp
        ((mem_restrictTotalDegree _ _ _).mp p.property)
      exact ⟨c, Subtype.ext hc.symm⟩
    · rintro ⟨c, rfl⟩
      change f ∣ c • f
      rw [Algebra.smul_def]
      exact dvd_mul_left f _
  have hdep (k : ℕ) (_ : 0 < k) :
      ¬ Function.Injective (fun p : V => (L p).eval (algebraMap K A k)) := by
    intro hki
    let aT : Fin (m + 2) → MvPolynomial τ K := Fin.cases (a 0 + (k : K) • l) (a ∘ Fin.succ)
    have hat (i : Fin (m + 2)) : (aT i).totalDegree ≤ 1 :=
      Fin.cases (motive := fun i => (aT i).totalDegree ≤ 1)
        ((totalDegree_add _ _).trans (max_le (ha 0) ((totalDegree_smul_le _ _).trans hl)))
        (fun j => ha j.succ) i
    obtain ⟨q, hq, hqd, hqker⟩ := exists_hypersurface_projection_equation_degree_le I aT hat _
      hdegree (fun j => X j.succ) (by simp) (by
        simpa [aT] using injective_projectionCoordinateMap_iff.mp hi)
    have heval : (D q).eval (algebraMap K A k) = projectionCoordinateMap I aT q := by
      rw [linearDeformation_eval, projectionCoordinateMap, AlgHom.comp_apply, comp_aeval_apply]
      apply congrArg (fun w : Fin (m + 2) → A => aeval w q)
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> simp [aT, aq, Algebra.smul_def]
    have hz : (L ⟨q, (mem_restrictTotalDegree _ _ _).mpr hqd⟩).eval (algebraMap K A k) =
        (L 0).eval (algebraMap K A k) := by
      rw [map_zero, Polynomial.eval_zero]
      exact heval.trans ((projectionCoordinateMap_eq_zero_iff hqker).mpr (dvd_refl q))
    exact hq.ne_zero (congrArg Subtype.val (hki hz))
  obtain ⟨P, hP⟩ := polynomial_family_first_order_mem_range L fV hker' hdep
  change (D P.val).coeff 0 = (D f).coeff 1 at hP
  rw [linearDeformation_coeff_zero, linearDeformation_coeff_one, hq] at hP
  refine ⟨P.val, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  change Ideal.Quotient.mkₐ K I _ = 0
  rw [map_sub, sub_eq_zero, map_mul]
  exact hP.symm

/-- The derivative in the extra coordinate gives a proper section, since the tail is independent. -/
theorem projection_head_derivative_proper {K τ : Type*} [Field K] [CharZero K] {m : ℕ}
    (I : Ideal (MvPolynomial τ K)) (a : Fin (m + 2) → MvPolynomial τ K)
    (hi : Function.Injective (projectionCoordinateMap I (fun i : Fin (m + 1) => a i.succ)))
    (f : MvPolynomial (Fin (m + 2)) K) (hf : f ≠ 0)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    aeval a (pderiv 0 f) ∉ I := by
  classical
  have hder : pderiv 0 f ≠ 0 := by
    intro hz
    have hk := notMem_vars_of_pderiv_eq_zero hz (fun _ hn _ => Nat.cast_ne_zero.mpr hn.ne')
    have hvars : (f.vars : Set (Fin (m + 2))) ⊆ Set.range (Fin.succ : Fin (m + 1) → _) := by
      intro i
      exact Fin.cases (fun h => (hk h).elim) (fun j _ => ⟨j, rfl⟩) i
    obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range f Fin.succ (Fin.succ_injective _) hvars
    have hzero := (projectionCoordinateMap_eq_zero_iff hker).mpr (dvd_refl f)
    rw [← hq, ← AlgHom.comp_apply, projectionCoordinateMap_comp_rename_succ, map_eq_zero_iff _ hi] at hzero
    simp_all
  exact fun h => not_dvd_pderiv_of_pderiv_ne_zero hder
    ((projectionCoordinateMap_eq_zero_iff hker).mp (Ideal.Quotient.eq_zero_iff_mem.mpr h))

/-- All source coordinates are reconstructed with this same denominator. -/
theorem exists_projection_reconstruction {K τ : Type*} [Field K] [CharZero K] [Fintype τ]
    [LinearOrder τ] {m : ℕ} (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin (m + 2) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hi : Function.Injective (projectionCoordinateMap I (fun i : Fin (m + 1) => a i.succ)))
    (f : MvPolynomial (Fin (m + 2)) K) (hf : f ≠ 0)
    (hdegree : HasProjectiveDimensionDegree I m f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    ∃ P : τ → MvPolynomial (Fin (m + 2)) K, aeval a (pderiv 0 f) ∉ I ∧
      ∀ i, aeval a (pderiv 0 f) * X i - aeval a (P i) ∈ I := by
  choose P hP using fun i => exists_derivative_reconstruction I a ha hi f hf hdegree hker (X i) (by simp)
  exact ⟨P, projection_head_derivative_proper I a hi f hf hker, hP⟩

end
end CCDN
