/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.ForMathlib.KrullHeight
import CCDN.Hilbert.AffineCurveDegree
import CCDN.Plane.IntegralAffineLine
import CCDN.Algebra.CoordinatePowerGeneration
import CCDN.Hilbert.CriticalFilteredGrowth
import CCDN.Hilbert.PrimeComponentTranscendence

/-!
# Degree-one prime curves are affine lines

The eventual Hilbert-degree definition implies a one-dimensional increase in
successive filtered spaces. Critical growth forces every coordinate to be affine
in one transcendental coordinate, giving polynomial containment of an affine line.
-/

namespace CCDN
open MvPolynomial

lemma coordinate_mul_filtered_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (j : σ) (N : ℕ)
    {u : MvPolynomial σ K ⧸ I} (hu : u ∈ filteredCoordinateSpace I N) :
    (Ideal.Quotient.mk I) (X j) * u ∈ filteredCoordinateSpace I (N + 1) := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hu
  apply Submodule.mem_map.mpr
  refine ⟨X j * f, ?_, by simp⟩
  rw [mem_restrictTotalDegree] at hf ⊢
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_X]
  omega

/-- Affine coordinate formulas in a prime quotient give polynomial containment
of an affine line through each base-field-valued point. -/
theorem affine_coordinates_line_polynomial_identity {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) 
    (j : Fin 3) (c d : Fin 3 → K)
    (hj : Transcendental K ((Ideal.Quotient.mk p) (X j)))
    (hcd : ∀ k, (Ideal.Quotient.mk p) (X k) =
      c k • (Ideal.Quotient.mk p) (X j) + algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (d k))
    (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p) :
    ∀ f ∈ p,
      MvPolynomial.aeval
        (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) f = 0 := by
  let x := (Ideal.Quotient.mk p) (X j)
  let φ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval (fun k => Polynomial.C (d k) + Polynomial.C (c k) * Polynomial.X)
  have hcomp : (Polynomial.aeval x).comp φ = Ideal.Quotient.mkₐ K p := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, φ, aeval_X, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X]
    rw [Ideal.Quotient.mkₐ_eq_mk, hcd k]
    have hsmul :=
        Algebra.smul_def (A := MvPolynomial (Fin 3) K ⧸ p) (c k)
          ((Ideal.Quotient.mk p) (X j))
    grind
  have hφ (f : MvPolynomial (Fin 3) K) (hf : f ∈ p) : φ f = 0 := by
    apply (transcendental_iff_injective.mp hj)
    change ((Polynomial.aeval x).comp φ) f = _
    rw [hcomp]
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hpoint (k : Fin 3) : z k = d k + c k * z j := by
    have hrel : X k - (C (d k) + C (c k) * X j) ∈ p := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change (Ideal.Quotient.mk p) (X k) -
        (algebraMap K _ (d k) + algebraMap K _ (c k) * (Ideal.Quotient.mk p) (X j)) = 0
      have hsmul :=
        Algebra.smul_def (A := MvPolynomial (Fin 3) K ⧸ p) (c k)
          ((Ideal.Quotient.mk p) (X j))
      grind
    have he := hz _ hrel
    grind [eval_sub, eval_add, eval_mul, eval_X, eval_C, sub_eq_zero]
  have htranslate :
      (Polynomial.aeval (Polynomial.C (z j) + Polynomial.X)).comp φ =
      MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [AlgHom.comp_apply, φ, aeval_X, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X]
    rw [hpoint k]
    simp
    ring
  intro f hf
  rw [← htranslate, AlgHom.comp_apply, hφ f hf, map_zero]

