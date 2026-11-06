/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.ForMathlib.KrullHeight
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Plane.IntegralAffineLine
import CCDN.Algebra.CoordinatePowerGeneration
import CCDN.Hilbert.CriticalFilteredGrowth
import CCDN.Hilbert.PrimeComponentTranscendence

/-!
# Degree-one prime curves are affine lines

The eventual Hilbert-degree definition implies a one-dimensional increase in
successive filtered spaces. Critical growth forces every coordinate to be affine
in one transcendental coordinate, giving polynomial containment of an affine line.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A degree-one prime component with a rational point is exactly a
rational affine line. This is equality of zero sets, not just containment. -/
theorem degree_one_zeroLocus_eq_rationalAffineLine
    (p : Ideal (CoordinatePolynomial 3)) [p.IsPrime] (hp : p.height = 2)
    (hdegree : HasAffineCurveDegree p 1)
    (z : RatPoint 3) (hz : z ∈ idealZeroLocus p) :
    ∃ v : RatPoint 3, v ≠ 0 ∧ idealZeroLocus p = rationalAffineLine z v ∧
      ∀ f ∈ p, MvPolynomial.aeval
        (fun k => Polynomial.C (z k) + Polynomial.C (v k) * Polynomial.X) f = 0 := by
  obtain ⟨N, b, hN⟩ := hdegree
  obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point p hp z hz
  have hdim : Module.finrank ℚ (filteredCoordinateSpace p (N + 1)) =
      Module.finrank ℚ (filteredCoordinateSpace p N) + 1 := by
    have h0 := hN N le_rfl; have h1 := hN (N + 1) (by omega)
    dsimp only [affineHilbertFunction, filteredCoordinateSpace] at h0 h1 ⊢
    push_cast at h0 h1; omega
  have hUone : (1 : CoordinatePolynomial 3 ⧸ p) ∈ filteredCoordinateSpace p N :=
    Submodule.mem_map.mpr ⟨1, by rw [mem_restrictTotalDegree, totalDegree_one]; omega, by simp⟩
  have hmul (k : Fin 3) (u : CoordinatePolynomial 3 ⧸ p)
      (hu : u ∈ filteredCoordinateSpace p N) :
      (Ideal.Quotient.mk p) (X k) * u ∈ filteredCoordinateSpace p (N + 1) := by
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hu
    refine Submodule.mem_map.mpr ⟨X k * f, ?_, by simp⟩
    rw [mem_restrictTotalDegree] at hf ⊢
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)
  choose c d hcd using fun k : Fin 3 =>
    affine_of_critical_growth_of_point (coordinatePoint p z hz)
      (filteredCoordinateSpace p N) (filteredCoordinateSpace p (N + 1))
      (filteredCoordinateSpace_mono p (by omega)) hUone hdim hj (hmul j) (hmul k)
  have hcj : c j ≠ 0 := fun hc => hj (by
    have he := hcd j; rw [hc, zero_smul, zero_add] at he; rw [he]; exact isAlgebraic_algebraMap _)
  have hpoint (x : RatPoint 3) (hx : x ∈ idealZeroLocus p) (k : Fin 3) :
      x k = c k * x j + d k := by
    simpa only [coordinatePoint_mk, eval_X, map_add, map_smul,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul] using
      congrArg (coordinatePoint p x hx) (hcd k)
  have hpoly (f : CoordinatePolynomial 3) (hf : f ∈ p) :
      MvPolynomial.aeval
        (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) f = 0 := by
    let x := (Ideal.Quotient.mk p) (X j)
    let φ : CoordinatePolynomial 3 →ₐ[ℚ] Polynomial ℚ :=
      MvPolynomial.aeval (fun k => Polynomial.C (d k) + Polynomial.C (c k) * Polynomial.X)
    have hsmul (k : Fin 3) : c k • x = algebraMap ℚ _ (c k) * x :=
      Algebra.smul_def (R := ℚ) (A := CoordinatePolynomial 3 ⧸ p) (c k) x
    have hcomp : (Polynomial.aeval x).comp φ = Ideal.Quotient.mkₐ ℚ p :=
      MvPolynomial.algHom_ext fun k => by
        simp only [AlgHom.comp_apply, φ, aeval_X, map_add, map_mul,
          Polynomial.aeval_C, Polynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk, hcd k]
        rw [show c k • (Ideal.Quotient.mk p) (X j) = algebraMap ℚ _ (c k) * x from hsmul k]
        exact add_comm _ _
    have hφ : φ f = 0 := (transcendental_iff_injective.mp hj) (by
      change ((Polynomial.aeval x).comp φ) f = _
      rw [hcomp]; simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hf)
    have htranslate :
        (Polynomial.aeval (Polynomial.C (z j) + Polynomial.X)).comp φ =
        MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) :=
      MvPolynomial.algHom_ext fun k => by
        simp only [AlgHom.comp_apply, φ, aeval_X, map_add, map_mul,
          Polynomial.aeval_C, Polynomial.aeval_X]
        rw [hpoint z hz k]
        simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.algebraMap_eq]
        ring
    rw [← htranslate, AlgHom.comp_apply, hφ, map_zero]
  refine ⟨c, fun h => hcj (congrFun h j), ?_, hpoly⟩
  ext x
  refine ⟨fun hx => ⟨x j - z j, funext fun k => ?_⟩, ?_⟩
  · change x k = z k + (x j - z j) * c k
    rw [hpoint x hx k, hpoint z hz k]; ring
  · rintro ⟨t, rfl⟩ f hf
    have he : (Polynomial.aeval t).comp
        (MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X)) =
        MvPolynomial.aeval (z + t • c) :=
      MvPolynomial.algHom_ext fun k => by
        simp only [AlgHom.comp_apply, aeval_X, map_add, map_mul,
          Polynomial.aeval_C, Polynomial.aeval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Algebra.algebraMap_self, RingHom.id_apply]
        ring
    have hz' := congrArg (Polynomial.aeval t) (hpoly f hf)
    change ((Polynomial.aeval t).comp
      (MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X))) f =
        (Polynomial.aeval t) 0 at hz'
    rwa [he, map_zero, MvPolynomial.aeval_eq_eval] at hz'

end
end CCDN
