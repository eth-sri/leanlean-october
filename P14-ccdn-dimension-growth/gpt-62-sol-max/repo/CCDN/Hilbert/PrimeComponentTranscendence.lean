/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.ForMathlib.KrullHeight
public import CCDN.Hilbert.FilteredIntersection
import CCDN.Hilbert.FilteredHilbertLinearity
import CCDN.Hilbert.CoordinateIndependence
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! A point on a prime component forces a transcendental coordinate and
 positive eventual Hilbert slope in codimension two. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A rational point's evaluation kernel has height equal to the number of variables. -/
private lemma height_ker_eval {K : Type*} [Field K] (n : ℕ) (z : Fin n → K) :
    (RingHom.ker (eval z)).height = n := by
  induction n with
  | zero =>
    have h : Function.Injective (eval z) := by
      intro f g hfg
      obtain ⟨a, rfl⟩ := (C_surjective (σ := Fin 0) (R := K)) f
      obtain ⟨b, rfl⟩ := (C_surjective (σ := Fin 0) (R := K)) g
      simpa using hfg
    simp [(RingHom.injective_iff_ker_eq_bot _).mp h]
  | succ n ih =>
    let e := MvPolynomial.finSuccEquiv K n
    let φ := eval (z ∘ Fin.succ)
    let ψ := Polynomial.eval₂RingHom φ (z 0)
    have he : ψ.comp e.toRingHom = eval z := by
      apply MvPolynomial.ringHom_ext
      · simp [ψ, φ, e, finSuccEquiv_apply]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [ψ, φ, e, finSuccEquiv_X_zero, finSuccEquiv_X_succ]
    let : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ fun a =>
      ⟨Polynomial.C (C a), by simp [ψ, φ]⟩
    let : (RingHom.ker ψ).LiesOver (RingHom.ker φ) := ⟨by
      change RingHom.ker φ = RingHom.ker (ψ.comp Polynomial.C)
      rw [Polynomial.eval₂RingHom_comp_C]⟩
    rw [← he, show RingHom.ker (ψ.comp e.toRingHom) = (RingHom.ker ψ).comap e.toRingEquiv from rfl,
      e.toRingEquiv.height_comap, Polynomial.height_eq_height_add_one (RingHom.ker φ), ih]
    push_cast
    rfl

/-- An algebraic element detected by a base-field-valued point is scalar. -/
private lemma algebraic_eq_scalar_of_point {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (φ : A →ₐ[K] K) {y : A} (hy : IsAlgebraic K y) :
    algebraMap K A (φ y) = y := by
  by_contra! h
  have hu := (hy.isIntegral.sub (isIntegral_algebraMap (x := φ y))).isUnit (sub_ne_zero.mpr h.symm)
  simpa using hu.map φ

/-- Evaluation at a rational point descends to its prime coordinate ring. -/
def coordinatePoint {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ idealZeroLocus p) :
    (MvPolynomial σ K ⧸ p) →ₐ[K] K :=
  Ideal.Quotient.liftₐ p (MvPolynomial.aeval z) (by
    assumption)

/-- Evaluation at the point `z` sends the class of `f` to `f(z)`. -/
@[simp] lemma coordinatePoint_mk {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ idealZeroLocus p)
    (f : MvPolynomial σ K) :
    coordinatePoint p z hz ((Ideal.Quotient.mk p) f) = MvPolynomial.eval z f := by
  rfl

/-- A positive eventual slope supplies a transcendental coordinate even without a rational point. -/
theorem exists_transcendental_coordinate_of_curve {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] {d : ℕ} (hd : 0 < d)
    (hdegree : HasFilteredCurveDegree I d) :
    ∃ j, Transcendental K ((Ideal.Quotient.mk I) (X j)) := by
  obtain ⟨U, hU, h⟩ := exists_hilbert_dimension_independent_coordinates I (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  rw [hdegree.natDegree_eq_one hd] at hU
  have : Nonempty U := Nat.card_pos_iff.mp (by omega) |>.1
  exact ⟨(Classical.choice this).val, h.transcendental _⟩

section

variable {K : Type*} [Field K]
  (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height ≤ 2)
  (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p)
include K p hp z hz

/-- A height-two prime in three variables containing a rational point retains a
transcendental coordinate over its base field. -/
private theorem height_two_transcendental_coordinate_of_point :
    ∃ j : Fin 3, Transcendental K ((Ideal.Quotient.mk p) (X j)) := by
  by_contra! h
  let A := MvPolynomial (Fin 3) K ⧸ p
  have he : Ideal.Quotient.mkₐ K p = (Algebra.ofId K A).comp (aeval z) := by
    ext j
    rw [AlgHom.comp_apply, aeval_X, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk]
    simpa using (algebraic_eq_scalar_of_point (coordinatePoint p z hz)
      (show IsAlgebraic K ((Ideal.Quotient.mk p) (X j)) by simpa [Transcendental] using h j)).symm
  have hle : RingHom.ker (eval z) ≤ p := by
    intro f hf
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ K p f = 0
    rw [he, AlgHom.comp_apply, show aeval z f = 0 from hf, map_zero]
  have hd := Ideal.height_mono hle
  rw [height_ker_eval] at hd
  norm_num at hp hd ⊢
  exact (by decide : ¬ (3 : ℕ∞) ≤ 2) (hd.trans hp)

/-- A height-two component with a base-field point has positive slope in
 any eventual linear Hilbert formula, independently of its cutoff. -/
theorem height_two_eventual_slope_pos_of_point {d : ℕ}
    (hlinear : HasFilteredCurveDegree p d) :
    0 < d := by
  obtain ⟨N, c, hlinear⟩ := hlinear
  obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point p hp z hz
  by_contra h
  have hd0 : d = 0 := by omega
  have hlo := transcendental_coordinate_filtered_lower p hj (N + c.natAbs)
  have hhi := hlinear (N + c.natAbs) (by omega)
  rw [hd0] at hhi
  omega

end

end
end CCDN
