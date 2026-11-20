/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Plane.IntegralAffineLine
public import CCDN.Algebra.AffineLineLeading
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Algebra.PolynomialSection
import CCDN.Hilbert.PrimeComponentTranscendence

@[expose] public section
namespace CCDN
open MvPolynomial
noncomputable section

/-- On a degree-one prime, every hyperplane through two distinct points
contains the curve. Using their separating coordinate as parameter identifies
its ideal with that of the secant line. -/
theorem degree_one_secant (P : Ideal (CoordinatePolynomial 3)) [P.IsPrime]
    (deg : HasAffineCurveDegree P 1) {a b : RatPoint 3} (ha : a ∈ idealZeroLocus P)
    (hb : b ∈ idealZeroLocus P) (hab : a ≠ b) :
    ∃ v, idealZeroLocus P = rationalAffineLine a v ∧
      ∀ f, f ∈ P ↔ rationalAffineLine a v ⊆ zeroLocus f := by
  classical
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hab
  let v (i : Fin 3) := (b i - a i)/(b j - a j)
  let t (x : RatPoint 3) := x j - a j
  have rel (i : Fin 3)  := by
    by_contra h
    let z : Bool → RatPoint 3 := fun k => if k then b else a
    have hi : Function.Injective z := by intro x y; cases x <;> cases y <;> simp_all [z,hab.symm]
    have hdeg : (X i - (C (a i)+C (v i)*(X j-C (a j))):CoordinatePolynomial 3).totalDegree ≤ 1 := by
      refine (totalDegree_sub ..).trans (max_le ?_ ((totalDegree_add ..).trans (max_le ?_ ((totalDegree_mul ..).trans ?_)))) <;> simp
      exact (totalDegree_sub ..).trans (by simp)
    have hh := polynomial_section_card_le_degree P 1 deg _ h 1 hdeg z hi
      (by intro k; cases k <;> assumption) (by intro k; cases k <;> simp [z,v,field,sub_ne_zero.mpr hj.symm])
    simp at hh
  let τ := Ideal.Quotient.mk P (X j - C (a j))
  have trans : Transcendental ℚ τ := by
    intro h
    have he := congrArg (coordinatePoint P b hb) (algebraic_eq_scalar_of_point (coordinatePoint P a ha) h)
    simp [τ] at he; exact hj (by linarith)
  let φ := affineLinePolynomial a v
  have hC (r : ℚ) : algebraMap ℚ _ r = Ideal.Quotient.mk P (C r) := ((Ideal.Quotient.mkₐ ℚ P).commutes r).symm
  have comp : (Polynomial.aeval τ).toRingHom.comp φ = Ideal.Quotient.mk P := by
    apply MvPolynomial.ringHom_ext
    · simp [φ,affineLinePolynomial,hC]
    · intro i
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr (rel i)
      simp only [map_sub, map_add, map_mul, sub_eq_zero] at hh
      simpa [φ,affineLinePolynomial,τ,hC] using hh.symm
  have mem (f : CoordinatePolynomial 3) : f ∈ P ↔ rationalAffineLine a v ⊆ zeroLocus f := by
    rw [← Ideal.Quotient.eq_zero_iff_mem,← comp,RingHom.comp_apply]
    constructor
    · intro h x ⟨r,hr⟩
      have hz : φ f = 0 := (transcendental_iff_injective.mp trans) (by simpa using h)
      change eval x f = 0
      rw [hr,← eval_affineLinePolynomial]; simp_all [φ]
    · intro h
      have hz : φ f = 0 := Polynomial.zero_of_eval_zero _ fun r => by rw [eval_affineLinePolynomial]; exact h ⟨r,rfl⟩
      simp [hz]
  refine ⟨v,Set.Subset.antisymm (fun x hx => ⟨t x,?_⟩) (fun x hx f hf => (mem f).mp hf hx),mem⟩
  funext i
  simpa [t,mul_comm,sub_eq_zero] using (hx _ (rel i))

end
end CCDN
