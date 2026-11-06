/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.UniversalPlaneBadWitness
import Mathlib.Algebra.Field.ZMod
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.FullDegreeSectionIrreducibility
import Mathlib.Algebra.MvPolynomial.Funext

/-! All coefficients of the universal witness vanish at a degree-dropping or
reducible ambient reduction. A nonzero integer coefficient therefore detects
every sufficiently large bad prime, in arbitrary ambient dimension. -/

namespace CCDN
section
open MvPolynomial

/-- Bad ambient reduction forces the ENTIRE parameter polynomial to vanish.
The target field is infinite, so it suffices to inspect sections. -/
theorem universalPlaneBadWitness_map_eq_zero_of_bad
    {R L σ : Type*} [CommRing R] [Field L] [Infinite L] {p : ℕ} [CharP L p]
    (φ : R →+* L) (f : MvPolynomial σ R) (hpos : 0 < f.totalDegree)
    (hchar : f.totalDegree < p)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (hbad : (MvPolynomial.map φ f).totalDegree ≠ f.totalDegree ∨
      ¬Irreducible (MvPolynomial.map φ f)) :
    MvPolynomial.map φ (universalPlaneBadWitness f rows cols) = 0 := by
  apply MvPolynomial.funext
  intro v
  rw [map_zero]
  by_contra h
  let ψ : MvPolynomial (PlaneParameters σ) R →+* L := (eval v).comp (MvPolynomial.map φ)
  have hg := universalPlaneBadWitness_good_specialization f hpos (.of_charP hchar) rows cols ψ h
  have he : universalPlaneSection (MvPolynomial.map φ f) v =
      bivariateMap ψ (universalPlanePolynomial f) := by
    rw [universalPlaneSection, universalPlanePolynomial_map, ← bivariateMap_comp_apply]
  have hs := universalPlanePolynomial_specialization_totalDegree (MvPolynomial.map φ f) (eval v)
  change bivariateTotalDegree (universalPlaneSection (MvPolynomial.map φ f) v) ≤ _ at hs
  rw [he, hg.1] at hs
  have hd := le_antisymm (totalDegree_map_le _ _) hs
  have hi :=
    irreducible_of_full_degree_planeSection _ v (he ▸ hg.2) (by grind)
  exact hbad.elim (fun hh => hh hd) (fun hh => hh hi)

/-- Every coefficient is divisible by a bad prime above the degree. Degree
loss, including the zero reduction, is included in the predicate. -/
theorem bad_prime_dvd_universalPlaneBadWitness_coeff
    {σ : Type*} (f : MvPolynomial σ ℤ) (hpos : 0 < f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (p : ℕ) [Fact p.Prime] (hp : f.totalDegree < p)
    (hbad : (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree ≠
        f.totalDegree ∨
      ¬Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f))
    (e : PlaneParameters σ →₀ ℕ) :
    (p : ℤ) ∣ (universalPlaneBadWitness f rows cols).coeff e := by
  let L := AlgebraicClosure (ZMod p)
  have hz :=
    universalPlaneBadWitness_map_eq_zero_of_bad (Int.castRingHom L) f hpos hp rows cols hbad
  have hc := congrArg (fun W => W.coeff e) hz
  rw [coeff_map] at hc
  exact (CharP.intCast_eq_zero_iff L p _).mp hc

