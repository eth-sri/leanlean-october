/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.UniversalPlaneBadWitness
public import Mathlib.Algebra.Field.ZMod
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.FullDegreeSectionIrreducibility
import Mathlib.Algebra.MvPolynomial.Funext

/-! All coefficients of the universal witness vanish at a degree-dropping or
reducible ambient reduction. A nonzero integer coefficient therefore detects
every sufficiently large bad prime, in arbitrary ambient dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

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
  let φ := Int.castRingHom L
  have hz : MvPolynomial.map φ (universalPlaneBadWitness f rows cols) = 0 := by
    apply MvPolynomial.funext; intro v; rw [map_zero]; by_contra h
    let ψ : MvPolynomial (PlaneParameters σ) ℤ →+* L := (eval v).comp (MvPolynomial.map φ)
    have hg := universalPlaneBadWitness_good_specialization f hpos (.of_charP hp) rows cols ψ h
    have he : universalPlaneSection (MvPolynomial.map φ f) v =
        bivariateMap ψ (universalPlanePolynomial f) := by
      rw [universalPlaneSection, universalPlanePolynomial_map, ← bivariateMap_comp_apply]
    have hs := universalPlanePolynomial_specialization_totalDegree (MvPolynomial.map φ f) (eval v)
    change bivariateTotalDegree (universalPlaneSection (MvPolynomial.map φ f) v) ≤ _ at hs
    rw [he, hg.2.1] at hs
    have hd : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      le_antisymm (totalDegree_map_le _ _) hs
    exact hbad.elim (fun hh => hh hd) fun hh =>
      hh (irreducible_of_full_degree_planeSection _ v (he ▸ hg.2.2) (by rw [he, hg.2.1, hd]))
  have hc := congrArg (fun W : MvPolynomial (PlaneParameters σ) L => W.coeff e) hz
  rw [coeff_map] at hc
  exact (CharP.intCast_eq_zero_iff L p _).mp hc

/-- A nonzero integer divisible by every bad prime larger than the
degree. The witness is a coefficient of the constructed universal polynomial,
so later coefficient-height bounds apply to this same integer. -/
theorem exists_integer_hypersurface_bad_prime_witness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
      (e : PlaneParameters (Option σ) →₀ ℕ),
      (universalPlaneBadWitness f rows cols).coeff e ≠ 0 ∧
      ∀ (p : ℕ) [Fact p.Prime], f.totalDegree < p →
        ((MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree ≠
            f.totalDegree ∨
          ¬Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f)) →
        (p : ℤ) ∣ (universalPlaneBadWitness f rows cols).coeff e := by
  obtain ⟨rows, cols, hw, _⟩ := exists_integer_universalPlane_badWitness f hf hpos
  obtain ⟨e, he⟩ : ∃ e, (universalPlaneBadWitness f rows cols).coeff e ≠ 0 := by
    by_contra! hn; exact hw (MvPolynomial.ext _ _ hn)
  exact ⟨rows, cols, e, he, fun p _ hp hbad =>
    bad_prime_dvd_universalPlaneBadWitness_coeff f hpos rows cols p hp hbad e⟩

end
end CCDN
