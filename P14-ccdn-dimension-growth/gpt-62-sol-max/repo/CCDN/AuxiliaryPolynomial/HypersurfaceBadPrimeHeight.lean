/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
public import CCDN.Plane.IntegerPlaneLogHeight
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.Noether.UniversalPlaneBadWitness
import CCDN.Plane.FullDegreeSectionIrreducibility
import CCDN.ForMathlib.MvPolynomial
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.ClosedFormMinorCharge

/-! One bounded integral plane section supplies a nonzero witness for all bad primes.
The logarithmic height of that witness controls the bad-prime charge. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma universalPlaneBadWitness_eval {σ : Type*}
    (f : MvPolynomial σ ℤ)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) :
    eval v (universalPlaneBadWitness f rows cols) =
      ((universalPlaneSection f v).coeff f.totalDegree).coeff 0 *
        ((closedFormCoefficientMatrix f.totalDegree (universalPlaneSection f v)).submatrix
          rows cols).det := by
  rw [universalPlaneBadWitness, map_mul, closedForm_minor_map]
  congr 1
  exact (bivariateMap_coeff (eval v) (universalPlanePolynomial f) f.totalDegree 0).symm

/-- The evaluated witness is a leading coefficient times an integer
minor; both are controlled by the height of the same plane section. -/
private theorem universalPlaneBadWitness_eval_log_bound {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (hd : 1 ≤ f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) (S : ℝ) (hS : 1 ≤ S)
    (hf : BivariateCoefficientBound (universalPlaneSection f v) S)
    (hw : eval v (universalPlaneBadWitness f rows cols) ≠ 0) :
    Real.log |(eval v (universalPlaneBadWitness f rows cols) : ℝ)| ≤
      Real.log S + (27 * (f.totalDegree : ℝ) ^ 4) *
        (1 + Real.log S / (f.totalDegree : ℝ) ^ 2) := by
  let g := universalPlaneSection f v
  let c := (g.coeff f.totalDegree).coeff 0
  let D := ((closedFormCoefficientMatrix f.totalDegree g).submatrix rows cols).det
  have he : eval v (universalPlaneBadWitness f rows cols) = c * D :=
    universalPlaneBadWitness_eval f rows cols v
  have hc : c ≠ 0 := fun h => hw (by simp_all)
  have hD : D ≠ 0 := fun h => hw (by simp_all)
  have ht :=
    universalPlanePolynomial_specialization_totalDegree f (eval v)
  have hb := closedForm_minor_log_height f.totalDegree (2 * f.totalDegree ^ 2 - 1)
    hd (Nat.sub_le _ _) g S hS hf
    ((bivariate_natDegree_le_totalDegree g).trans ht)
    (fun i => (bivariate_coefficient_natDegree_le_totalDegree g i).trans ht) rows cols hD
  have hl := Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc)) (hf f.totalDegree 0)
  rw [he, Int.cast_mul, abs_mul, Real.log_mul
    (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hc)) (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hD))]
  linarith

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma bad_prime_dvd_universalPlaneBadWitness_eval {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (hpos : 0 < f.totalDegree)
    (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
    (v : PlaneParameters σ → ℤ) (p : ℕ)
    (hp : f.totalDegree < p) (hbad : HypersurfaceBadReduction f p) :
    (p : ℤ) ∣ eval v (universalPlaneBadWitness f rows cols) := by
  classical
  obtain ⟨hpprime, hbad⟩ := hbad
  let : Fact p.Prime := ⟨hpprime⟩
  let L := AlgebraicClosure (ZMod p)
  let φ := Int.castRingHom L
  let w := φ ∘ v
  let ψ := (eval w).comp (MvPolynomial.map φ)
  apply (CharP.intCast_eq_zero_iff L p _).mp
  change φ (eval v _) = 0
  rw [map_eval]
  change ψ _ = 0
  by_contra h
  obtain ⟨hdeg, hir⟩ := universalPlaneBadWitness_good_specialization
    f hpos (.of_charP hp) rows cols ψ h
  have he : universalPlaneSection (MvPolynomial.map φ f) w =
      bivariateMap ψ (universalPlanePolynomial f) := by
    rw [universalPlaneSection, universalPlanePolynomial_map, ← bivariateMap_comp_apply]
  have hs := universalPlanePolynomial_specialization_totalDegree (MvPolynomial.map φ f) (eval w)
  change bivariateTotalDegree (universalPlaneSection (MvPolynomial.map φ f) w) ≤ _ at hs
  rw [he, hdeg] at hs
  have hd := le_antisymm (totalDegree_map_le φ f) hs
  exact hbad.elim (fun hn => hn hd) (fun hn => hn
    (irreducible_of_full_degree_planeSection _ w (he ▸ hir) (by rw [he, hdeg, hd])))

/-- The universal plane bad-prime witness of an absolutely irreducible integer polynomial
takes a nonzero value at some integer parameter in the box `[0, 2d³]`, and every prime above
`d` with bad geometric reduction divides that value. -/
private theorem exists_bounded_integer_plane_witness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree)
      (v : PlaneParameters (Option σ) → ℤ),
      (∀ i, 0 ≤ v i ∧ v i ≤ (2 * f.totalDegree ^ 3 : ℕ)) ∧
      eval v (universalPlaneBadWitness f rows cols) ≠ 0 ∧
      ∀ p : ℕ, f.totalDegree < p → HypersurfaceBadReduction f p →
        (p : ℤ) ∣ eval v (universalPlaneBadWitness f rows cols) := by
  obtain ⟨rows, cols, hw, hd⟩ := exists_universalPlane_badWitness f _ Int.cast_injective hf hpos (.of_charZero _)
  obtain ⟨v, hv, he⟩ := exists_integer_grid_eval_ne_zero _ hw _ hd
  exact ⟨rows, cols, v, hv, he,
    fun p hp hbad => bad_prime_dvd_universalPlaneBadWitness_eval f hpos rows cols v p hp hbad⟩

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- An effective positive integer detecting every bad prime above the degree. -/
theorem exists_hypersurface_bad_prime_height_witness
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Fintype σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (f.totalDegree : ℝ) ^ 4) *
        (hypersurfaceHeightConstant (Fintype.card (Option σ)) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) ∧
      ∀ p : ℕ, f.totalDegree < p → HypersurfaceBadReduction f p → (p : ℤ) ∣ D := by
  obtain ⟨rows, cols, v, hv, hw, hdiv⟩ := exists_bounded_integer_plane_witness f hf hpos
  let S := integerPlaneHeight (Fintype.card (Option σ)) f.totalDegree H
    (2 * (f.totalDegree : ℝ) ^ 3)
  have hd := hpos
  have hdR : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hA : 1 ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by nlinarith [one_le_pow₀ hdR (n := 3)]
  have hv' (i : PlaneParameters (Option σ)) : |(v i : ℝ)| ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by
    rw [abs_of_nonneg (by simp_all)]
    exact_mod_cast (hv i).2
  have hS : 1 ≤ S := integerPlaneHeight_one_le _ _ hd H hH
  have hcoeffS : BivariateCoefficientBound (universalPlaneSection f v) S :=
    integer_plane_section_coefficient_bound f H _ (by linarith) hA hcoeff v hv'
  refine ⟨|eval v (universalPlaneBadWitness f rows cols)|, abs_pos.mpr hw, ?_, ?_⟩
  · rw [Int.cast_abs]
    exact (universalPlaneBadWitness_eval_log_bound f hd rows cols v S hS hcoeffS hw).trans
      (integerPlaneHeight_scaled_log_le _ _ hd H hH)
  · intro p hp hbad
    exact (dvd_abs _ _).mpr (hdiv p hp hbad)

end
end CCDN
