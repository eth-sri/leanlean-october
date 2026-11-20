/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousSlice
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.ForMathlib.MvPolynomial

/-! Prime scaling changes the geometric bad-prime factor by at most an
absolute constant. Outside the scaling prime, the homogeneous models are
related by an invertible change of coordinates and a nonzero scalar. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma firstCoordinateScaleHom_scaledHomogenize {R : Type*} [CommRing R] {n d : ℕ}
    (h : R) (f : MvPolynomial (Fin n) R) (hd : f.totalDegree ≤ d) :
    firstCoordinateScaleHom R h (scaledHomogenize d h f) =
      C (h ^ d) * scaledHomogenize d 1 f := by
  apply affineChart_injective_on_homogeneous
    (firstCoordinateScaleHom_homogeneous h (scaledHomogenize_homogeneous h f hd))
    ((scaledHomogenize_homogeneous 1 f hd).C_mul (h ^ d))
  rw [← homogeneousSlice_eq_chart_scale, homogeneousSlice_scaledHomogenize h f hd,
    map_mul, affineChart_scaledHomogenize_one]
  simp [affineChart]

private lemma scaledHomogenize_irreducible_iff {K : Type*} [Field K] {n d : ℕ}
    (h : K) (hh : h ≠ 0) (f : MvPolynomial (Fin n) K) (hd : f.totalDegree ≤ d) :
    Irreducible (scaledHomogenize d h f) ↔ Irreducible (scaledHomogenize d 1 f) := by
  have hu := IsUnit.map (C : K →+* MvPolynomial (Fin (n + 1)) K)
    (isUnit_iff_ne_zero.mpr (pow_ne_zero d hh))
  rw [← (MulEquiv.irreducible_iff (firstCoordinateScale K h hh)),
    show firstCoordinateScale K h hh (scaledHomogenize d h f) = _ from
      firstCoordinateScaleHom_scaledHomogenize h f hd, irreducible_isUnit_mul hu]

private lemma scaledHomogenize_map_irreducible_iff {K : Type*} [Field K] {n d : ℕ}
    (φ : ℤ →+* K) (h : ℤ) (hh : φ h ≠ 0)
    (f : MvPolynomial (Fin n) ℤ) (hd : f.totalDegree ≤ d) :
    Irreducible (map φ (scaledHomogenize d h f)) ↔
      Irreducible (map φ (scaledHomogenize d 1 f)) := by
  rw [scaledHomogenize_map, scaledHomogenize_map, map_one]
  apply scaledHomogenize_irreducible_iff _ hh
  exact (totalDegree_map_le _ _).trans hd

private lemma hypersurfaceBadReduction_scaledHomogenize {n d : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) (hd : f.totalDegree ≤ d)
    {p q : ℕ} (hp : p.Prime) (hqp : q ≠ p) :
    HypersurfaceBadReduction (scaledHomogenize d (p : ℤ) f) q ↔
      HypersurfaceBadReduction (scaledHomogenize d 1 f) q := by
  by_cases hq : q.Prime
  · let : Fact q.Prime := ⟨hq⟩
    have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpK : (p : AlgebraicClosure (ZMod q)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff _ q]
      exact fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)
    rw [homogeneous_hypersurfaceBadReduction_iff _ (scaledHomogenize_homogeneous _ _ hd)
        (scaledHomogenize_ne_zero d hpZ hf),
      homogeneous_hypersurfaceBadReduction_iff _ (scaledHomogenize_homogeneous _ _ hd)
        (scaledHomogenize_ne_zero d one_ne_zero hf)]
    apply not_congr
    exact scaledHomogenize_map_irreducible_iff _ (p : ℤ) (by simpa using hpK) f hd
  · constructor <;> intro h <;> exact (hq h.1).elim

/-- Prime scaling preserves all geometric bad primes away from the scaling
prime, and therefore multiplies the paper's bad-prime factor by at most `e`. -/
theorem hypersurfaceBadPrimeFactor_scaledHomogenize_le {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) {p : ℕ} (hp : p.Prime) :
    hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree (p : ℤ) f) ≤
      Real.exp 1 * hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f) := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he := hypersurfaceBadPrimeFactor_le_of_badReduction_imp
    (scaledHomogenize f.totalDegree (p : ℤ) f) (scaledHomogenize f.totalDegree 1 f) {p}
  simp only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one] at he
  apply he
  · rw [(scaledHomogenize_homogeneous (p : ℤ) f le_rfl).totalDegree
        (scaledHomogenize_ne_zero f.totalDegree hpZ hf),
      (scaledHomogenize_homogeneous (1 : ℤ) f le_rfl).totalDegree
        (scaledHomogenize_ne_zero f.totalDegree one_ne_zero hf)]
  · exact (scaledHomogenize_map_irreducible_iff _ (p : ℤ)
      (by simp_all)
      f le_rfl).mp
  · intro q hq
    exact (hypersurfaceBadReduction_scaledHomogenize f hf le_rfl hp hq).mp

end
end CCDN
