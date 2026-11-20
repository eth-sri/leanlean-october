/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Ideal.Height
import CCDN.Algebra.PolynomialLinearDescent
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! CCDN Corollary 4.1.4 for irreducible affine hypersurfaces in three
variables. Splitting of the full equation over any field extension gives
an auxiliary equation of degree at most d. The prime curve
components of the resulting section have total degree at most d², giving
the sharp elementary bound d²(2B+1), whatever the highest homogeneous
component. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Linear descent of both proper factors produces a base-field auxiliary
equation vanishing at every base-field zero, with degree at most d. -/
theorem nonabsolute_affine_auxiliary {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n : ℕ}
    (f : MvPolynomial (Fin n) k) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ q : MvPolynomial (Fin n) k, q ≠ 0 ∧
      q.totalDegree ≤ f.totalDegree ∧ ¬ f ∣ q ∧
      ∀ x : Fin n → k, eval x f = 0 → eval x q = 0 := by
  have hd := totalDegree_pos_of_ne_zero_of_not_isUnit hir.ne_zero hir.not_isUnit
  have hmap0 : map (algebraMap k K) f ≠ 0 := by
    intro he
    apply hir.ne_zero
    exact map_injective (algebraMap k K) (algebraMap k K).injective (by simpa using he)
  have hmapd : (map (algebraMap k K) f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective (algebraMap k K).injective _
  have hmapu : ¬ IsUnit (map (algebraMap k K) f) := by
    intro hu
    have he := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  have hfac : ∃ g h : MvPolynomial (Fin n) K,
      map (algebraMap k K) f = g * h ∧ ¬ IsUnit g ∧ ¬ IsUnit h := by
    by_contra! hn
    apply hred
    refine ⟨hmapu, ?_⟩
    grind
  obtain ⟨g, h, hfac, hgu, hhu⟩ := hfac
  have hg0 : g ≠ 0 := by grind
  have hh0 : h ≠ 0 := by grind
  have hgd := totalDegree_pos_of_ne_zero_of_not_isUnit hg0 hgu
  have hhd := totalDegree_pos_of_ne_zero_of_not_isUnit hh0 hhu
  have hdegrees := by
    rw [hfac, totalDegree_mul_of_isDomain hg0 hh0] at hmapd
    exact hmapd
  obtain ⟨g₀, hg₀, hgd₀, hgz⟩ := exists_nonzero_polynomial_linear_descent (k := k) g hg0
  obtain ⟨h₀, hh₀, hhd₀, hhz⟩ := exists_nonzero_polynomial_linear_descent (k := k) h hh0
  refine ⟨g₀ * h₀, mul_ne_zero hg₀ hh₀, ?_, ?_, ?_⟩
  · rw [totalDegree_mul_of_isDomain hg₀ hh₀]
    omega
  · intro hdiv
    rcases hir.prime.dvd_or_dvd hdiv with hgdiv | hhdiv
    · have he := totalDegree_le_of_dvd_of_isDomain hgdiv hg₀
      omega
    · have he := totalDegree_le_of_dvd_of_isDomain hhdiv hh₀
      omega
  · intro x hx
    have he := congrArg (algebraMap k K) hx
    rw [map_eval, hfac, eval_mul, map_zero] at he
    rcases mul_eq_zero.mp he with hgzero | hhzero
    aesop
    aesop

end
end CCDN
