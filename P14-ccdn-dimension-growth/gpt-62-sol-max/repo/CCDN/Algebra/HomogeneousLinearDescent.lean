/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialLinearDescent
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Auxiliaries obtained by descending the factors of a nonabsolute equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The homogeneous component of `g * h` in degree `g.totalDegree + h.totalDegree` is the
product of the top-degree homogeneous components of `g` and `h`. -/
lemma top_homogeneousComponent_mul {K σ : Type*} [CommRing K]
    (g h : MvPolynomial σ K) :
    homogeneousComponent (g.totalDegree + h.totalDegree) (g * h) =
      homogeneousComponent g.totalDegree g * homogeneousComponent h.totalDegree h := by
  classical
  calc
    _ = homogeneousComponent (g.totalDegree + h.totalDegree)
        ((∑ i ∈ Finset.range (g.totalDegree + 1), homogeneousComponent i g) * h) := by
      rw [sum_homogeneousComponent]
    _ = ∑ i ∈ Finset.range (g.totalDegree + 1),
        homogeneousComponent (g.totalDegree + h.totalDegree) (homogeneousComponent i g * h) := by
      rw [Finset.sum_mul, map_sum]
    _ = homogeneousComponent (g.totalDegree + h.totalDegree)
        (homogeneousComponent g.totalDegree g * h) := by
      apply Finset.sum_eq_single g.totalDegree
      · intro i hi hne
        have hi' : i < g.totalDegree := by grind
        apply homogeneousComponent_eq_zero
        have hh := totalDegree_mul (homogeneousComponent i g) h
        have hh' := (homogeneousComponent_isHomogeneous i g).totalDegree_le
        omega
      simp
    _ = _ := homogeneousComponent_mul_of_isHomogeneous_left
      (homogeneousComponent_isHomogeneous _ _) h _

/-- A proper factorization over an extension produces a base-field auxiliary of
no greater degree, homogeneous when the original equation is homogeneous. -/
theorem nonabsolute_auxiliary {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    (f : MvPolynomial σ k) (hf : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ q : MvPolynomial σ k, q ≠ 0 ∧ q.totalDegree ≤ f.totalDegree ∧ ¬ f ∣ q ∧
      (∀ d, f.IsHomogeneous d → q.IsHomogeneous d) ∧
      ∀ x : σ → k, eval x f = 0 → eval x q = 0 := by
  let F := map (algebraMap k K) f
  have hF : F ≠ 0 := fun h => hf.ne_zero ((map_injective _ (algebraMap k K).injective)
    (h.trans (map_zero _).symm))
  have hdeg : F.totalDegree = f.totalDegree := totalDegree_map_of_injective (algebraMap k K).injective _
  have hFnu : ¬ IsUnit F := fun h => (totalDegree_pos_of_irreducible hf).ne'
    (hdeg ▸ (isUnit_iff_totalDegree_of_isReduced.mp h).2)
  obtain ⟨g, h, he, hgu, hhu⟩ : ∃ g h, F = g * h ∧ ¬ IsUnit g ∧ ¬ IsUnit h := by
    by_contra! H
    exact hred ⟨hFnu, by tauto⟩
  have hg : g ≠ 0 := fun e => hF (by simp_all)
  have hh : h ≠ 0 := fun e => hF (by simp_all)
  have hgd := totalDegree_pos_of_ne_zero_of_not_isUnit hg hgu
  have hhd := totalDegree_pos_of_ne_zero_of_not_isUnit hh hhu
  have hsum : g.totalDegree + h.totalDegree = f.totalDegree := by
    rw [← hdeg, he, totalDegree_mul_of_isDomain hg hh]
  suffices ∃ g' h' : MvPolynomial σ K, F = g' * h' ∧ g' ≠ 0 ∧ h' ≠ 0 ∧
      g'.totalDegree = g.totalDegree ∧ h'.totalDegree = h.totalDegree ∧
      (f.IsHomogeneous f.totalDegree → g'.IsHomogeneous g.totalDegree ∧ h'.IsHomogeneous h.totalDegree) by
    obtain ⟨g', h', hfac, hg', hh', hgd', hhd', hhom⟩ := this
    obtain ⟨p, hp, hpd, hph, hpz⟩ := exists_nonzero_polynomial_linear_descent (k := k) g' hg'
    obtain ⟨q, hq, hqd, hqh, hqz⟩ := exists_nonzero_polynomial_linear_descent (k := k) h' hh'
    refine ⟨p * q, mul_ne_zero hp hq, (totalDegree_mul _ _).trans (by omega), ?_, ?_, ?_⟩
    · intro hfdiv
      rcases hf.prime.dvd_or_dvd hfdiv with H | H
      · have := totalDegree_le_of_dvd_of_isDomain H hp
        omega
      · have := totalDegree_le_of_dvd_of_isDomain H hq
        omega
    · intro d hd
      have hd' := hd.totalDegree hf.ne_zero
      obtain ⟨H₁, H₂⟩ := hhom (hd' ▸ hd)
      exact (hsum.trans hd') ▸ (hph _ H₁).mul (hqh _ H₂)
    · intro x hx
      have hz := congrArg (algebraMap k K) hx
      rw [map_eval, show map (algebraMap k K) f = F from rfl, hfac, eval_mul, map_zero] at hz
      rw [eval_mul]
      exact mul_eq_zero.mpr ((mul_eq_zero.mp hz).imp (hpz x) (hqz x))
  by_cases H : f.IsHomogeneous f.totalDegree
  · have H₁ := homogeneousComponent_isHomogeneous g.totalDegree g
    have H₂ := homogeneousComponent_isHomogeneous h.totalDegree h
    have e₁ := homogeneousComponent_totalDegree_ne_zero hg
    have e₂ := homogeneousComponent_totalDegree_ne_zero hh
    refine ⟨_, _, ?_, e₁, e₂, H₁.totalDegree e₁, H₂.totalDegree e₂, fun _ => ⟨H₁, H₂⟩⟩
    rw [← top_homogeneousComponent_mul, ← he, hsum, homogeneousComponent_eq_self (H.map _)]
  · exact ⟨g, h, he, hg, hh, rfl, rfl, fun h => (H h).elim⟩

end
end CCDN
