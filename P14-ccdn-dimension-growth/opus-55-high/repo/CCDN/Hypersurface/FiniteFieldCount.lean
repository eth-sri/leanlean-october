/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Plane.FiniteFieldConstants
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.SectionSum

/-!
A sharp coefficient-uniform count for geometrically irreducible affine
hypersurfaces over prime fields, proved by plane-section averaging.

Numerical absorption of bad and zero plane sections above the cutoff
p>27*d^4. The leading term remains exactly p^(m-1).
-/

namespace CCDN

/-- The unsimplified incidence estimate implies the desired sharp affine
hypersurface estimate in every ambient dimension at least three. -/
theorem hypersurface_count_of_incidence_bound (n : ℕ) {d p N : ℝ}
    (hd : 1 ≤ d) (hp : stepanovThreshold d < p)
    (hcount : N * p ^ (2 * n + 8) ≤
      p ^ (3 * n + 9) * (p + planeResidueConstant * d ^ 2 * Real.sqrt p) +
      2 * d ^ 4 * p ^ (3 * n + 9) + d ^ 3 * p ^ (3 * n + 8)) :
    N ≤ p ^ (n + 2) + hypersurfaceResidueConstant * d ^ 2 * p ^ (n + 1) * Real.sqrt p := by
  rw [planeResidueConstant_eq] at hcount
  rw [hypersurfaceResidueConstant_eq]
  have herr : 2 * d ^ 4 * p + d ^ 3 ≤ 3 * d ^ 2 * p * Real.sqrt p := by
    unfold stepanovThreshold at hp
    have hd0 : 0 ≤ d := by linarith
    have hd2 : 1 ≤ d ^ 2 := by nlinarith
    have hd4 : 1 ≤ d ^ 4 := by nlinarith
    have hp1 : 1 ≤ p := by nlinarith
    have hp0 : 0 ≤ p := by linarith
    have hs : d ^ 2 ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by grind)
    have hds : d ≤ Real.sqrt p := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * d ^ 2 * p by positivity)
    have h2 := by omega
    have h3 := mul_le_mul_of_nonneg_right hp1 (show 0 ≤ d ^ 2 * Real.sqrt p by positivity)
    nlinarith
  unfold stepanovThreshold at hp
  have hp0 := lt_of_le_of_lt (by positivity) hp
  have hmajor := mul_le_mul_of_nonneg_left herr (pow_nonneg hp0.le (3 * n + 8))
  have hfact :
      p ^ (3 * n + 9) * (p + 161 * d ^ 2 * Real.sqrt p) +
      2 * d ^ 4 * p ^ (3 * n + 9) + d ^ 3 * p ^ (3 * n + 8) ≤
      p ^ (3 * n + 8) * (p ^ 2 + 164 * d ^ 2 * p * Real.sqrt p) := by
    rw [show 3 * n + 9 = (3 * n + 8) + 1 by omega, pow_succ]
    nlinarith
  have he : p ^ (3 * n + 8) * (p ^ 2 + 164 * d ^ 2 * p * Real.sqrt p) =
      (p ^ (n + 2) + 164 * d ^ 2 * p ^ (n + 1) * Real.sqrt p) * p ^ (2 * n + 8) := by
    rw [show 3 * n + 8 = (2 * n + 8) + n by omega, pow_add]
    simp [pow_add, pow_one]
    ring
  rw [he] at hfact
  exact (mul_le_mul_iff_left₀ (pow_pos hp0 _)).mp (hcount.trans hfact)

open MvPolynomial

/-- In n+3 ambient coordinates, the leading term is p^(n+2), with an explicit
absolute square-degree square-root error. -/
theorem affine_hypersurface_finite_field_bound_option {n : ℕ}
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Option (Fin (n + 2))) (ZMod p))
    (hf : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) f))
    (hsize : stepanovThreshold (f.totalDegree : ℝ) < p) :
    (Nat.card {z : Option (Fin (n + 2)) → ZMod p // eval z f = 0} : ℝ) ≤
      (p : ℝ) ^ (n + 2) + hypersurfaceResidueConstant * (f.totalDegree : ℝ) ^ 2 *
        (p : ℝ) ^ (n + 1) * Real.sqrt p := by
  have hir :=
    mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) f hf
  have hd :=
    totalDegree_pos_of_ne_zero_of_not_isUnit hir.ne_zero hir.not_isUnit
  have hpN : 27 * f.totalDegree ^ 4 < p := mod_cast hsize
  have hbN := finite_field_bad_plane_parameters_card f hf hd (by
    have h2 : 1 ≤ f.totalDegree ^ 2 := by nlinarith
    nlinarith)
  have hzN := finite_field_zero_plane_parameters_card f hir.ne_zero
  simp at hbN hzN
  rw [show 3 * (n + 2 + 1) - 1 = 3 * n + 8 by omega] at hbN
  rw [show 3 * (n + 2) = 3 * n + 6 by omega] at hzN
  have hb : (Nat.card (BadPlaneParameters f) : ℝ) ≤
      2 * f.totalDegree ^ 3 * p ^ (3 * n + 8) := mod_cast hbN
  have hz : (Nat.card (ZeroPlaneParameters f) : ℝ) ≤
      (f.totalDegree : ℝ) ^ 3 * (p : ℝ) ^ (3 * n + 6) := mod_cast hzN
  have hi := plane_sections_incidence_bound p f hsize
  simp only [Fintype.card_option, Fintype.card_fin] at hi
  rw [show 2 * (n + 2 + 1) + 2 = 2 * n + 8 by omega,
    show 3 * (n + 2 + 1) = 3 * n + 9 by omega] at hi
  apply hypersurface_count_of_incidence_bound n (mod_cast hd) hsize
  calc
    _ ≤ p ^ (3 * n + 9) *
          (p + planeResidueConstant * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) +
        (2 * (f.totalDegree : ℝ) ^ 3 * (p : ℝ) ^ (3 * n + 8)) * (f.totalDegree * p) +
        ((f.totalDegree : ℝ) ^ 3 * (p : ℝ) ^ (3 * n + 6)) * (p : ℝ) ^ 2 := by
      exact hi.trans (add_le_add
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hb (show 0 ≤ (f.totalDegree : ℝ) * p by positivity)))
        (mul_le_mul_of_nonneg_right hz (show 0 ≤ (p : ℝ) ^ 2 by positivity)))
    _ = _ := by grind

/-- Renaming coordinates preserves the number of affine zeros. -/
lemma polynomial_zero_card_renameEquiv {K σ τ : Type*} [CommRing K]
    (e : σ ≃ τ) (f : MvPolynomial σ K) :
    Nat.card {z : τ → K // eval z (rename e f) = 0} =
      Nat.card {z : σ → K // eval z f = 0} := by
  apply Nat.card_congr
  exact {
    toFun := fun z => ⟨z.val ∘ e, by grind [eval_rename]⟩
    invFun := fun z => ⟨z.val ∘ e.symm, by grind [eval_rename, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]⟩
    left_inv := fun z => by aesop
    right_inv := fun z => by aesop }

