/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Plane.FiniteFieldConstants
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.SectionSum

/-!
A sharp coefficient-uniform count for geometrically irreducible affine
hypersurfaces over prime fields, proved by plane-section averaging.

Numerical absorption of bad and zero plane sections above the cutoff
p>27*d^4. The leading term remains exactly p^(m-1).
-/

public section
namespace CCDN

/-- For `1 ≤ d` and `p` above the threshold `27 * d ^ 4`, the bad-section error
`2 * d ^ 4 * p + d ^ 3` is at most `3 * d ^ 2 * p * √p`. -/
lemma hypersurface_bad_section_error {d p : ℝ} (hd : 1 ≤ d) (hp : stepanovThreshold d < p) :
    2 * d ^ 4 * p + d ^ 3 ≤ 3 * d ^ 2 * p * Real.sqrt p := by
  unfold stepanovThreshold at hp
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hp1 : 1 ≤ p := by nlinarith
  have hs : d ^ 2 ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (d ^ 2)])
  have hds : d ≤ Real.sqrt p := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * d ^ 2 * p by positivity)
  have h3 := mul_le_mul_of_nonneg_right hp1 (show 0 ≤ d ^ 2 * Real.sqrt p by positivity)
  nlinarith

/-- The unsimplified incidence estimate implies the desired sharp affine
hypersurface estimate in every ambient dimension at least three. -/
private theorem hypersurface_count_of_incidence_bound (n : ℕ) {d p N : ℝ}
    (hd : 1 ≤ d) (hp : stepanovThreshold d < p)
    (hcount : N * p ^ (2 * n + 8) ≤
      p ^ (3 * n + 9) * (p + planeResidueConstant * d ^ 2 * Real.sqrt p) +
      2 * d ^ 4 * p ^ (3 * n + 9) + d ^ 3 * p ^ (3 * n + 8)) :
    N ≤ p ^ (n + 2) + hypersurfaceResidueConstant * d ^ 2 * p ^ (n + 1) * Real.sqrt p := by
  have herr := hypersurface_bad_section_error hd hp
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
    ring
  rw [he] at hfact
  exact (mul_le_mul_iff_left₀ (pow_pos hp0 _)).mp (hcount.trans hfact)

end CCDN

namespace CCDN
open MvPolynomial

variable {n : ℕ} (p : ℕ) [Fact p.Prime]


/-- Renaming coordinates preserves the number of affine zeros. -/
private lemma polynomial_zero_card_renameEquiv {K σ τ : Type*} [CommRing K]
    (e : σ ≃ τ) (f : MvPolynomial σ K) :
    Nat.card {z : τ → K // eval z (rename e f) = 0} =
      Nat.card {z : σ → K // eval z f = 0} := by
  apply Nat.card_congr
  exact {
    toFun := fun z => ⟨z.val ∘ e, by grind [eval_rename]⟩
    invFun := fun z => ⟨z.val ∘ e.symm, by
      grind [eval_rename, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]⟩
    left_inv := fun z => by aesop
    right_inv := fun z => by aesop }

/-- A geometrically irreducible affine hypersurface `f = 0` in `n + 3` variables over `ZMod p`,
with `p` above the threshold `27 * (deg f) ^ 4`, has at most
`p ^ (n + 2) + hypersurfaceResidueConstant * (deg f) ^ 2 * p ^ (n + 1) * √p` points. -/
theorem affine_hypersurface_finite_field_bound  (f : MvPolynomial (Fin (n + 3)) (ZMod p))
    (hf : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) f))
    (hsize : stepanovThreshold (f.totalDegree : ℝ) < p) :
    (Nat.card {z : Fin (n + 3) → ZMod p // eval z f = 0} : ℝ) ≤
      ↑p ^ (n + 2) + hypersurfaceResidueConstant * ↑f.totalDegree ^ 2 *
        ↑p ^ (n + 1) * Real.sqrt p := by
  let e : Fin (n + 3) ≃ Option (Fin (n + 2)) := finSuccEquiv' 0
  let g := rename e f
  have hg : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) g) := by
    rw [show g = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv (AlgebraicClosure (ZMod p)) e)).mpr hf
  have hd : g.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  have h := (by
              let inline_hsize := Eq.symm hd ▸ hsize
              have hir :=
                mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) g hg
              have hd :=
                totalDegree_pos_of_ne_zero_of_not_isUnit hir.ne_zero hir.not_isUnit
              have hdR : (1 : ℝ) ≤ g.totalDegree := by exact_mod_cast hd
              have hpN : 27 * g.totalDegree ^ 4 < p := by exact_mod_cast inline_hsize
              have hchar : 2 * g.totalDegree ^ 2 < p := by
                have h2 : 1 ≤ g.totalDegree ^ 2 := by nlinarith
                nlinarith
              have hbN := finite_field_bad_plane_parameters_card g hg hd hchar
              have hzN := finite_field_zero_plane_parameters_card g hir.ne_zero
              simp only [Fintype.card_fin, ZMod.card] at hbN hzN
              have hb : (Nat.card (BadPlaneParameters g) : ℝ) ≤
                  2 * ↑g.totalDegree ^ 3 * ↑p ^ (3 * n + 8) := by exact_mod_cast hbN
              have hz : (Nat.card (ZeroPlaneParameters g) : ℝ) ≤
                  ↑g.totalDegree ^ 3 * ↑p ^ (3 * n + 6) := by exact_mod_cast hzN
              have hi := plane_sections_incidence_bound p g inline_hsize
              simp only [Fintype.card_option, Fintype.card_fin] at hi
              apply hypersurface_count_of_incidence_bound n hdR inline_hsize
              calc
                _ ≤ ↑p ^ (3 * n + 9) *
                      (p + planeResidueConstant * ↑g.totalDegree ^ 2 * Real.sqrt p) +
                    (2 * ↑g.totalDegree ^ 3 * ↑p ^ (3 * n + 8)) * (g.totalDegree * p) +
                    (↑g.totalDegree ^ 3 * ↑p ^ (3 * n + 6)) * ↑p ^ 2 := by
                  exact hi.trans (add_le_add
                    (add_le_add le_rfl
                      (mul_le_mul_of_nonneg_right hb (show 0 ≤ (g.totalDegree : ℝ) * p by positivity)))
                    (mul_le_mul_of_nonneg_right hz (show 0 ≤ (p : ℝ) ^ 2 by positivity)))
                _ = _ := by
                  ring)
  rw [hd, polynomial_zero_card_renameEquiv] at h
  exact h

end CCDN
