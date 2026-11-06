/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A geometrically irreducible affine hypersurface `f = 0` in `n + 3` variables over `ZMod p`,
with `p` above the threshold `27 * (deg f) ^ 4`, has at most
`p ^ (n + 2) + hypersurfaceResidueConstant * (deg f) ^ 2 * p ^ (n + 1) * √p` points. -/
theorem affine_hypersurface_finite_field_bound {n : ℕ}
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) (ZMod p))
    (hf : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) f))
    (hsize : stepanovThreshold (f.totalDegree : ℝ) < p) :
    (Nat.card {z : Fin (n + 3) → ZMod p // eval z f = 0} : ℝ) ≤
      (p : ℝ) ^ (n + 2) + hypersurfaceResidueConstant * (f.totalDegree : ℝ) ^ 2 *
        (p : ℝ) ^ (n + 1) * Real.sqrt p := by
  let e : Fin (n + 3) ≃ Option (Fin (n + 2)) := finSuccEquiv' 0
  let g := rename e f
  have hg : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) g) := by
    rw [show g = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv (AlgebraicClosure (ZMod p)) e)).mpr hf
  have hgd : g.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  have hcard : Nat.card {z : Fin (n + 3) → ZMod p // eval z f = 0} =
      Nat.card {z : Option (Fin (n + 2)) → ZMod p // eval z g = 0} :=
    Nat.card_congr {
      toFun := fun z => ⟨z.val ∘ e.symm, by
        simpa only [g, eval_rename, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
          using z.property⟩
      invFun := fun z => ⟨z.val ∘ e, by simpa only [g, eval_rename] using z.property⟩
      left_inv := fun z => Subtype.ext (funext fun _ => by simp)
      right_inv := fun z => Subtype.ext (funext fun _ => by simp) }
  rw [hcard, ← hgd]
  replace hsize : stepanovThreshold (g.totalDegree : ℝ) < p := hgd ▸ hsize
  have hir :=
    mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) g hg
  have hd : 0 < g.totalDegree :=
    totalDegree_pos_of_ne_zero_of_not_isUnit hir.ne_zero hir.not_isUnit
  have hdR : (1 : ℝ) ≤ g.totalDegree := mod_cast hd
  have hpN : 27 * g.totalDegree ^ 4 < p := mod_cast hsize
  have hchar : 2 * g.totalDegree ^ 2 < p := by
    have h2 : 1 ≤ g.totalDegree ^ 2 := by nlinarith
    nlinarith [show g.totalDegree ^ 2 ≤ g.totalDegree ^ 4 by nlinarith]
  have hbN := finite_field_bad_plane_parameters_card g hg hd hchar
  have hzN := finite_field_zero_plane_parameters_card g hir.ne_zero
  simp only [Fintype.card_fin, ZMod.card] at hbN hzN
  rw [show 3 * (n + 2 + 1) - 1 = 3 * n + 8 by omega] at hbN
  rw [show 3 * (n + 2) = 3 * n + 6 by omega] at hzN
  have hb : (Nat.card (BadPlaneParameters g) : ℝ) ≤
      2 * (g.totalDegree : ℝ) ^ 3 * (p : ℝ) ^ (3 * n + 8) := mod_cast hbN
  have hz : (Nat.card (ZeroPlaneParameters g) : ℝ) ≤
      (g.totalDegree : ℝ) ^ 3 * (p : ℝ) ^ (3 * n + 6) := mod_cast hzN
  let d : ℝ := g.totalDegree
  have hi := plane_sections_incidence_bound p g hsize
  simp only [Fintype.card_option, Fintype.card_fin] at hi
  rw [show 2 * (n + 2 + 1) + 2 = 2 * n + 8 by omega,
    show 3 * (n + 2 + 1) = 3 * n + 9 by omega] at hi
  have hcount : (Nat.card {z : Option (Fin (n + 2)) → ZMod p // eval z g = 0} : ℝ) *
      (p : ℝ) ^ (2 * n + 8) ≤
      (p : ℝ) ^ (3 * n + 9) * (p + planeResidueConstant * d ^ 2 * Real.sqrt p) +
      2 * d ^ 4 * (p : ℝ) ^ (3 * n + 9) + d ^ 3 * (p : ℝ) ^ (3 * n + 8) :=
    (hi.trans (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ d * p)))
      (mul_le_mul_of_nonneg_right hz (by positivity : 0 ≤ (p : ℝ) ^ 2)))).trans_eq (by
        rw [show 3 * n + 9 = (3 * n + 8) + 1 by omega, pow_succ,
          show 3 * n + 8 = (3 * n + 6) + 2 by omega, pow_add]; ring)
  rw [planeResidueConstant_eq] at hcount
  rw [hypersurfaceResidueConstant_eq]
  change stepanovThreshold d < p at hsize
  unfold stepanovThreshold at hsize
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hd4 : 1 ≤ d ^ 4 := by nlinarith [sq_nonneg (d ^ 2 - 1)]
  have hp1 : 1 ≤ (p : ℝ) := by nlinarith
  have hp0 : 0 < (p : ℝ) := by linarith
  have hs : d ^ 2 ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (d ^ 2)])
  have herr : 2 * d ^ 4 * p + d ^ 3 ≤ 3 * d ^ 2 * p * Real.sqrt p := by
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * d ^ 2 * p by positivity),
      mul_le_mul_of_nonneg_left (show d ≤ Real.sqrt p by nlinarith) (sq_nonneg d),
      mul_le_mul_of_nonneg_right hp1 (show 0 ≤ d ^ 2 * Real.sqrt p by positivity)]
  have hmajor := mul_le_mul_of_nonneg_left herr (pow_nonneg hp0.le (3 * n + 8))
  have hfact :
      (p : ℝ) ^ (3 * n + 9) * (p + 161 * d ^ 2 * Real.sqrt p) +
      2 * d ^ 4 * (p : ℝ) ^ (3 * n + 9) + d ^ 3 * (p : ℝ) ^ (3 * n + 8) ≤
      ((p : ℝ) ^ (n + 2) + 164 * d ^ 2 * (p : ℝ) ^ (n + 1) * Real.sqrt p) * (p : ℝ) ^ (2 * n + 8) := by
    calc
      _ ≤ (p : ℝ) ^ (3 * n + 8) * ((p : ℝ) ^ 2 + 164 * d ^ 2 * p * Real.sqrt p) := by
        rw [show 3 * n + 9 = (3 * n + 8) + 1 by omega, pow_succ]; nlinarith
      _ = _ := by
        rw [show 3 * n + 8 = (2 * n + 8) + n by omega, pow_add]
        simp only [pow_add, pow_one]; ring
  exact (mul_le_mul_iff_left₀ (pow_pos hp0 _)).mp (hcount.trans hfact)

end
end CCDN
