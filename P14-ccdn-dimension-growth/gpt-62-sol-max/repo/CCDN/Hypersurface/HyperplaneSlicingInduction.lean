/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hypersurface.IntegerHyperplaneSlices
public import CCDN.Statements
import CCDN.Hypersurface.GoodHyperplane
import CCDN.Hypersurface.HyperplaneSliceCoordinates
import CCDN.Algebra.OriginShift
import CCDN.ForMathlib.MvPolynomial

/-! A dimension induction with a cubic degree cost per integral graph section. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Restrict to the graph `x_none = ∑ a i * x (some i) + k`. -/
private def integralGraphSlice {σ : Type*} [Fintype σ]
    (a : σ → ℤ) (k : ℤ) (f : MvPolynomial (Option σ) ℤ) : MvPolynomial σ ℤ :=
  graphHyperplaneRestriction a (originShift (fun i => i.elim k fun _ => 0) f)

private lemma integralGraphSlice_vanishes {σ : Type*} [Fintype σ] (a : σ → ℤ) (k : ℤ)
    (f : MvPolynomial (Option σ) ℤ) (x : Option σ → ℤ)
    (hlevel : x none - ∑ i, a i * x (some i) = k) (hz : eval x f = 0) :
    eval (fun i => x (some i)) (integralGraphSlice a k f) = 0 := by
  rw [integralGraphSlice, graphHyperplaneRestriction_eval, eval_originShift]
  refine Eq.trans ?_ hz
  apply congrArg (fun y => eval y f)
  funext i
  cases i with
  | none => simpa [add_comm] using (sub_eq_iff_eq_add.mp hlevel).symm
  | some i => simp

private lemma integralGraphSlice_degree_top {σ : Type*} [Fintype σ]
    (a : σ → ℤ) (f : MvPolynomial (Option σ) ℤ) (k : ℤ)
    (hg : AbsolutelyIrreducible (graphHyperplaneRestriction a (homogeneousComponent f.totalDegree f))) :
    (integralGraphSlice a k f).totalDegree = f.totalDegree ∧
      HasAbsIrreducibleTopForm (integralGraphSlice a k f) := by
  have he : homogeneousComponent f.totalDegree (integralGraphSlice a k f) =
      graphHyperplaneRestriction a (homogeneousComponent f.totalDegree f) := by
    rw [integralGraphSlice, ← graphHyperplaneRestriction_homogeneousComponent,
      homogeneousComponent_originShift_of_le _ _ _ le_rfl]
  have hd : (integralGraphSlice a k f).totalDegree = f.totalDegree := by
    refine le_antisymm ((graphHyperplaneRestriction_totalDegree_le a _).trans (originShift_totalDegree_le _ _)) (le_of_not_gt fun h => hg.ne_zero ?_)
    rw [← he, homogeneousComponent_eq_zero _ _ h, map_zero]
  refine ⟨hd, ?_⟩
  rwa [HasAbsIrreducibleTopForm, hd, he]

private theorem count_le_of_cubic_slices {n d e r : ℕ}
    (X : Set (RatPoint (n + 1))) (a : IntPoint (n + 1))
    (j : Fin (n + 1)) (hj : a j ≠ 0) (Y : ℤ → Set (RatPoint n))
    (hd : 1 ≤ d) {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (ha : InBox a (2 * (d : ℝ) ^ 3))
    (hmap : ∀ k x, x ∈ integerSlicePoints X B a k →
      rationalPoint (deleteIntegerCoordinate j x) ∈ Y k)
    (hcount : ∀ k, (count (Y k) B : ℝ) ≤ C * (d : ℝ) ^ e * B ^ r) :
    (count X B : ℝ) ≤
      (4 * (n + 1 : ℕ) + 1) * C * (d : ℝ) ^ (e + 3) * B ^ (r + 1) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : 0 ≤ C * (d : ℝ) ^ e * B ^ r := by positivity
  have hDB : 1 ≤ (d : ℝ) ^ 3 * B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hdR) hB
  calc
    _ ≤ (2 * (n + 1 : ℕ) * (2 * (d : ℝ) ^ 3) * B + 1) * _ :=
      count_le_of_integer_hyperplane_slices X a j hj Y
        (by positivity) (by positivity) hK ha hmap hcount
    _ ≤ ((4 * (n + 1 : ℕ) + 1) * (d : ℝ) ^ 3 * B) * _ :=
      mul_le_mul_of_nonneg_right (by nlinarith) hK
    _ = _ := by ring

/-- A cubic bound for the slicing normal costs three powers of the degree and one of the box. -/
private theorem AffineHypersurfaceGrowth.succ {n e : ℕ} (h : AffineHypersurfaceGrowth n e) :
    AffineHypersurfaceGrowth (n + 1) (e + 3) := by
  obtain ⟨C, hC, hbound⟩ := h
  rw [show n + 3 = 3 + n by omega] at hbound
  unfold AffineHypersurfaceGrowth
  rw [show n + 1 + 3 = 3 + n + 1 by omega]
  refine ⟨(4 * (3 + n + 1 : ℕ) + 1) * C, by positivity, ?_⟩
  intro f hir hd B hB
  let E : Fin (3 + n + 1) ≃ Option (Fin (3 + n)) := finSuccEquiv' 0
  let F := rename E f
  have hFdegree : F.totalDegree = f.totalDegree := totalDegree_renameEquiv E f
  have hFir := integer_top_irreducible_rename E f hir
  let t := homogeneousComponent F.totalDegree F
  have htd : t.totalDegree = f.totalDegree :=
    ((homogeneousComponent_isHomogeneous _ _).totalDegree
      (homogeneousComponent_totalDegree_ne_zero (by intro hz; rw [hz, totalDegree_zero] at hFdegree; omega))).trans hFdegree
  obtain ⟨a, ha, hgood⟩ := exists_good_integer_graph t hFir (by omega)
  let g (k : ℤ) := integralGraphSlice a k F
  have hb (i : Fin (3 + n + 1)) : |(graphIntegerNormal 1 a i : ℝ)| ≤ 2 * (f.totalDegree : ℝ) ^ 3 := by
    rw [← htd]
    have he : |(1 : ℤ)| ≤ (2 * t.totalDegree ^ 3 : ℕ) := by
      have hh : 1 ≤ t.totalDegree ^ 3 := one_le_pow₀ (by omega)
      exact_mod_cast (show 1 ≤ 2 * t.totalDegree ^ 3 by omega)
    simpa using graphIntegerNormal_height 1 a he ha i
  refine count_le_of_cubic_slices (zeroLocus (map (Int.castRingHom ℚ) f)) (graphIntegerNormal 1 a)
    0 (by simp [graphIntegerNormal]) (fun k => zeroLocus (map (Int.castRingHom ℚ) (g k)))
    (by omega) hB hC.le hb ?_ ?_
  · intro k x hx
    exact integer_slice_map_of_option_equations f 1 a g
      (fun l z hlevel hz => integralGraphSlice_vanishes a l F z (by simpa using hlevel) hz) B k x hx
  · intro k
    obtain ⟨hk, hi⟩ := integralGraphSlice_degree_top a F k hgood
    simpa [g, hk, hFdegree] using hbound (g k) hi (by simpa [g, hk, hFdegree] using hd) B hB

/-- Bounded good hyperplanes lift a surface bound with degree exponent `e` to every
higher dimension; each slice adds three to the exponent. -/
theorem affineHypersurfaceGrowth_of_surface {e : ℕ} (h : AffineHypersurfaceGrowth 0 e) :
    ∀ n, AffineHypersurfaceGrowth n (e + 3 * n)
  | 0 => h
  | n + 1 => (affineHypersurfaceGrowth_of_surface h n).succ

end
end CCDN
