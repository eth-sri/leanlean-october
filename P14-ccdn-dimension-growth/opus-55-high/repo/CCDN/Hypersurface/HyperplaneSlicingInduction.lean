/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hypersurface.IntegerHyperplaneSlices
import CCDN.Statements
import CCDN.Hypersurface.GoodHyperplane
import CCDN.Hypersurface.HyperplaneSliceCoordinates
import CCDN.Hypersurface.IntegerGoodHyperplaneSlices

/-!
A dimension induction with a cubic degree cost per hyperplane slice,
using the constructed universal Noether detector.

Integer equations for every parallel level of a good hyperplane whose
normal has cubic degree height.
-/

namespace CCDN
open MvPolynomial

/-- One bounded good hyperplane slice: affine dimension growth in `n + 3` variables
gives it in `n + 4` variables, at the cost of three powers of the degree and one power of
the box radius. -/
theorem AffineHypersurfaceGrowth.succ {n e : ℕ} (h : AffineHypersurfaceGrowth n e) :
    AffineHypersurfaceGrowth (n + 1) (e + 3) := by
  obtain ⟨C, hC, hbound⟩ := h
  rw [show n + 3 = 3 + n by omega] at hbound
  unfold AffineHypersurfaceGrowth
  rw [show n + 1 + 3 = 3 + n + 1 by omega]
  refine ⟨(2 * (3 + n + 1 : ℕ) + 1) * C, by positivity, ?_⟩
  intro f hir hd B hB
  let indexEquiv : Fin (3 + n + 1) ≃ Option (Fin (3 + n)) := finSuccEquiv' 0
  let F := rename indexEquiv f
  have hFdegree : F.totalDegree = f.totalDegree := totalDegree_renameEquiv indexEquiv f
  have hFir : HasAbsIrreducibleTopForm (rename indexEquiv f) := by
    dsimp [HasAbsIrreducibleTopForm, AbsolutelyIrreducible]
    rw [show (rename indexEquiv f).totalDegree = f.totalDegree from totalDegree_renameEquiv indexEquiv f,
      ← rename_homogeneousComponent, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv _ indexEquiv)).mpr hir
  obtain ⟨D, a, hD, hDb, hab, hgood⟩ := exists_geometrically_good_hyperplane
    (homogeneousComponent F.totalDegree F) F.totalDegree (by grind)
    (homogeneousComponent_isHomogeneous _ _) hFir
  obtain ⟨g, hg⟩ := exists_integer_hyperplane_slice_models F D a hD hgood
  rw [hFdegree] at hDb hab
  let b := graphIntegerNormal D a
  have hb0 := hD
  have hbheight (i : Fin (3 + n + 1)) :
      |(b i : ℝ)| ≤ f.totalDegree ^ 3 := by
    simpa using graphIntegerNormal_height D a hDb hab i
  let Y : ℤ → Set (RatPoint (3 + n)) :=
    fun k => zeroLocus (map (Int.castRingHom ℚ) (g k))
  have hmap (k : ℤ) (x : IntPoint (3 + n + 1))
      (hx : x ∈ integerSlicePoints (zeroLocus (map (Int.castRingHom ℚ) f)) B b k) :
      rationalPoint (deleteIntegerCoordinate 0 x) ∈ Y k :=
    integer_slice_map_of_option_equations f D a g (fun k => (hg k).2.2) B k x hx
  have hcount (k : ℤ) :
      (count (Y k) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1) := by
    have hdegree := (hg k).1.trans hFdegree
    simpa [hdegree, Y] using hbound (g k) (hg k).2.1 (by omega) B hB
  let X := zeroLocus (map (Int.castRingHom ℚ) f)
  have hd0 : (0 : ℝ) ≤ f.totalDegree := Nat.cast_nonneg _
  have hB0 : 0 ≤ B := by linarith
  have hK : 0 ≤ C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1) := by positivity
  have hD : 1 ≤ (f.totalDegree : ℝ) ^ 3 := one_le_pow₀ (by bound)
  have hDB := one_le_mul_of_one_le_of_one_le hD hB
  have hfactor :
      2 * (3 + n + 1 : ℕ) * (f.totalDegree ^ 3) * B + 1 ≤
        (2 * (3 + n + 1 : ℕ) + 1) * (f.totalDegree : ℝ) ^ 3 * B := by
    nlinarith
  rw [(show count X B = ∑ k ∈ integerSliceLevels X B b, (integerSlicePoints X B b k).card by
      exact Finset.card_eq_sum_card_image (integerLinearLevel b) (integralPoints X B)), Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ integerSliceLevels X B b, C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1) := by
      apply Finset.sum_le_sum
      intro k _
      have hh : ((integerSlicePoints X B b k).card : ℝ) ≤ (count (Y k) B : ℝ) := by
        exact_mod_cast integerSlicePoints_card_le_count X (Y k) B b 0 hb0 k (hmap k)
      grind
    _ = ((integerSliceLevels X B b).card : ℝ) * (C * f.totalDegree ^ e * B ^ (n + 1)) := by simp
    _ ≤ (2 * (3 + n + 1 : ℕ) * (f.totalDegree ^ 3) * B + 1) * (C * f.totalDegree ^ e * B ^ (n + 1)) :=
      mul_le_mul_of_nonneg_right (integerSliceLevels_card_le X b (by positivity) hB0 hbheight) hK
    _ ≤ ((2 * (3 + n + 1 : ℕ) + 1) * f.totalDegree ^ 3 * B) *
        (C * (f.totalDegree : ℝ) ^ e * B ^ (n + 1)) := mul_le_mul_of_nonneg_right hfactor hK
    _ = _ := by grind

/-- Bounded good hyperplanes lift a surface bound with degree exponent `e` to every
higher dimension; each slice adds three to the exponent. -/
theorem affineHypersurfaceGrowth_of_surface {e : ℕ} (h : AffineHypersurfaceGrowth 0 e) :
    ∀ n, AffineHypersurfaceGrowth n (e + 3 * n)
  | 0 => h
  | n + 1 => (affineHypersurfaceGrowth_of_surface h n).succ

