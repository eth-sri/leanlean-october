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
import CCDN.Hypersurface.IntegerGoodHyperplaneSlices

/-!
A dimension induction with a cubic degree cost per hyperplane slice,
using the constructed universal Noether detector.

Integer equations for every parallel level of a good hyperplane whose
normal has cubic degree height.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Bounded good hyperplanes lift a surface bound with degree exponent `e` to every
higher dimension; each slice adds three to the exponent. -/
theorem affineHypersurfaceGrowth_of_surface {e : ℕ} (h : AffineHypersurfaceGrowth 0 e) :
    ∀ n, AffineHypersurfaceGrowth n (e + 3 * n)
  | 0 => h
  | n + 1 => by
    /- One bounded good hyperplane slice: affine dimension growth in `n + 3` variables
    gives it in `n + 4` variables, at the cost of three powers of the degree and one power of
    the box radius. -/
    classical
    obtain ⟨C, hC, hbound⟩ := affineHypersurfaceGrowth_of_surface h n
    rw [show n + 3 = 3 + n by omega] at hbound
    unfold AffineHypersurfaceGrowth
    rw [show n + 1 + 3 = 3 + n + 1 by omega, show e + 3 * (n + 1) = e + 3 * n + 3 by omega]
    refine ⟨(2 * (3 + n + 1 : ℕ) + 1) * C, by positivity, fun f hir hd B hB => ?_⟩
    let indexEquiv : Fin (3 + n + 1) ≃ Option (Fin (3 + n)) := finSuccEquiv' 0
    let F := rename indexEquiv f
    have hFdegree : F.totalDegree = f.totalDegree := totalDegree_renameEquiv indexEquiv f
    have hFir : HasAbsIrreducibleTopForm F := integer_top_irreducible_rename indexEquiv f hir
    obtain ⟨D, a, hD, hDb, hab, _, hgood⟩ := exists_geometrically_good_hyperplane
      (homogeneousComponent F.totalDegree F) F.totalDegree (by rw [hFdegree]; omega)
      (homogeneousComponent_isHomogeneous _ _) hFir
    obtain ⟨g, hg⟩ := exists_integer_hyperplane_slice_models F D a hD hgood
    rw [hFdegree] at hDb hab
    let b := graphIntegerNormal D a
    have hbheight (i : Fin (3 + n + 1)) : |(b i : ℝ)| ≤ (f.totalDegree : ℝ) ^ 3 := by
      simpa only [Nat.cast_pow] using graphIntegerNormal_height D a hDb hab i
    let Y : ℤ → Set (RatPoint (3 + n)) := fun k => zeroLocus (map (Int.castRingHom ℚ) (g k))
    have hmap (k : ℤ) (x : IntPoint (3 + n + 1))
        (hx : x ∈ integerSlicePoints (zeroLocus (map (Int.castRingHom ℚ) f)) B b k) :
        rationalPoint (deleteIntegerCoordinate 0 x) ∈ Y k :=
      integer_slice_map_of_option_equations f D a g (fun k => (hg k).2.2) B k x hx
    have hcount (k : ℤ) : (count (Y k) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ (e + 3 * n) * B ^ (n + 1) := by
      have hdegree : (g k).totalDegree = f.totalDegree := (hg k).1.trans hFdegree
      simpa only [hdegree, Y] using hbound (g k) (hg k).2.1 (by omega) B hB
    let d := f.totalDegree
    have hdR : (1 : ℝ) ≤ d := mod_cast (show 1 ≤ d by omega)
    have hK : 0 ≤ C * (d : ℝ) ^ (e + 3 * n) * B ^ (n + 1) := by positivity
    have hDB : 1 ≤ (d : ℝ) ^ 3 * B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hdR) hB
    have hfactor : 2 * (3 + n + 1 : ℕ) * ((d : ℝ) ^ 3) * B + 1 ≤
        (2 * (3 + n + 1 : ℕ) + 1) * (d : ℝ) ^ 3 * B := by nlinarith
    exact (count_le_of_integer_hyperplane_slices (zeroLocus (map (Int.castRingHom ℚ) f))
      b 0 hD Y (by positivity) (by linarith) hK hbheight hmap hcount).trans
      ((mul_le_mul_of_nonneg_right hfactor hK).trans_eq (by rw [pow_add, pow_succ]; ring))

end
end CCDN
