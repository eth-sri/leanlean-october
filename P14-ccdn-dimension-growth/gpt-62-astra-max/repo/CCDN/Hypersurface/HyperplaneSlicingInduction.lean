/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Hypersurface.IntegerHyperplaneSlices
public import CCDN.Statements
import CCDN.Hypersurface.GoodHyperplane
import CCDN.Hypersurface.HyperplaneSliceCoordinates
import CCDN.Hypersurface.AffineHyperplaneSlice

/-!
A dimension induction with a cubic degree cost per hyperplane slice,
using the universal plane witness.

Integer equations for every parallel level of a good hyperplane whose
normal has cubic degree height.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {n d e : ℕ}

private theorem exists_good_integer_hyperplane_slices
    (f : MvPolynomial (Option (Fin (3 + n))) ℤ)
    (hir : HasAbsIrreducibleTopForm f) (hd : 2 ≤ f.totalDegree) :
    ∃ (a : Fin (3 + n) → ℤ) (g : ℤ → IntegerPolynomial (3 + n)),
      (∀ i, |a i| ≤ (f.totalDegree ^ 3 : ℕ)) ∧
      ∀ k : ℤ, (g k).totalDegree = f.totalDegree ∧ HasAbsIrreducibleTopForm (g k) ∧
        ∀ x : Option (Fin (3 + n)) → ℤ,
          x none - ∑ i, a i * x (some i) = k →
          eval x f = 0 → eval (fun i => x (some i)) (g k) = 0 := by
  let F := homogeneousComponent f.totalDegree f
  have hdeg := (homogeneousComponent_isHomogeneous f.totalDegree f).totalDegree (fun h => hir.ne_zero (by aesop))
  obtain ⟨a, ha, habs⟩ := exists_geometrically_good_hyperplane F (by grind) hir
  refine ⟨a, fun k => affineGraphHyperplaneSlice a k f, hdeg ▸ ha, fun k => ?_⟩
  have hg := affineGraphHyperplaneSlice_degree a k f (fun h => habs.ne_zero (by rw [h, map_zero]))
  refine ⟨hg, ?_, fun x hx hxf => ?_⟩
  · rwa [HasAbsIrreducibleTopForm, hg, affineGraphHyperplaneSlice_top]
  · rw [affineGraphHyperplaneSlice_eval, show (∑ i, a i * x (some i)) + k = x none by omega]
    convert hxf using 3
    funext i
    cases i <;> rfl

/-- A normal of height at most `d^3` costs three powers of the degree
and one power of the box radius in a dimension induction. -/
private theorem count_le_of_good_integer_hyperplane_slices {r : ℕ}
    (X : Set (RatPoint (n + 1))) (a : IntPoint (n + 1))
    (j : Fin (n + 1)) (hj : a j ≠ 0) (Y : ℤ → Set (RatPoint n))
    (hd : 1 ≤ d) {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (ha : InBox a ((d : ℝ) ^ 3))
    (hmap : ∀ k x, x ∈ integerSlicePoints X B a k →
      rationalPoint (deleteIntegerCoordinate j x) ∈ Y k)
    (hcount : ∀ k, (count (Y k) B : ℝ) ≤ C * (d : ℝ) ^ e * B ^ r) :
    (count X B : ℝ) ≤
      (2 * (n + 1 : ℕ) + 1) * C * (d : ℝ) ^ (e + 3) * B ^ (r + 1) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hB0 : 0 ≤ B := by linarith
  have hK : 0 ≤ C * (d : ℝ) ^ e * B ^ r := by positivity
  have hD : 1 ≤ (d : ℝ) ^ 3 := one_le_pow₀ hdR
  have hfactor :
      2 * (n + 1 : ℕ) * ((d : ℝ) ^ 3) * B + 1 ≤
        (2 * (n + 1 : ℕ) + 1) * (d : ℝ) ^ 3 * B := by
    nlinarith
  calc
    _ ≤ (2 * (n + 1 : ℕ) * (d ^ 3) * B + 1) *
        (C * d ^ e * B ^ r) :=
      count_le_of_integer_hyperplane_slices X a j hj Y
        (by positivity) hB0 hK ha hmap hcount
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hK
    _ = _ := by ring

/-- One bounded good hyperplane slice: affine dimension growth in `n + 3` variables
gives it in `n + 4` variables, at the cost of three powers of the degree and one power of
the box radius. -/
private theorem AffineHypersurfaceGrowth.succ (h : AffineHypersurfaceGrowth n e) :
    AffineHypersurfaceGrowth (n + 1) (e + 3) := by
  classical
  obtain ⟨C, hC, hbound⟩ := h
  rw [show n + 3 = 3 + n by omega] at hbound
  unfold AffineHypersurfaceGrowth
  rw [show n + 1 + 3 = 3 + n + 1 by omega]
  refine ⟨(2 * (3 + n + 1 : ℕ) + 1) * C, by positivity, ?_⟩
  intro f hir hd B hB
  let indexEquiv : Fin (3 + n + 1) ≃ Option (Fin (3 + n)) := finSuccEquiv' 0
  let F := rename indexEquiv f
  have hFdegree : F.totalDegree = f.totalDegree := totalDegree_renameEquiv indexEquiv f
  obtain ⟨a, g, hab, hg⟩ :=
    exists_good_integer_hyperplane_slices F (integer_top_irreducible_rename indexEquiv f hir) (by rw [hFdegree]; omega)
  rw [hFdegree] at hab
  let b := graphIntegerNormal 1 a
  have hbheight (i : Fin (3 + n + 1))  := by
    simpa using graphIntegerNormal_height 1 a (by simp; exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ f.totalDegree by omega))) hab i
  have hmap (k : ℤ) (x : IntPoint (3 + n + 1))
      (hx : x ∈ integerSlicePoints (zeroLocus (rationalEquation f)) B b k)  :=
    integer_slice_map_of_option_equations f 1 a g (by simpa using fun k => (hg k).2.2) B k x hx
  have hcount (k : ℤ)  := by
    have hdegree := (hg k).1.trans hFdegree
    simpa [*] using hbound (g k) (hg k).2.1 (by omega) B hB
  exact count_le_of_good_integer_hyperplane_slices
    (zeroLocus (rationalEquation f)) b 0 one_ne_zero (fun k => zeroLocus (rationalEquation (g k)))
    (show 1 ≤ f.totalDegree by omega) hB hC.le hbheight hmap hcount

/-- Bounded good hyperplanes lift a surface bound with degree exponent `e` to every
higher dimension; each slice adds three to the exponent. -/
theorem affineHypersurfaceGrowth_of_surface (h : AffineHypersurfaceGrowth 0 e) :
    ∀ n, AffineHypersurfaceGrowth n (e + 3 * n)
  | 0 => h
  | n + 1 => (affineHypersurfaceGrowth_of_surface h n).succ

end
end CCDN
