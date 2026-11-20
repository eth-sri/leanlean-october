/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredPrimeDecomposition
public import CCDN.Surface.CurveComponents
import CCDN.ForMathlib.KrullHeight
import CCDN.Plane.Bezout
import CCDN.Surface.CompleteIntersectionDegreeBudget
import CCDN.Surface.NonlinearCount

/-! Degree and proper-section budgets for any finite family of distinct
prime curves on a surface section. A curve constructed by another
auxiliary is counted as a component of the section whenever its ideal
contains the section's equation. -/

@[expose] public section
namespace CCDN
noncomputable section

open Classical in
/-- For curves `P ∈ S` on the irreducible surface `f = 0` whose ideals contain `g` (with `f`
not dividing `g`), the integral points of height at most `B` on `h = 0` lying on those curves
whose ideals do not contain `h` number at most `deg f * deg g * deg h`. -/
theorem surface_curve_crossing_count_le
    (f g h : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ P ∈ S, IsSurfaceCurve f P (δ P)) (B : ℝ) :
    count (⋃ P ∈ S.filter (fun P => g ∈ P ∧ h ∉ P), idealZeroLocus P ∩ zeroLocus h) B ≤
      f.totalDegree * g.totalDegree * h.totalDegree := by
  classical
  let T := S.filter (fun P => g ∈ P ∧ h ∉ P)
  have hcurve (P) (hPT : P ∈ T) :
      count (idealZeroLocus P ∩ zeroLocus h) B ≤ δ P * h.totalDegree := by
    obtain ⟨hPS, hgP, hhP⟩ := Finset.mem_filter.mp hPT
    have : P.IsPrime := (hS P hPS).isPrime
    exact count_curve_section_le P (hS P hPS).degree h hhP B
  have hbudget := surface_prime_curve_degree_sum_le f g hf hfg T δ fun P hP => by
    grind
  calc
    _ ≤ _ := count_biUnion_finset_le T _ B
    _ ≤ ∑ P ∈ T, δ P * h.totalDegree := Finset.sum_le_sum hcurve
    _ = _ := Finset.sum_mul .. |>.symm
    _ ≤ _ := Nat.mul_le_mul_right _ hbudget

end
end CCDN
