/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Plane.IntegralAffineLine
public import CCDN.Surface.CurveComponents
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Plane.DegreeOneAffineLine
import CCDN.Surface.CompleteIntersectionDegreeBudget
import CCDN.Surface.DirectionalDerivative
import CCDN.Surface.TopFormBadPrimes

/-! Lines in a fixed direction are components of the section by the
corresponding directional derivative. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A surface with absolutely irreducible top form has at most `d(d-1)` distinct
degree-one components with a given nonzero direction. -/
theorem surface_parallel_lines_card_le
    (f : MvPolynomial (Fin 3) ℤ) (hir : HasAbsIrreducibleTopForm f) (hd : 2 ≤ f.totalDegree)
    (v : RatPoint 3) (hv : v ≠ 0) (S : Finset (Ideal (CoordinatePolynomial 3)))
    (hlines : ∀ P ∈ S, ∃ a, idealZeroLocus P = rationalAffineLine a v)
    (hcurves : ∀ P ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) P 1) :
    S.card ≤ f.totalDegree * (f.totalDegree - 1) := by
  classical
  let F := map (Int.castRingHom ℚ) f
  let g := directionalDerivative v F
  have hf : Irreducible F := rational_irreducible_of_charZero_map f
    (absolute_irreducible_of_top_homogeneousComponent_irreducible f hir)
  have hg : g ≠ 0 := surface_directionalDerivative_ne_zero f hir hd v hv
  have hgdeg : g.totalDegree ≤ f.totalDegree - 1 := by
    simpa [F, g, rational_map_totalDegree] using directionalDerivative_totalDegree_le v F
  have hfg : ¬ F ∣ g := by
    intro hdvd
    have hh := totalDegree_le_of_dvd_of_isDomain hdvd hg
    rw [show F.totalDegree = f.totalDegree from rational_map_totalDegree _] at hh
    omega
  have hPg (P) (hP : P ∈ S) : IsSurfaceCurve F P 1 ∧ g ∈ P := by
    have hC := hcurves P hP
    let := hC.isPrime
    obtain ⟨a, ha⟩ := hlines P hP
    refine ⟨hC, (degree_one_zeroLocus_eq_rationalAffineLine P hC.degree).2 _ ?_⟩
    rw [ha]
    apply rationalAffineLine_contained_directionalDerivative
    rw [← ha]
    exact fun _ hx => hx _ hC.mem
  have hb := surface_prime_curve_degree_sum_le F g hf hfg S (fun _ => 1) hPg
  simpa using hb.trans (Nat.mul_le_mul (rational_map_totalDegree f).le hgdeg)

end
end CCDN
