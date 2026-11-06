/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Plane.IntegralAffineLine
public import Mathlib.RingTheory.Ideal.Height
import CCDN.Plane.DegreeOneAffineLine
import CCDN.Surface.LineContribution

/-!
The proved line contribution applies to degree-one prime
components, with the original number of components as the additive cost.

A finite family of degree-one prime components gives a finite
set of rational affine lines with the same rational zero-set union. Empty
rational loci are discarded, and repeated line sets are counted only once.
-/

@[expose] public section
namespace CCDN
noncomputable section

open MvPolynomial

/-- There is an absolute constant `C` such that, for an integer surface equation `f` of degree
`d ≥ 3` with absolutely irreducible top-degree form, the integral points of height at most `B`
on a finite family `S` of degree-one curves on the surface number at most
`C d⁶ B + #S`. -/
theorem surface_degree_one_component_contribution :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      3 ≤ f.totalDegree → ∀ B : ℝ, 0 ≤ B →
      ∀ S : Finset (Ideal (CoordinatePolynomial 3)),
      (∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P 1) →
      (∀ P ∈ S, map (Int.castRingHom ℚ) f ∈ P) →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ 6 * B + S.card := by
  /- The union of the rational zero sets of finitely many degree-one affine curves in
  three-space is a union of at most as many rational affine lines, each of which is the zero set
  of one of the curves. -/
  classical
  obtain ⟨C, hC, hline⟩ := surface_line_contribution
  refine ⟨C, hC, fun f hir hd B hB S hcurve hSf => ?_⟩
  let T := S.filter (fun P => (idealZeroLocus P).Nonempty)
  let lines := T.image idealZeroLocus
  have hcover : (⋃ P ∈ S, idealZeroLocus P) = (⋃ L ∈ lines, L) := by
    ext x; constructor
    · intro hx
      obtain ⟨P, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨idealZeroLocus P,
        Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨P, Finset.mem_filter.mpr ⟨hPS, ⟨x, hxP⟩⟩, rfl⟩, hxP⟩⟩
    · intro hx
      obtain ⟨L, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hLs, hxL⟩ := Set.mem_iUnion.mp hx
      obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hLs
      exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hPT).1, hxL⟩⟩
  have hh := (hline f hir hd B hB lines
    (fun L hL => by
      obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hL
      obtain ⟨hPS, z, hz⟩ := Finset.mem_filter.mp hPT
      obtain ⟨hp, hheight, hdegree⟩ := hcurve P hPS
      have : P.IsPrime := hp
      obtain ⟨v, _, he, _⟩ := degree_one_zeroLocus_eq_rationalAffineLine P hheight hdegree z hz
      exact ⟨z, v, he⟩)
    (fun L hL x hx => by
      obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hL
      exact hx _ (hSf P (Finset.mem_filter.mp hPT).1))).2
  rw [← hcover] at hh
  exact hh.trans (add_le_add le_rfl
    (mod_cast Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))))

end
end CCDN
