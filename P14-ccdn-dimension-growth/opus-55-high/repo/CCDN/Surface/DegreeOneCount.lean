/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Algebra.PolynomialPredicates
import CCDN.Hilbert.AffineCurveDegree
import CCDN.Plane.IntegralAffineLine
import Mathlib.RingTheory.Ideal.Height
import CCDN.Plane.DegreeOneAffineLine
import CCDN.Surface.LineContribution

/-!
The proved line contribution applies to degree-one prime
components, with the original number of components as the additive cost.

A finite family of degree-one prime components gives a finite
set of rational affine lines with the same rational zero-set union. Empty
rational loci are discarded, and repeated line sets are counted only once.
-/

namespace CCDN
section

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
  obtain ⟨C, hC, hline⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      3 ≤ f.totalDegree →
      ∀ (B : ℝ), 0 ≤ B →
      ∀ s : Finset (Set (RatPoint 3)),
      (∀ L ∈ s, ∃ a v, L = rationalAffineLine a v) →
      (∀ L ∈ s, L ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) →
      (∀ (v : RatPoint 3), v ≠ 0 →
        ∀ t : Finset (Set (RatPoint 3)), t ⊆ s →
          (∀ L ∈ t, ∃ a, L = rationalAffineLine a v) →
          t.card ≤ f.totalDegree * (f.totalDegree - 1)) →
      (∑ L ∈ s, (count L B : ℝ)) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + s.card ∧
      (count (⋃ L ∈ s, L) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + s.card := by
    classical
    obtain ⟨K, hK, hweight⟩ : ∃ C : ℝ, 0 < C ∧
        ∀ (d : ℕ), 3 ≤ d →
        ∀ F : MvPolynomial (Fin 3) ℤ, F.IsHomogeneous d →
        AbsolutelyIrreducible F →
        ∀ s : Finset (ProjectivePoint 2),
          (∀ x ∈ s, x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) F)) →
          ∑ x ∈ s, 1 / x.mulHeight ≤ C * (d : ℝ) ^ 4 := by
      obtain ⟨C, hC, hbound⟩ : ∃ C : ℝ, 0 < C ∧
          ∀ (d : ℕ), 3 ≤ d →
          ∀ f : MvPolynomial (Fin 3) ℚ, f.IsHomogeneous d → Irreducible f →
          ∀ s : Finset (ProjectivePoint 2), (∀ x ∈ s, x ∈ projectiveZeroLocus f) →
            ∑ x ∈ s, 1 / x.mulHeight ≤ C * (d : ℝ) ^ 4 := by
        classical
        refine ⟨9 * projectivePlaneAbsoluteConstant, by
          exact mul_pos (by norm_num) projectivePlaneAbsoluteConstant_pos, ?_⟩
        intro d hd f hf hir s hs
        have hC := projectivePlaneAbsoluteConstant_pos
        have hd0 : (0 : ℝ) < d := by positivity
        have hd3 : (3 : ℝ) ≤ d := mod_cast hd
        have h := sum_inv_height_le_of_geometric_count s (fun x => x.mulHeight)
          (projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4)
          (by positivity) (fun x _ => x.one_le_mulHeight) ?_
        · grind
        intro k
        have hB : (1 : ℝ) ≤ 8 ^ k := one_le_pow₀ (by norm_num)
        have hc : (s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card ≤
            projectiveCount (projectiveZeroLocus f) ((8 : ℝ) ^ k) := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨hxs, hheight⟩ := Finset.mem_filter.mp hx
          exact mem_projectivePoints.mpr ⟨hheight, hs x hxs⟩
        have hcR : ((s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card : ℝ) ≤
            (projectiveCount (projectiveZeroLocus f) ((8 : ℝ) ^ k) : ℝ) := mod_cast hc
        have hp : ((8 : ℝ) ^ k) ^ (2 / (d : ℝ)) ≤ (4 : ℝ) ^ k := by
          calc
            _ ≤ ((8 : ℝ) ^ k) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB
              ((div_le_div_iff₀ hd0 (by norm_num)).mpr (by nlinarith))
            _ = _ := eight_pow_two_thirds k
        exact (hcR.trans (projective_plane_equation_bound f hf (by omega) hir hB)).trans
          (mul_le_mul_of_nonneg_left hp (by positivity))
      refine ⟨C, hC, ?_⟩
      intro d hd F hF hir s hs
      exact hbound d hd (map (Int.castRingHom ℚ) F) (hF.map _)
        (rational_irreducible_of_charZero_map F hir) s hs
    refine ⟨4 * K, by positivity, ?_⟩
    intro f hir hd B hB s hlines hsurface hparallel
    let t := s.filter (fun L => 1 < count L B)
    have hdir (L : Set (RatPoint 3)) (hL : L ∈ t) :
        ∃ p : ProjectivePoint 2,
          p ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
          0 < p.mulHeight ∧ p.mulHeight ≤ 2 * B ∧
          (∃ a, L = rationalAffineLine a p.rep) ∧
          (count L B : ℝ) ≤ 4 * B / p.mulHeight :=
      surface_line_projective_direction f L (hlines L (Finset.mem_filter.mp hL).1)
        (hsurface L (Finset.mem_filter.mp hL).1) hB (Finset.mem_filter.mp hL).2
    let p : Set (RatPoint 3) → ProjectivePoint 2 := fun L =>
      if hL : L ∈ t then (hdir L hL).choose else Classical.choice inferInstance
    have hp (L : Set (RatPoint 3)) (hL : L ∈ t) :
        p L ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
        0 < (p L).mulHeight ∧ (p L).mulHeight ≤ 2 * B ∧
        (∃ a, L = rationalAffineLine a (p L).rep) ∧
        (count L B : ℝ) ≤ 4 * B / (p L).mulHeight := by
      simpa only [p, dite_eq_left hL] using (hdir L hL).choose_spec
    have hfib (q : ProjectivePoint 2) (_hq : q ∈ t.image p) :
        ((t.filter (fun L => p L = q)).card : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := by
      have hc := hparallel q.rep q.rep_nonzero (t.filter (fun L => p L = q))
        (fun L hL => (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).1) (by grind)
      exact_mod_cast hc.trans (by
        nlinarith [Nat.sub_le f.totalDegree 1])
    have himage : ∑ q ∈ t.image p, 1 / q.mulHeight ≤ K * (f.totalDegree : ℝ) ^ 4 := by
      apply hweight f.totalDegree hd (homogeneousComponent f.totalDegree f)
        (homogeneousComponent_isHomogeneous _ _) hir
      grind
    have hsum : ∑ L ∈ t, 1 / (p L).mulHeight ≤ K * (f.totalDegree : ℝ) ^ 6 := by
      calc
        _ ≤ f.totalDegree ^ 2 * ∑ q ∈ t.image p, 1 / q.mulHeight :=
          sum_comp_le_fiber_card_mul t p (fun q => 1 / q.mulHeight) _
            (fun q _ => by positivity) hfib
        _ ≤ f.totalDegree ^ 2 * (K * f.totalDegree ^ 4) :=
          mul_le_mul_of_nonneg_left himage (by positivity)
        _ = _ := by ring
    have hgood : ∑ L ∈ t, (count L B : ℝ) ≤ (4 * K) * f.totalDegree ^ 6 * B := by
      calc
        _ ≤ ∑ L ∈ t, 4 * B / (p L).mulHeight :=
          Finset.sum_le_sum (fun L hL => by grind)
        _ = 4 * B * ∑ L ∈ t, 1 / (p L).mulHeight := by
          rw [Finset.mul_sum]
          grind
        _ ≤ 4 * B * (K * f.totalDegree ^ 6) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := by ring
    have hbad : ∑ L ∈ s.filter (fun L => ¬1 < count L B), (count L B : ℝ) ≤ s.card := by
      calc
        _ ≤ ∑ _L ∈ s.filter (fun L => ¬1 < count L B), (1 : ℝ) := by
          apply Finset.sum_le_sum
          simp_all
        _ = ((s.filter (fun L => ¬1 < count L B)).card : ℝ) := by simp
        _ ≤ s.card := mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hall : ∑ L ∈ s, (count L B : ℝ) ≤
        (4 * K) * (f.totalDegree : ℝ) ^ 6 * B + s.card := by
      have he : (∑ L ∈ t, (count L B : ℝ)) +
          (∑ L ∈ s.filter (fun L => ¬1 < count L B), (count L B : ℝ)) =
          ∑ L ∈ s, (count L B : ℝ) := Finset.sum_filter_add_sum_filter_not _ _ _
      linarith
    refine ⟨hall, ?_⟩
    have hc : (count (⋃ L ∈ s, L) B : ℝ) ≤ ∑ L ∈ s, (count L B : ℝ) := by
      exact_mod_cast count_biUnion_finset_le s (fun L => L) B
    exact hc.trans hall
  refine ⟨C, hC, ?_⟩
  intro f hir hd B hB S hcurve hSf
  obtain ⟨lines, hcover, hcard, hlines⟩ : ∃ lines : Finset (Set (RatPoint 3)),
      (⋃ P ∈ S, idealZeroLocus P) = (⋃ L ∈ lines, L) ∧
      lines.card ≤ S.card ∧
      ∀ L ∈ lines, (∃ P ∈ S, L = idealZeroLocus P) ∧
        ∃ a v : RatPoint 3, v ≠ 0 ∧ L = rationalAffineLine a v := by
    classical
    let T := S.filter (fun P => (idealZeroLocus P).Nonempty)
    let lines := T.image idealZeroLocus
    refine ⟨lines, ?_, (Finset.card_image_le).trans (Finset.card_le_card
      (Finset.filter_subset _ _)), ?_⟩
    · ext x
      constructor
      · intro hx
        obtain ⟨P, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hx
        have hPT : P ∈ T := Finset.mem_filter.mpr ⟨hPS, ⟨x, hxP⟩⟩
        exact Set.mem_iUnion.mpr ⟨idealZeroLocus P,
          Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨P, hPT, rfl⟩, hxP⟩⟩
      · aesop
    · intro L hL
      obtain ⟨P, hPT, rfl⟩ := Finset.mem_image.mp hL
      obtain ⟨hPS, z, hz⟩ := Finset.mem_filter.mp hPT
      obtain ⟨hp, hheight, hdegree⟩ := hcurve P hPS
      obtain ⟨v, hv, he⟩ : ∃ v : RatPoint 3, v ≠ 0 ∧ idealZeroLocus P = rationalAffineLine z v := by
        obtain ⟨N, b, hN⟩ := hdegree
        obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point P hheight z hz
        have hdim : Module.finrank ℚ (filteredCoordinateSpace P (N + 1)) =
            Module.finrank ℚ (filteredCoordinateSpace P N) + 1 := by
          have h0 := hN N le_rfl
          have h1 := hN (N + 1) (by omega)
          push_cast [affineHilbertFunction] at h0 h1
          omega
        have hUone : (1 : MvPolynomial (Fin 3) ℚ ⧸ P) ∈ filteredCoordinateSpace P N := by
          apply Submodule.mem_map.mpr
          refine ⟨1, ?_, by simp⟩
          rw [mem_restrictTotalDegree, totalDegree_one]
          omega
        have hex (k : Fin 3) : ∃ c d : ℚ,
            (Ideal.Quotient.mk P) (X k) = c • (Ideal.Quotient.mk P) (X j) +
              algebraMap ℚ (MvPolynomial (Fin 3) ℚ ⧸ P) d := by
          obtain ⟨c, hc⟩ := algebraic_difference_of_critical_growth
            (filteredCoordinateSpace P N) (filteredCoordinateSpace P (N + 1))
            (filteredCoordinateSpace_mono P (by omega)) hUone hdim hj
            (fun _ hu => coordinate_mul_filtered_mem P j N hu)
            (fun _ hu => coordinate_mul_filtered_mem P k N hu)
          refine ⟨c, coordinatePoint P z hz (Ideal.Quotient.mk P (X k) - c • Ideal.Quotient.mk P (X j)), ?_⟩
          rw [algebraic_eq_scalar_of_point (coordinatePoint P z hz) hc]
          abel
        choose c d hcd using hex
        have hcj : c j ≠ 0 := by
          intro hc
          have he := hcd j
          rw [hc, zero_smul, zero_add] at he
          apply hj
          rw [he]
          exact isAlgebraic_algebraMap (d j)
        refine ⟨c, fun h => hcj (congrFun h j), ?_⟩
        have hpoint (x : Fin 3 → ℚ) (hx : x ∈ idealZeroLocus P) (k : Fin 3) :
            x k = c k * x j + d k := by
          have he := congrArg (coordinatePoint P x hx) (hcd k)
          simpa using he
        ext x
        constructor
        · intro hx
          refine ⟨x j - z j, ?_⟩
          funext k
          change x k = z k + (x j - z j) * c k
          grind
        · rintro ⟨t, rfl⟩ f hf
          have hpoly := affine_coordinates_line_polynomial_identity P j c d hj hcd z hz f hf
          have he : (Polynomial.aeval t).comp
              (MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X)) =
              MvPolynomial.aeval (z + t • c) := by
            apply MvPolynomial.algHom_ext
            intro k
            simp
            ring
          have hz' := congrArg (Polynomial.aeval t) hpoly
          change ((Polynomial.aeval t).comp
            (MvPolynomial.aeval (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X))) f =
              (Polynomial.aeval t) 0 at hz'
          rwa [he, map_zero, MvPolynomial.aeval_eq_eval] at hz'
      grind
  have hsurf : ∀ L ∈ lines, L ⊆ zeroLocus (map (Int.castRingHom ℚ) f) := by
    intro L hL x hx
    obtain ⟨P, hPS, rfl⟩ := (hlines L hL).1
    exact hx _ (hSf P hPS)
  have hh := (hline f hir hd B hB lines (by grind) hsurf fun v hv t ht htv =>
    surface_parallel_lines_card_le f hir (by omega) v hv t htv fun L hL => hsurf L (ht hL)).2
  rw [← hcover] at hh
  exact hh.trans (add_le_add le_rfl (mod_cast hcard))

