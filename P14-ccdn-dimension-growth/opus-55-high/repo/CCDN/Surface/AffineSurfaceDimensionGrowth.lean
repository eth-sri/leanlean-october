/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Height.Box
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Surface.AffineSurfaceCountLargeDegree
import CCDN.Surface.PrimitiveSurfaceFixedDegree
import CCDN.Surface.TopFormBadPrimes

/-!
The affine surface bound in every degree at least five. The finitely many
degrees below the large-degree threshold are absorbed in one constant.

Removing integer content from the fixed-degree surface estimate.
The resulting constant is uniform in all integer coefficients.
-/

namespace CCDN
section
open MvPolynomial

/-- Every fixed degree at least five has a coefficient-uniform linear
integer-point bound when the highest homogeneous part is absolutely
irreducible. The equation need not be primitive. -/
theorem top_form_surface_fixed_degree_linear_bound (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := primitive_surface_fixed_degree_linear_bound d hd
  refine ⟨C, hC, ?_⟩
  intro f hir hfd B hB
  obtain ⟨c, u, hc, hprim, he⟩ := exists_primitive_integer_factor f (by aesop)
  obtain ⟨hudeg, hutop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
  have hzero : zeroLocus (map (Int.castRingHom ℚ) f) =
      zeroLocus (map (Int.castRingHom ℚ) u) := by
    ext x
    change eval x (map (Int.castRingHom ℚ) f) = 0 ↔
      eval x (map (Int.castRingHom ℚ) u) = 0
    rw [he, map_mul, map_C, eval_mul, eval_C]
    exact mul_eq_zero_iff_left (show (c : ℚ) ≠ 0 by exact_mod_cast hc)
  rw [hzero]
  exact hbound u hprim hutop (hudeg.trans hfd) B hB

/-- Corrected CCDN Proposition 4.3.4 in every degree at least five: the surface bound
`C d^18 B` for integer equations in three variables with absolutely irreducible top-degree
form. -/
theorem affine_surface_dimension_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * (f.totalDegree : ℝ) ^ 18 * B := by
  obtain ⟨Cbig, hCbig, hbig⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      topFormSurfaceThreshold ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        C * f.totalDegree ^ 18 * B := by
    obtain ⟨A, hA, hnonlinear⟩ : ∃ A : ℝ, 0 < A ∧
        ∀ f : MvPolynomial (Fin 3) ℤ,
        HasAbsIrreducibleTopForm f →
        16 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
        ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
          ∃ δ : Ideal (CoordinatePolynomial 3) → ℕ,
            (∀ P ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) P (δ P) ∧ 0 < δ P) ∧
            (∀ x : IntPoint 3, InBox x B → eval x f = 0 →
              ∃ P ∈ S, rationalPoint x ∈ idealZeroLocus P) ∧
            ((∑ P ∈ S, δ P : ℕ) : ℝ) ≤ topFormAuxiliaryConstant 1 *
              (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) *
                B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) ∧
            (count (⋃ P ∈ S.filter (fun P => 2 ≤ δ P), idealZeroLocus P) B : ℝ) ≤
              A * (f.totalDegree : ℝ) ^ 18 * B ∧
            (count (zeroLocus (map (Int.castRingHom ℚ) f) \
              (⋃ P ∈ S.filter (fun P => δ P = 1), idealZeroLocus P)) B : ℝ) ≤
                A * (f.totalDegree : ℝ) ^ 18 * B := by
      obtain ⟨K, hK, hcount⟩ := affine_curve_count 3 (by omega)
      let C := topFormAuxiliaryConstant 1
      have hC := topFormAuxiliaryConstant_pos 1
      let A := K * Real.exp 1 * (480 * C + 2 * C ^ 4)
      refine ⟨A, by positivity, ?_⟩
      intro f hir hd B hB
      have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f hir
      have hfQ :=
        rational_irreducible_of_charZero_map f habs
      have hdR : (0 : ℝ) < f.totalDegree := by norm_cast; omega
      obtain ⟨c, u, hc, huprim, he⟩ := exists_primitive_integer_factor f fun hz => hir.ne_zero (by grind)
      obtain ⟨huDegree, huTop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
      obtain ⟨g, ⟨_, hgnd, hgz⟩, hgdeg⟩ := primitive_top_form_auxiliary u huprim huTop hB
      replace hgnd : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g := fun h => hgnd
        (huprim.rational_map_dvd_iff.mp ((map_dvd (map (Int.castRingHom ℚ)) ⟨MvPolynomial.C c, by grind⟩).trans h))
      replace hgz (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0) : eval x g = 0 := by aesop
      rw [huDegree] at hgdeg
      have hgdegree : (g.totalDegree : ℝ) ≤ topFormAuxiliaryConstant 1 *
          (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) *
            B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) := by
        norm_num at hgdeg ⊢
        exact hgdeg
      obtain ⟨S, δ, hcomponents, hcov, hbudget⟩ :=
        exists_completeIntersection_curve_components (map (Int.castRingHom ℚ) f)
          (map (Int.castRingHom ℚ) g) hfQ hgnd
      have hmapdegree (p : MvPolynomial (Fin 3) ℤ) :
          (map (Int.castRingHom ℚ) p).totalDegree = p.totalDegree :=
          totalDegree_map_of_injective Int.cast_injective _
      have hpower : (f.totalDegree : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) =
          (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) := by
        calc
          _ = (f.totalDegree : ℝ) ^ (1 : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) := by simp_all
          _ = (f.totalDegree : ℝ) ^ ((1 : ℝ) + 7 / 2) := (Real.rpow_add hdR _ _).symm
          _ = _ := by norm_num
      have hsum : ((∑ P ∈ S, δ P : ℕ) : ℝ) ≤ topFormAuxiliaryConstant 1 *
          (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) := by
        have hbudgetR : ((∑ P ∈ S, δ P : ℕ) : ℝ) ≤
            (f.totalDegree : ℝ) * g.totalDegree := by
          rw [hmapdegree f, hmapdegree g] at hbudget
          exact_mod_cast hbudget
        calc
          _ ≤ (f.totalDegree : ℝ) * g.totalDegree := hbudgetR
          _ ≤ (f.totalDegree : ℝ) * (topFormAuxiliaryConstant 1 *
              (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) *
                B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hgdegree hdR.le
          _ = topFormAuxiliaryConstant 1 *
              ((f.totalDegree : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ)) *
                B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) := by ring
          _ = _ := by grind
      have hcover : ∀ x : IntPoint 3, InBox x B → eval x f = 0 →
          ∃ P ∈ S, rationalPoint x ∈ idealZeroLocus P := by
        intro x hx hxf
        have hmapzero (p : MvPolynomial (Fin 3) ℤ) (hp : eval x p = 0) :
            eval (rationalPoint x) (map (Int.castRingHom ℚ) p) = 0 := by
          have hh := congrArg (Int.castRingHom ℚ) hp
          rwa [map_eval, map_zero] at hh
        have hxsection : rationalPoint x ∈
            zeroLocus (map (Int.castRingHom ℚ) f) ∩ zeroLocus (map (Int.castRingHom ℚ) g) :=
          ⟨hmapzero f hxf, hmapzero g (hgz x hx hxf)⟩
        simp_all
      let T := S.filter (fun P => 2 ≤ δ P)
      let L := ⋃ P ∈ S.filter (fun P => δ P = 1), idealZeroLocus P
      have hcurves (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
          P.IsPrime ∧ 2 ≤ δ P ∧ HasAffineCurveDegree P (δ P) := by
        obtain ⟨hPS, hδ⟩ := Finset.mem_filter.mp hP
        exact ⟨(hcomponents P hPS).isPrime, hδ, (hcomponents P hPS).degree⟩
      have hsubsum : (∑ P ∈ T, δ P) ≤ ∑ P ∈ S, δ P :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by grind)
      have hTsum : (∑ P ∈ T, (δ P : ℝ)) ≤
          C * f.totalDegree ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt f.totalDegree) := by
        have hcast : ((∑ P ∈ T, δ P : ℕ) : ℝ) ≤ ((∑ P ∈ S, δ P : ℕ) : ℝ) := by
          exact_mod_cast hsubsum
        simpa only [Nat.cast_sum, ← Real.sqrt_eq_rpow] using hcast.trans hsum
      have hnonlinear : (count (⋃ P ∈ T, idealZeroLocus P) B : ℝ) ≤ A * f.totalDegree ^ 18 * B :=
        calc
          _ ≤ ∑ P ∈ T, (count (idealZeroLocus P) B : ℝ) := by
            exact_mod_cast count_biUnion_finset_le T idealZeroLocus B
          _ ≤ ∑ P ∈ T, K * curveBound (δ P) B := by
            apply Finset.sum_le_sum
            grind
          _ = K * ∑ P ∈ T, curveBound (δ P) B := (Finset.mul_sum _ _ _).symm
          _ ≤ K * (Real.exp 1 * (480 * C + 2 * C ^ 4) * f.totalDegree ^ 18 * B) :=
            mul_le_mul_of_nonneg_left (sum_curveBound_le_surface_degree_budget T δ hd hC.le hB
              (fun P hP => (hcurves P hP).2.1) hTsum) hK.le
          _ = _ := by ring
      have houtside :
          count (zeroLocus (map (Int.castRingHom ℚ) f) \ L) B ≤
            count (⋃ P ∈ T, idealZeroLocus P) B := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨hbox, hxf, hxL⟩ := mem_integralPoints.mp hx
        obtain ⟨P, hPS, hxP⟩ := hcover x hbox (by
          apply Int.cast_injective (α := ℚ)
          change (Int.castRingHom ℚ) (eval x f) = (Int.castRingHom ℚ) 0
          rwa [map_eval, map_zero])
        have hpositive := (hcomponents P hPS).pos
        have hnotone : δ P ≠ 1 := by aesop
        exact mem_integralPoints.mpr ⟨hbox,
          Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mpr ⟨hPS, by omega⟩), hxP⟩⟩⟩
      refine ⟨S, δ, ?_, hcover, hsum, hnonlinear, ?_⟩
      · exact fun P hPS => ⟨(hcomponents P hPS).toIsSurfaceCurve, (hcomponents P hPS).pos⟩
      · have hh : (count (zeroLocus (map (Int.castRingHom ℚ) f) \ L) B : ℝ) ≤
            (count (⋃ P ∈ T, idealZeroLocus P) B : ℝ) := mod_cast houtside
        grind
    obtain ⟨C, hC, hlines⟩ := surface_degree_one_component_contribution
    let K := topFormAuxiliaryConstant 1
    have hK := topFormAuxiliaryConstant_pos 1
    refine ⟨A + C + K, by positivity, ?_⟩
    intro f hir hd B hB
    unfold topFormSurfaceThreshold at hd
    obtain ⟨S, δ, hcomponents, _, hdegree, _, houtside⟩ :=
      hnonlinear f hir hd B hB
    let T := S.filter (fun P => δ P = 1)
    let L := ⋃ P ∈ T, idealZeroLocus P
    have hTcurve (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
        P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P 1 := by
      obtain ⟨hPS, hone⟩ := Finset.mem_filter.mp hP
      exact ⟨(hcomponents P hPS).1.isPrime, (hcomponents P hPS).1.height_eq,
        by simpa [hone] using (hcomponents P hPS).1.degree⟩
    have hTsurface (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
        map (Int.castRingHom ℚ) f ∈ P :=
      (hcomponents P (Finset.mem_filter.mp hP).1).1.mem
    have hlinecount :=
      hlines f hir (by omega) B (by linarith) T hTcurve hTsurface
    have hcard : T.card ≤ ∑ P ∈ S, δ P := by
      calc
        T.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = ∑ _P ∈ S, 1 := by simp
        _ ≤ ∑ P ∈ S, δ P := by
          apply Finset.sum_le_sum
          grind
    have hcardR : (T.card : ℝ) ≤ K * (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) *
        B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) := by
      have hh : (T.card : ℝ) ≤ ((∑ P ∈ S, δ P : ℕ) : ℝ) := by
        exact_mod_cast hcard
      exact hh.trans hdegree
    have hd1 : (1 : ℝ) ≤ f.totalDegree := mod_cast (show 1 ≤ f.totalDegree by omega)
    have hroot : (1 : ℝ) ≤ f.totalDegree ^ (1 / 2 : ℝ) :=
      Real.one_le_rpow hd1 (by norm_num)
    have hexp :=
      (div_le_one (by positivity)).2 hroot
    have hBpower : B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) ≤ B := by
      simpa using Real.rpow_le_rpow_of_exponent_le hB hexp
    have hdpower : (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) ≤ (f.totalDegree : ℝ) ^ 18 := by
      simpa using
        Real.rpow_le_rpow_of_exponent_le hd1 (show (9 / 2 : ℝ) ≤ 18 by norm_num)
    have hcardfinal : (T.card : ℝ) ≤ K * (f.totalDegree : ℝ) ^ 18 * B := by
      apply hcardR.trans
      gcongr
    have hdsix : (f.totalDegree : ℝ) ^ 6 ≤ (f.totalDegree : ℝ) ^ 18 :=
      pow_le_pow_right₀ hd1 (by omega)
    have hlinefinal : (count L B : ℝ) ≤ (C + K) * (f.totalDegree : ℝ) ^ 18 * B := by
      calc
        _ ≤ C * (f.totalDegree : ℝ) ^ 6 * B + T.card := hlinecount
        _ ≤ C * (f.totalDegree : ℝ) ^ 18 * B +
            K * (f.totalDegree : ℝ) ^ 18 * B := by gcongr
        _ = _ := by ring
    have hcover : zeroLocus (map (Int.castRingHom ℚ) f) ⊆
        (zeroLocus (map (Int.castRingHom ℚ) f) \ L) ∪ L := by
      intro x hx
      by_cases hxL : x ∈ L
      · grind
      · grind
    have htotal :=
      (count_mono hcover le_rfl).trans (count_union_le _ _ B)
    calc
      _ ≤ (count (zeroLocus (map (Int.castRingHom ℚ) f) \ L) B : ℝ) + count L B := by
        exact_mod_cast htotal
      _ ≤ A * (f.totalDegree : ℝ) ^ 18 * B +
          (C + K) * (f.totalDegree : ℝ) ^ 18 * B :=
        add_le_add houtside hlinefinal
      _ = _ := by ring
  obtain ⟨Csmall, hCsmall, hsmall⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → f.totalDegree < topFormSurfaceThreshold → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ C * B := by
    induction topFormSurfaceThreshold with
    | zero => exact ⟨1, one_pos, fun _ _ _ ht => absurd ht (Nat.not_lt_zero _)⟩
    | succ topFormSurfaceThreshold ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      by_cases ht : 5 ≤ topFormSurfaceThreshold
      · obtain ⟨C', hC', hbound'⟩ := top_form_surface_fixed_degree_linear_bound topFormSurfaceThreshold ht
        refine ⟨C + C', by positivity, fun f hir hd hlt B hB => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
        · exact (hbound f hir hd hlt B hB).trans (by nlinarith)
        · exact (hbound' f hir heq B hB).trans (by nlinarith)
      · grind
  refine ⟨Cbig + Csmall, by positivity, fun f hir hd B hB => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  have hdpow : 1 ≤ (f.totalDegree : ℝ) ^ 18 :=
    one_le_pow₀ (mod_cast (show 1 ≤ f.totalDegree by omega))
  by_cases hlarge : topFormSurfaceThreshold ≤ f.totalDegree
  · exact (hbig f hir hlarge B hB).trans (by gcongr; linarith)
  · calc
      _ ≤ Csmall * B := hsmall f hir hd (by omega) B hB
      _ ≤ (Cbig + Csmall) * 1 * B := by nlinarith
      _ ≤ (Cbig + Csmall) * (f.totalDegree : ℝ) ^ 18 * B := by gcongr

