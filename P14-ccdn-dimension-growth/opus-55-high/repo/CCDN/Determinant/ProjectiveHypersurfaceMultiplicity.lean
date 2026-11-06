/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
import CCDN.Algebra.CharZeroOrGT
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Determinant.PlaneMultiplicitySmooth
import CCDN.Determinant.PlaneSingularities
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Height.FiniteFieldSectionCount
import Mathlib.RingTheory.SimpleRing.Principal

/-!
The singular multiplicity correction for projective hypersurfaces.
Chart coordinates inject each selected residue class into an affine
singular locus, whose codimension-two point bound is proved by interpolation.

The singular points of an irreducible hypersurface satisfy a
coefficient-uniform codimension-two finite-field bound.
-/

namespace CCDN
open MvPolynomial

section
variable {n p : ℕ} [Fact p.Prime]

lemma hypersurfaceResidueChart_normalized
    (r : ProjectiveResidueSpace (n + 2) p) :
    (Fin.cons 1 (fun j => (projectiveResidueChartLift r j : ZMod p))) ∘
      Equiv.swap 0 (projectiveResiduePivot r) =
        (r.rep (projectiveResiduePivot r))⁻¹ • r.rep := by
  have h : Fin.cons 1 (fun j => (projectiveResidueChartLift r j : ZMod p)) =
      (r.rep (projectiveResiduePivot r))⁻¹ •
        (r.rep ∘ Equiv.swap 0 (projectiveResiduePivot r)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [projectiveResiduePivot_ne_zero]
    · simp [cast_projectiveResidueChartLift, div_eq_mul_inv, mul_comm]
  rw [h]
  funext j
  simp

theorem hypersurfaceResidueChart_injective_of_pivot_eq
    {r t : ProjectiveResidueSpace (n + 2) p}
    (hk : projectiveResiduePivot r = projectiveResiduePivot t)
    (ha : (fun j => (projectiveResidueChartLift r j : ZMod p)) =
      (fun j => (projectiveResidueChartLift t j : ZMod p))) : r = t := by
  have he : (r.rep (projectiveResiduePivot r))⁻¹ • r.rep =
      (t.rep (projectiveResiduePivot t))⁻¹ • t.rep := by
    rw [← hypersurfaceResidueChart_normalized, ← hypersurfaceResidueChart_normalized, hk, ha]
  have hh := congrArg (fun v => r.rep (projectiveResiduePivot r) • v) he
  have hs : (r.rep (projectiveResiduePivot r) / t.rep (projectiveResiduePivot t)) • t.rep =
      r.rep := by
    simpa [smul_smul, mul_inv_cancel₀ (projectiveResiduePivot_ne_zero r), one_smul,
      div_eq_mul_inv] using hh.symm
  calc
    r = Projectivization.mk (ZMod p) r.rep r.rep_nonzero := r.mk_rep.symm
    _ = Projectivization.mk (ZMod p) t.rep t.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      grind
    _ = t := t.mk_rep

end

section
variable {n p d : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
include hf

theorem projectiveHypersurfaceChart_irreducible_degree
    (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (k : Fin (n + 3)) :
    Irreducible (map (Int.castRingHom (ZMod p)) (projectivePlaneChart k f)) ∧
      (map (Int.castRingHom (ZMod p)) (projectivePlaneChart k f)).totalDegree = d := by
  let q := rename (Equiv.swap 0 k) (map (Int.castRingHom (ZMod p)) f)
  have hq : q.IsHomogeneous d := (hf.map _).rename_isHomogeneous
  have hqi :=
    (MulEquiv.irreducible_iff (f := renameEquiv (ZMod p) (Equiv.swap 0 k))).mpr hir
  have hX := variable_not_dvd_irreducible_homogeneous q hq hqi hd 0
  have he :
      map (Int.castRingHom (ZMod p)) (projectivePlaneChart k f) = affineChart (n + 2) q := by
    change map _ (affineChart (n + 2) (rename (Equiv.swap 0 k) f)) = _
    rw [← affineChart_map, map_rename]
  rw [he]
  exact ⟨affineChart_irreducible_of_not_variable_dvd q hq hqi hX,
    affineChart_degree_of_not_variable_dvd q hq hX⟩

lemma projectiveHypersurfaceResidueMultiplicity_singular
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (r : ProjectiveHypersurfaceResidue f p)
    (hμ : 2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hf0 r) :
    ∀ j, eval (fun i => (projectiveResidueChartLift r.val i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p))
        (projectivePlaneChart (projectiveResiduePivot r.val) f))) = 0 := by
  have hp := (projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 r).2.2.1
  change map (Int.castRingHom (ZMod p)) (originShift (projectiveResidueChartLift r.val)
    (projectivePlaneChart (projectiveResiduePivot r.val) f)) ∈ _ at hp
  rw [originShift_map] at hp
  exact singular_of_origin_order_ge_two _ _ hμ hp

end

variable {n p d : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
include hd

/-- Count singular classes in their n+3 possible charts. The pivots and
multiplicities here are those of the reduced projective hypersurface. -/
theorem projective_hypersurface_singular_residue_card_le
    (hchar : d < p) :
    (Finset.univ.filter fun r : ProjectiveHypersurfaceResidue f p =>
      2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r).card ≤
      (n + 3) * ((n + 4) ^ n * d * (d - 1) * p ^ n) := by
  classical
  let S := Finset.univ.filter fun r =>
    2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r
  let T (k : Fin (n + 3)) := S.filter fun r => projectiveResiduePivot r.val = k
  have hk {k : Fin (n + 3)} (r : T k) : projectiveResiduePivot r.val.val = k :=
    (Finset.mem_filter.mp r.property).2
  have hT (k : Fin (n + 3)) : (T k).card ≤ (n + 4) ^ n * d * (d - 1) * p ^ n := by
    let q := map (Int.castRingHom (ZMod p)) (projectivePlaneChart k f)
    have hq := projectiveHypersurfaceChart_irreducible_degree f hf hd hir k
    let z : T k → Fin (n + 2) → ZMod p :=
      fun r j => (projectiveResidueChartLift r.val.val j : ZMod p)
    have hz : Function.Injective z := by
      intro r t he
      apply Subtype.ext
      apply Subtype.ext
      exact hypersurfaceResidueChart_injective_of_pivot_eq ((hk r).trans (hk t).symm) he
    have hzero (r : T k) : eval (z r) q = 0 := by
      have h := projectiveResidueChartLift_zero f hf r.val.val r.val.property
      aesop
    have hsing (r : T k) (j : Fin (n + 2)) : eval (z r) (pderiv j q) = 0 := by
      have h := projectiveHypersurfaceResidueMultiplicity_singular f hf hir.ne_zero r.val
        (Finset.mem_filter.mp (Finset.mem_filter.mp r.property).1).2 j
      grind
    obtain ⟨j, hj⟩ := exists_pderiv_ne_zero (by grind : 0 < q.totalDegree)
      (CharZeroOrGT.of_charP (by grind : q.totalDegree < p))
    have hdeg := pderiv_totalDegree_le q j
    have h := finite_field_common_zeros_card_le q (pderiv j q) hq.1.prime
      (not_dvd_pderiv_of_pderiv_ne_zero hq.1.ne_zero hj) (by rw [ZMod.card]; grind) z hz hzero
      fun r => hsing r j
    rw [ZMod.card] at h
    replace h := h.trans (Nat.mul_le_mul_right (p ^ n)
      (Nat.mul_le_mul_left ((n + 4) ^ n * q.totalDegree) hdeg))
    simp_all [Fintype.card_coe, q, hq.2]
  have hsum : ∑ k : Fin (n + 3), (T k).card = S.card := by
    simp only [T, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n + 3)))) => hT k)
  rw [hsum] at h
  simpa
    using h

/-- Singular classes contribute only a lower-order correction to the
projective point count; the leading term is not multiplied by the degree. -/
theorem projectiveHypersurfaceTotalMultiplicity_le_card_add_correction
    (hchar : d < p) :
    projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        (n + 3) * (n + 4) ^ n * d ^ 2 * (d - 1) * p ^ n := by
  classical
  let S := Finset.univ.filter fun r =>
    2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r
  have hS :=
    projective_hypersurface_singular_residue_card_le f hf hd hir hchar
  have hpoint (r : ProjectiveHypersurfaceResidue f p) :
      projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r ≤
        1 + if r ∈ S then d else 0 := by
    have h := (projectiveHypersurfaceResidueMultiplicity_spec f hf hir.ne_zero r).2.1
    by_cases hr : r ∈ S
    · grind
    · grind
  have hsum : projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) + S.card * d := by
    calc _ ≤ ∑ r : ProjectiveHypersurfaceResidue f p, (1 + if r ∈ S then d else 0) :=
           Finset.sum_le_sum fun r _ => hpoint r
         _ = _ := by simp [Finset.sum_add_distrib]
  apply hsum.trans
  apply Nat.add_le_add_left
  convert Nat.mul_le_mul_right d hS using 1
  ring

/-- Above the square-degree cutoff the multiplicity correction has the
O_n(d^2 p^(dimension-1/2)) scale required by CCDN Lemma 2.7. -/
theorem projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error
    (hsize : d ^ 2 < p) :
    (projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        ((n + 3) * (n + 4) ^ n : ℕ) * (d : ℝ) ^ 2 * (p : ℝ) ^ n * Real.sqrt p := by
  have h := projectiveHypersurfaceTotalMultiplicity_le_card_add_correction f hf hd hir ((Nat.le_mul_self d).trans_lt (by grind))
  have hR : (projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        ((n + 3) * (n + 4) ^ n * d ^ 2 * (d - 1) * p ^ n : ℕ) := mod_cast h
  have hs : d ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (mod_cast hsize.le)
  have hsub :=
    (mod_cast Nat.sub_le d 1 : ((d - 1 : ℕ) : ℝ) ≤ d).trans hs
  have hmul := mul_le_mul_of_nonneg_left hsub
    (show 0 ≤ (((n + 3) * (n + 4) ^ n : ℕ) : ℝ) * (d : ℝ) ^ 2 * (p : ℝ) ^ n by positivity)
  apply hR.trans
  apply add_le_add le_rfl
  push_cast at hmul ⊢
  convert hmul using 1
  ring

