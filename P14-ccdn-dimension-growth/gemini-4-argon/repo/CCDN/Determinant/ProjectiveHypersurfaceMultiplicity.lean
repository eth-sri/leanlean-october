/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Above the square-degree cutoff the multiplicity correction has the
O_n(d^2 p^(dimension-1/2)) scale required by CCDN Lemma 2.7. -/
theorem projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error {n p d : ℕ}
    [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hd : 2 ≤ d) (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hsize : d ^ 2 < p) :
    (projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        ((n + 3) * (n + 4) ^ n : ℕ) * (d : ℝ) ^ 2 * (p : ℝ) ^ n * Real.sqrt p := by
  classical
  have hnorm (r : ProjectiveResidueSpace (n + 2) p) :
      (Fin.cons 1 (fun j => (hypersurfaceResidueChartLift r j : ZMod p))) ∘
        Equiv.swap 0 (hypersurfaceResiduePivot r) =
          (r.rep (hypersurfaceResiduePivot r))⁻¹ • r.rep := by
    rw [show Fin.cons 1 (fun j => (hypersurfaceResidueChartLift r j : ZMod p)) =
        (r.rep (hypersurfaceResiduePivot r))⁻¹ •
          (r.rep ∘ Equiv.swap 0 (hypersurfaceResiduePivot r)) from funext fun j =>
      Fin.cases (by simp [hypersurfaceResiduePivot_ne_zero])
        (fun k => by simp [cast_hypersurfaceResidueChartLift, div_eq_mul_inv, mul_comm]) j]
    funext j; simp
  have hchar : d < p := (Nat.le_mul_self d).trans_lt (by simpa only [pow_two] using hsize)
  let S := Finset.univ.filter fun r : ProjectiveHypersurfaceResidue f p =>
    2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r
  let T (k : Fin (n + 3)) := S.filter fun r => hypersurfaceResiduePivot r.val = k
  have hk {k : Fin (n + 3)} (r : T k) : hypersurfaceResiduePivot r.val.val = k :=
    (Finset.mem_filter.mp r.property).2
  have hT (k : Fin (n + 3)) : (T k).card ≤ (n + 4) ^ n * d * (d - 1) * p ^ n := by
    let q0 := rename (Equiv.swap 0 k) (map (Int.castRingHom (ZMod p)) f)
    have hq0 : q0.IsHomogeneous d := (hf.map _).rename_isHomogeneous
    have hq0i : Irreducible q0 :=
      (MulEquiv.irreducible_iff (f := renameEquiv (ZMod p) (Equiv.swap 0 k))).mpr hir
    have hX := variable_not_dvd_irreducible_homogeneous q0 hq0 hq0i hd 0
    let q := map (Int.castRingHom (ZMod p)) (projectiveHypersurfaceChart k f)
    have hq_eq : q = affineChart (n + 2) q0 := by
      change map _ (affineChart (n + 2) (rename (Equiv.swap 0 k) f)) = _
      rw [← affineChart_map, map_rename]
    have hq_ir : Irreducible q := hq_eq ▸ affineChart_irreducible_of_not_variable_dvd q0 hq0 hq0i hX
    have hq_deg : q.totalDegree = d := hq_eq ▸ affineChart_degree_of_not_variable_dvd q0 hq0 hX
    let z : T k → Fin (n + 2) → ZMod p :=
      fun r j => (hypersurfaceResidueChartLift r.val.val j : ZMod p)
    have hz : Function.Injective z := by
      intro r t he
      apply Subtype.ext; apply Subtype.ext
      have hkp : hypersurfaceResiduePivot r.val.val = hypersurfaceResiduePivot t.val.val :=
        (hk r).trans (hk t).symm
      have ha : (fun j => (hypersurfaceResidueChartLift r.val.val j : ZMod p)) =
          (fun j => (hypersurfaceResidueChartLift t.val.val j : ZMod p)) := he
      have he' : (r.val.val.rep (hypersurfaceResiduePivot r.val.val))⁻¹ • r.val.val.rep =
          (t.val.val.rep (hypersurfaceResiduePivot t.val.val))⁻¹ • t.val.val.rep := by
        rw [← hnorm, ← hnorm, hkp, ha]
      have hh := congrArg (fun v : Fin (n + 3) → ZMod p =>
        r.val.val.rep (hypersurfaceResiduePivot r.val.val) • v) he'
      have hs : (r.val.val.rep (hypersurfaceResiduePivot r.val.val) /
          t.val.val.rep (hypersurfaceResiduePivot t.val.val)) • t.val.val.rep = r.val.val.rep := by
        simpa only [smul_smul, mul_inv_cancel₀ (hypersurfaceResiduePivot_ne_zero r.val.val),
          one_smul, div_eq_mul_inv] using hh.symm
      exact r.val.val.mk_rep.symm.trans
        ((Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr ⟨_, hs⟩ |>.trans t.val.val.mk_rep)
    have hzero (r : T k) : eval (z r) q = 0 := by
      have h := hypersurfaceResidueChartLift_zero f hf r.val.val r.val.property
      rw [hk r] at h
      simpa only [q, z, eval_map] using h
    have hsing (r : T k) (j : Fin (n + 2)) : eval (z r) (pderiv j q) = 0 := by
      have hp := (projectiveHypersurfaceResidueMultiplicity_spec f hf hir.ne_zero r.val).2.2.1
      change map (Int.castRingHom (ZMod p)) (originShift (hypersurfaceResidueChartLift r.val.val)
        (projectiveHypersurfaceChart (hypersurfaceResiduePivot r.val.val) f)) ∈ _ at hp
      rw [originShift_map] at hp
      have h := singular_of_origin_order_ge_two _ _
        (Finset.mem_filter.mp (Finset.mem_filter.mp r.property).1).2 hp j
      dsimp only [q, z]
      simpa only [Int.coe_castRingHom, hk r] using h
    obtain ⟨j, hj⟩ := exists_pderiv_ne_zero (by rw [hq_deg]; omega : 0 < q.totalDegree)
      (CharZeroOrGT.of_charP (by rwa [hq_deg]))
    have hdeg := pderiv_totalDegree_le q j
    have h := finite_field_common_zeros_card_le q (pderiv j q) hq_ir.prime
      (not_dvd_pderiv_of_pderiv_ne_zero hq_ir.ne_zero hj)
      (by rw [ZMod.card]; omega) z hz hzero fun i => hsing i j
    rw [ZMod.card] at h
    simpa only [Fintype.card_coe, hq_deg] using h.trans (Nat.mul_le_mul_right (p ^ n)
      (Nat.mul_le_mul_left ((n + 4) ^ n * q.totalDegree) hdeg))
  have hS : S.card ≤ (n + 3) * ((n + 4) ^ n * d * (d - 1) * p ^ n) := by
    have hsum : ∑ k : Fin (n + 3), (T k).card = S.card := by
      simp only [T, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]; simp
    have h := Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin (n + 3)))) => hT k
    rw [hsum] at h
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc] using h
  have hpoint (r : ProjectiveHypersurfaceResidue f p) :
      projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r ≤
        1 + if r ∈ S then d else 0 := by
    have h := (projectiveHypersurfaceResidueMultiplicity_spec f hf hir.ne_zero r).2.1
    by_cases hr : r ∈ S
    · rw [ite_eq_left hr]; omega
    · rw [ite_eq_right hr]
      have hh : ¬ 2 ≤ projectiveHypersurfaceResidueMultiplicity f hf hir.ne_zero r := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hr
      omega
  have hsum : projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) + S.card * d := by
    calc _ ≤ ∑ r : ProjectiveHypersurfaceResidue f p, (1 + if r ∈ S then d else 0) :=
           Finset.sum_le_sum fun r _ => hpoint r
         _ = _ := by simp [Finset.sum_add_distrib]
  have hsum' : projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        (n + 3) * (n + 4) ^ n * d ^ 2 * (d - 1) * p ^ n := by
    refine hsum.trans (Nat.add_le_add_left ?_ _)
    convert Nat.mul_le_mul_right d hS using 1
    ring
  have hR : (projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        ((n + 3) * (n + 4) ^ n * d ^ 2 * (d - 1) * p ^ n : ℕ) := mod_cast hsum'
  have hsub : ((d - 1 : ℕ) : ℝ) ≤ Real.sqrt p :=
    (by exact_mod_cast Nat.sub_le d 1 : ((d - 1 : ℕ) : ℝ) ≤ d).trans
      (Real.le_sqrt_of_sq_le (mod_cast hsize.le))
  have hmul := mul_le_mul_of_nonneg_left hsub
    (show 0 ≤ (((n + 3) * (n + 4) ^ n : ℕ) : ℝ) * (d : ℝ) ^ 2 * (p : ℝ) ^ n by positivity)
  refine hR.trans (add_le_add le_rfl ?_)
  push_cast at hmul ⊢
  convert hmul using 1
  ring

end
end CCDN
