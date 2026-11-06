/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.ProjectivePlaneResidueDeterminant
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Determinant.PlaneMultiplicitySmooth
import CCDN.Determinant.PlaneSingularities

/-! Singular projective residue classes are counted in their selected affine
charts. The correction is polynomial in the degree and does not change the
leading finite-field point-count term. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The singular correction does not multiply the leading point-count term. -/
theorem projectivePlaneTotalMultiplicity_le_card_add_correction {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hchar : d < p) :
    projectivePlaneTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectivePlaneResidue f p) + 3 * d ^ 2 * (d - 1) := by
  classical
  have hnorm (r : ProjectiveResidueSpace 2 p) :
      (Fin.cons 1 (fun j => (projectiveResidueChartLift r j : ZMod p))) ∘
        Equiv.swap 0 (projectiveResiduePivot r) =
          (r.rep (projectiveResiduePivot r))⁻¹ • r.rep := by
    rw [show Fin.cons 1 (fun j => (projectiveResidueChartLift r j : ZMod p)) =
        (r.rep (projectiveResiduePivot r))⁻¹ • (r.rep ∘ Equiv.swap 0 (projectiveResiduePivot r)) from
      funext (Fin.cases (by simp [projectiveResiduePivot_ne_zero])
        fun _ => by simp [cast_projectiveResidueChartLift, div_eq_mul_inv, mul_comm])]
    funext j; simp
  let S := Finset.univ.filter fun r : ProjectivePlaneResidue f p =>
    2 ≤ projectivePlaneResidueMultiplicity f hf hir.ne_zero r
  let T (k : Fin 3) := S.filter fun r => projectiveResiduePivot r.val = k
  have hk {k : Fin 3} (r : T k) : projectiveResiduePivot r.val.val = k :=
    (Finset.mem_filter.mp r.property).2
  have hT (k : Fin 3) : (T k).card ≤ d * (d - 1) := by
    let q0 := rename (Equiv.swap 0 k) (map (Int.castRingHom (ZMod p)) f)
    have hq0 : q0.IsHomogeneous d := (hf.map _).rename_isHomogeneous
    have hqi : Irreducible q0 :=
      (MulEquiv.irreducible_iff (f := renameEquiv (ZMod p) (Equiv.swap 0 k))).mpr hir
    have hX := variable_not_dvd_irreducible_homogeneous q0 hq0 hqi hd 0
    let q := map (Int.castRingHom (ZMod p)) (projectivePlaneChart k f)
    have heq : q = affineChart 2 q0 := by
      change map _ (affineChart 2 (rename (Equiv.swap 0 k) f)) = _
      rw [← affineChart_map, map_rename]
    have hq_ir : Irreducible q := heq ▸ affineChart_irreducible_of_not_variable_dvd q0 hq0 hqi hX
    have hq_deg : q.totalDegree = d := heq ▸ affineChart_degree_of_not_variable_dvd q0 hq0 hX
    let z : T k → Fin 2 → ZMod p := fun r j => (projectiveResidueChartLift r.val.val j : ZMod p)
    have hz : Function.Injective z := by
      intro r t he
      refine Subtype.ext (Subtype.ext ?_)
      have hkp := (hk r).trans (hk t).symm
      have hn : (r.val.val.rep (projectiveResiduePivot r.val.val))⁻¹ • r.val.val.rep =
          (t.val.val.rep (projectiveResiduePivot t.val.val))⁻¹ • t.val.val.rep := by
        rw [← hnorm, ← hnorm, hkp,
          show (fun j => (projectiveResidueChartLift r.val.val j : ZMod p)) =
            fun j => (projectiveResidueChartLift t.val.val j : ZMod p) from he]
      have hs : (r.val.val.rep (projectiveResiduePivot r.val.val) /
          t.val.val.rep (projectiveResiduePivot t.val.val)) • t.val.val.rep = r.val.val.rep := by
        simpa only [smul_smul, mul_inv_cancel₀ (projectiveResiduePivot_ne_zero r.val.val),
          one_smul, div_eq_mul_inv] using
          (congrArg (fun v : Fin 3 → ZMod p => r.val.val.rep (projectiveResiduePivot r.val.val) • v) hn).symm
      rw [← r.val.val.mk_rep, ← t.val.val.mk_rep, Projectivization.mk_eq_mk_iff']
      exact ⟨_, hs⟩
    have hzero (r : T k) : eval (z r) q = 0 := by
      have h := projectiveResidueChartLift_zero f hf r.val.val r.val.property
      rw [hk r] at h
      simpa only [q, z, eval_map] using h
    have hsing (r : T k) (j : Fin 2) : eval (z r) (pderiv j q) = 0 := by
      have hp := (projectivePlaneResidueMultiplicity_spec f hf hir.ne_zero r.val).2.2.1
      change map (Int.castRingHom (ZMod p)) (originShift (projectiveResidueChartLift r.val.val)
        (projectivePlaneChart (projectiveResiduePivot r.val.val) f)) ∈ _ at hp
      rw [originShift_map] at hp
      simpa only [q, z, Int.coe_castRingHom, hk r] using singular_of_origin_order_ge_two _ _
        (Finset.mem_filter.mp (Finset.mem_filter.mp r.property).1).2 hp j
    simpa only [Fintype.card_coe, q, hq_deg] using
      plane_singular_points_card_le (p := p) q hq_ir (by rw [hq_deg]; omega)
        (by rwa [hq_deg]) z hz hzero hsing
  have hS : S.card ≤ 3 * d * (d - 1) := by
    have hsum : ∑ k : Fin 3, (T k).card = S.card := by
      simp only [T, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]; simp
    have h := Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hT k
    rw [hsum] at h
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc] using h
  have hpoint (r : ProjectivePlaneResidue f p) :
      projectivePlaneResidueMultiplicity f hf hir.ne_zero r ≤ 1 + if r ∈ S then d else 0 := by
    have h := (projectivePlaneResidueMultiplicity_spec f hf hir.ne_zero r).2.1
    by_cases hr : r ∈ S
    · rw [ite_eq_left hr]; omega
    · rw [ite_eq_right hr]
      have hh : ¬ 2 ≤ projectivePlaneResidueMultiplicity f hf hir.ne_zero r := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hr
      omega
  have hsum : projectivePlaneTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectivePlaneResidue f p) + S.card * d :=
    (Finset.sum_le_sum fun r _ => hpoint r).trans_eq (by simp [Finset.sum_add_distrib])
  nlinarith [Nat.mul_le_mul_right d hS]

end
end CCDN
