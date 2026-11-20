/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Surface.ResidueLevels
public import CCDN.Surface.CurveCrossing
import CCDN.ForMathlib.MvPolynomial

@[expose] public section
namespace CCDN
noncomputable section
open Finset MvPolynomial

namespace SurfaceWindow
variable {N : ℕ} {B A : ℝ} (W : SurfaceWindow N B) {f : IntegerPolynomial 3}
    (F : SurfaceCongruenceFamily f B A) (S : Finset (Ideal (CoordinatePolynomial 3)))

open Classical in
/-- A parent auxiliary contains a curve on the surface; the child cuts it properly. -/
def crossing (R : W.nodes) (p : R.val) (r : SmoothAffineResidueFamily f R.val) : Set (RatPoint 3) :=
  let g := W.equation F (W.parent R p) (r.restrict (erase_subset p.val _))
  let h := W.equation F R r
  ⋃ I ∈ (S.filter (g ∈ ·)).filter (h ∉ ·), idealZeroLocus I ∩ zeroLocus h

abbrev residual := ⋃ (R : W.nodes) (p : R.val) (r : SmoothAffineResidueFamily f R.val), W.crossing F S R p r

variable (δ : Ideal (CoordinatePolynomial 3) → ℕ) (hS : ∀ I ∈ S, IsSurfaceCurve (rationalEquation f) I (δ I))
    (hir : Irreducible (rationalEquation f)) (hd : 5 ≤ f.totalDegree) (hB : 1 ≤ B) (hA : 0 ≤ A)

include hS hir hd hB hA in
private theorem count_edge (R : W.nodes) (p : R.val) :
    (count (⋃ r : SmoothAffineResidueFamily f R.val, W.crossing F S R p r) B : ℝ) ≤
      residueCost f.totalDegree N * f.totalDegree * (levelCost N A * boxLog B)^2 * windowUnit B^19 := by
  classical
  let (q : R.val) : NeZero q.val := ⟨(W.prime R q.val q.2).ne_zero⟩
  let : Fintype (SmoothAffineResidueFamily f R.val) := Pi.instFintype
  let Y := windowUnit B
  let k := R.val.card
  let D := levelCost N A * boxLog B
  have hy := windowUnit_one_le hB
  have hD : 0 ≤ D := by have := boxLog_one_le hB; dsimp only [D,levelCost]; positivity
  have he (r) : (count (W.crossing F S R p r) B:ℝ) ≤ f.totalDegree*(D*Y^(9-(k-1)))*(D*Y^(9-k)) := by
    let g := W.equation F (W.parent R p) (r.restrict (erase_subset p.val _))
    let h := W.equation F R r
    have hc : count (W.crossing F S R p r) B ≤ (rationalEquation f).totalDegree * g.totalDegree * h.totalDegree :=
      surface_curve_crossing_count_le _ g h hir (F.proper _ _ _) (S.filter (g ∈ ·)) δ (by grind) B
    rw [rational_map_totalDegree] at hc
    calc _ ≤ (f.totalDegree:ℝ)*g.totalDegree*h.totalDegree := by exact_mod_cast hc
         _ ≤ _ := by
           gcongr
           · simpa only [g,parent,node,card_erase_of_mem p.property] using W.degree_at_node F hB hA hd (W.parent R p) (r.restrict (erase_subset p.val _))
           · exact W.degree_at_node F hB hA hd R r
  have heq : (Y^k)^2 * Y^(9-(k-1)) * Y^(9-k) = Y^19 := by
    rw [← pow_mul,← pow_add,← pow_add]; congr 1
    have : 0 < k := card_pos.mpr ⟨_,p.2⟩
    have : k ≤ 9 := W.depth R
    omega
  calc _ ≤ _ := count_iUnion_bound _ B he
       _ ≤ residueCost f.totalDegree N*(Y^k)^2*(f.totalDegree*(D*Y^(9-(k-1)))*(D*Y^(9-k))) := by
            gcongr; exact W.residue_card hB (by omega) R
       _ = _ := by change _ = _*_*D^2*Y^19; rw [← heq]; ring

abbrev residualCost (N d : ℕ) (A : ℝ) := 2^N * 9 * residueCost d N * d * levelCost N A ^ 2

include hS hir hd hB hA in
lemma residual_bound : (count (W.residual F S) B : ℝ) ≤ residualCost N f.totalDegree A * (windowUnit B^19 * boxLog B^2) := by
  let C := residueCost f.totalDegree N * f.totalDegree * (levelCost N A * boxLog B)^2 * windowUnit B^19
  have hc : 0 ≤ C := by unfold C residueCost; positivity
  have hR (R : W.nodes) : (count (⋃ (p : R.val) (r : SmoothAffineResidueFamily f R.val), W.crossing F S R p r) B:ℝ) ≤ 9*C := by
    apply (count_iUnion_bound _ _ (W.count_edge F S δ hS hir hd hB hA R)).trans
    simp only [Nat.card_eq_fintype_card,Fintype.card_coe]; gcongr; exact_mod_cast W.depth R
  have hcard : W.nodes.card ≤ 2^N := (card_le_card (filter_subset ..)).trans_eq (by rw [card_powerset,W.card])
  calc _ ≤ _ := count_iUnion_bound _ _ hR
       _ ≤ (2:ℝ)^N*(9*C) := by simp only [Nat.card_eq_fintype_card,Fintype.card_coe]; gcongr; exact_mod_cast hcard
       _ = _ := by unfold C residualCost; ring

end SurfaceWindow
end
end CCDN
