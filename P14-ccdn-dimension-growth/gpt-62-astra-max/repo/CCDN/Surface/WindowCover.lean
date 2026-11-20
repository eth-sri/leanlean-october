/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Surface.ResidueEdges
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hypersurface.SingularHypersurfaceCount

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- On the subsets of `P`, a predicate false at the root and true at `P` changes across some deletion edge. -/
private lemma first_marked_subset (P : Finset ℕ) (marked : ∀ R ⊆ P, Prop)
    (h0 : ¬ marked ∅ (empty_subset _)) (hP : marked P (Subset.refl _)) :
    ∃ R, ∃ h : R ⊆ P, ∃ p ∈ R, marked R h ∧ ¬ marked (R.erase p) ((erase_subset p R).trans h) := by
  classical
  suffices ∀ R, ∀ h : R ⊆ P, marked R h → ∃ T, ∃ hT : T ⊆ P, ∃ p ∈ T, marked T hT ∧ ¬ marked (T.erase p) ((erase_subset p T).trans hT) by exact this P _ hP
  intro R
  induction R using Finset.induction_on with
  | empty => exact fun _ h => (h0 h).elim
  | insert p R hp ih =>
    intro h hm
    by_cases hr : marked R ((subset_insert ..).trans h)
    · exact ih _ hr
    · exact ⟨_,h,p,mem_insert_self ..,hm,by simpa [hp] using hr⟩

namespace SurfaceWindow
variable {N : ℕ} {A B : ℝ} {f : IntegerPolynomial 3} (W : SurfaceWindow N B)
    (F : SurfaceCongruenceFamily f B A) (S : Finset (Ideal (CoordinatePolynomial 3)))

lemma large_curve_mem_residual (hB : 1 ≤ B) (hA : 0 ≤ A) (hd : 5 ≤ f.totalDegree)
    (hir : Irreducible (rationalEquation f)) {I : Ideal (CoordinatePolynomial 3)} (hIS : I ∈ S)
    {e : ℕ} (hI : IsSurfaceCurve (rationalEquation f) I e) (hi : rationalEquation F.initial ∈ I)
    (large : f.totalDegree * levelCost N A * boxLog B < e)
    (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0) (hxI : rationalPoint x ∈ idealZeroLocus I)
    (P : Finset ℕ) (hP : P ⊆ W.primes) (hk : P.card = 9)
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p)) (pderiv j (residueEquation p f)) ≠ 0) : rationalPoint x ∈ W.residual F S := by
  classical
  let r := smoothResidueFamilyOfPoint x hxf P hs
  let stage (T) (h : T ⊆ P) := W.node T (h.trans hP) ((card_le_card h).trans hk.le)
  let g (T) (h : T ⊆ P) := W.equation F (stage T h) (r.restrict h)
  have root : g ∅ (empty_subset _) ∈ I := by
    change rationalEquation (F.auxiliary ∅ _ _) ∈ I
    rwa [F.initial_eq]
  have terminal (hm : g P (Subset.refl _) ∈ I) : False := by
    let T := stage P (Subset.refl _)
    have hdeg := W.degree_at_node F hB hA hd T (r.restrict (Subset.refl _))
    change ((g P _).totalDegree:ℝ) ≤ _*_*_^ (9-P.card) at hdeg
    simp only [hk,Nat.sub_self,pow_zero,mul_one] at hdeg
    have hc := surface_prime_curve_degree_sum_le (rationalEquation f) (g P (Subset.refl _)) hir (F.proper _ _ _) {I} (fun _ => e) (by simpa using And.intro hI hm)
    rw [sum_singleton,rational_map_totalDegree] at hc
    have h' : (e:ℝ) ≤ (f.totalDegree:ℝ)*(g P (Subset.refl _)).totalDegree := by exact_mod_cast hc
    linarith [mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg (α:=ℝ) f.totalDegree)]
  obtain ⟨T,hT,p,hp,child,parent⟩ := first_marked_subset P (fun T h => g T h ∉ I) (not_not.mpr root) terminal
  simp only [residual,Set.mem_iUnion]
  refine ⟨stage T hT,⟨p,hp⟩,r.restrict hT,?_⟩
  simp only [crossing,Set.mem_iUnion]
  refine ⟨I,mem_filter.mpr ⟨mem_filter.mpr ⟨hIS,not_not.mp parent⟩,child⟩,hxI,?_⟩
  change eval (rationalPoint x) (rationalEquation _) = 0
  rw [eval_rationalPoint_map,Int.cast_eq_zero]
  exact F.point_vanishes x hx hxf T _ (fun q h => hs q (hT h))

end SurfaceWindow
end
end CCDN
