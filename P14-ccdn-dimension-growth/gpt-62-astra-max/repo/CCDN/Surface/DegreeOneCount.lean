/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Surface.CurveComponents
public import CCDN.Algebra.PolynomialPredicates
import CCDN.Plane.DegreeOneAffineLine
import CCDN.Surface.LineDirections
import CCDN.Surface.CurveCrossing
import CCDN.Surface.DirectionalDerivative
import CCDN.Surface.DirectionSum
import CCDN.Surface.TopFormBadPrimes
import CCDN.Algebra.FieldMapIrreducible
import CCDN.ForMathlib.MvPolynomial

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- Weighted finite sums with a uniform bound on the cardinality of each
fiber. No injectivity of the indexing map is required. -/
private theorem sum_comp_le_fiber_card_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (p : α → β) (w : β → ℝ) (M : ℝ)
    (hw : ∀ q ∈ s.image p, 0 ≤ w q)
    (hfiber : ∀ q ∈ s.image p, ((s.filter (fun x => p x = q)).card : ℝ) ≤ M) :
    ∑ x ∈ s, w (p x) ≤ M * ∑ q ∈ s.image p, w q := by
  classical
  calc
    _ = ∑ q ∈ s.image p, ∑ x ∈ s.filter (fun x => p x = q), w (p x) :=
      (Finset.sum_fiberwise_of_maps_to (by grind) _).symm
    _ ≤ ∑ q ∈ s.image p, M * w q := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        _ = ∑ _x ∈ s.filter (fun x => p x = q), w q :=
          Finset.sum_congr rfl (by grind)
        _ = ((s.filter (fun x => p x = q)).card) * w q := by simp
        _ ≤ M * w q := by bound
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Group the *prime curves* by direction. A fiber lies in the polar section,
so its cardinality is bounded by the degree budget for that section. -/
theorem surface_degree_one_component_contribution : ∃ C : ℝ, 0 < C ∧ ∀ f : IntegerPolynomial 3,
    HasAbsIrreducibleTopForm f → 3 ≤ f.totalDegree → ∀ B : ℝ, 0 ≤ B →
    ∀ S : Finset (Ideal (CoordinatePolynomial 3)), (∀ P ∈ S, IsSurfaceCurve (rationalEquation f) P 1) →
    (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤ C*(f.totalDegree:ℝ)^6*B + S.card := by
  classical
  obtain ⟨K,hK,weight⟩ := integer_projective_plane_reciprocal_height_sum
  refine ⟨8*K,by positivity,?_⟩
  intro f top hd B hB S hS
  let F := rationalEquation f
  have hir := rational_irreducible_of_charZero_map f (absolute_irreducible_of_top_homogeneousComponent_irreducible f top)
  let N (P : Ideal (CoordinatePolynomial 3)) := count (idealZeroLocus P) B
  let T := S.filter fun P => 1 < N P
  have data (P : T) : ∃ p : ProjectivePoint 2,
      p ∈ projectiveZeroLocus (rationalEquation (homogeneousComponent f.totalDegree f)) ∧
      (∃ a, idealZeroLocus P.val = rationalAffineLine a p.rep) ∧ (N P:ℝ) ≤ 8*B/p.mulHeight ∧
      ∀ g, idealZeroLocus P.val ⊆ zeroLocus g → g ∈ P.val := by
    obtain ⟨hPS,hN⟩ := mem_filter.mp P.2
    have H := hS _ hPS
    have := H.isPrime
    obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp hN
    obtain ⟨v,he,rad⟩ := degree_one_secant P.1 H.degree (mem_integralPoints.mp hx).2 (mem_integralPoints.mp hy).2 ((rationalPoint_injective 3).ne ne)
    obtain ⟨p,hp,hl,hc⟩ := line_direction_bound f (idealZeroLocus P.1) ⟨_,v,he⟩ (fun _ hz => hz _ H.mem) hB hN
    exact ⟨p,hp,hl,hc,fun g h => (rad g).mpr (he ▸ h)⟩
  choose p hp hl hN hr using data
  have hfiber (q : ProjectivePoint 2) (_ : q ∈ univ.image p) :
      ((univ.filter (fun i : T => p i = q)).card : ℝ) ≤ (f.totalDegree : ℝ)^2 := by
    let g := directionalDerivative q.rep F
    have hg : g.totalDegree ≤ f.totalDegree-1 := by simpa [g,F,rational_map_totalDegree] using directionalDerivative_totalDegree_le q.rep F
    have hfg : ¬ F ∣ g := fun h => by
      have := totalDegree_le_of_dvd_of_isDomain h (surface_directionalDerivative_ne_zero f top (by omega) _ q.rep_nonzero)
      rw [rational_map_totalDegree] at this; omega
    let U := univ.filter fun i : T => p i = q
    have hsum := surface_prime_curve_degree_sum_le F g hir hfg (U.image Subtype.val) (fun _ => 1) (by
      intro I hI
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hI
      have H := hS i (mem_filter.mp i.2).1
      refine ⟨H,hr i _ ?_⟩
      obtain ⟨a,he⟩ := hl i
      rw [(mem_filter.mp hi).2] at he
      rw [he]; exact rationalAffineLine_contained_directionalDerivative _ _ _ fun x hx => (he ▸ hx : x ∈ idealZeroLocus i.val) _ H.mem)
    simp [F,rational_map_totalDegree,card_image_of_injective _ Subtype.val_injective] at hsum
    change (U.card:ℝ) ≤ _
    exact_mod_cast hsum.trans (by nlinarith [Nat.sub_le f.totalDegree 1])
  have hw := weight f.totalDegree hd _ (homogeneousComponent_isHomogeneous _ _) top (univ.image p) (by intro q hq; obtain ⟨i,-,rfl⟩ := mem_image.mp hq; exact hp i)
  have hfib := sum_comp_le_fiber_card_mul univ p (fun q => 1/q.mulHeight) _ (by intros; positivity) hfiber
  have hgood : (∑ I ∈ T, (N I:ℝ)) ≤ 8*K*f.totalDegree^6*B := by
    rw [← sum_coe_sort]
    calc
      _ ≤ ∑ i : T, (8*B)*(1/(p i).mulHeight) := sum_le_sum fun i _ => (hN i).trans_eq (by ring)
      _ = (8*B)*∑ i : T, 1/(p i).mulHeight := (mul_sum ..).symm
      _ ≤ (8*B)*(f.totalDegree^2*(K*f.totalDegree^4)) := mul_le_mul_of_nonneg_left (hfib.trans (mul_le_mul_of_nonneg_left hw (by positivity))) (by positivity)
      _ = _ := by ring
  have hbad : ∑ I ∈ S.filter (fun I => ¬1 < N I), (N I:ℝ) ≤ S.card := by
    calc _ ≤ ∑ _ ∈ S.filter (fun I => ¬1 < N I), (1:ℝ) := sum_le_sum fun I h => by exact_mod_cast Nat.le_of_not_gt (mem_filter.mp h).2
         _ ≤ _ := by simpa using (card_le_card (filter_subset (fun I => ¬1 < N I) S))
  calc _ ≤ ∑ I ∈ S, (N I:ℝ) := by exact_mod_cast count_biUnion_finset_le S idealZeroLocus B
       _ ≤ _ := by rw [← sum_filter_add_sum_filter_not S (fun I => 1<N I)]; exact add_le_add hgood hbad

end
end CCDN
