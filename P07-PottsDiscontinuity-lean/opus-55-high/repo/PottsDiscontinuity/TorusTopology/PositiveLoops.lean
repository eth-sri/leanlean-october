module

public import PottsDiscontinuity.TorusTopology.ClusterVerticalValues

/-! U counts positive winding with multiplicity. Positive-winding loops belong
to different original primal clusters, by the degree-two conservation law. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
open scoped Classical
variable {N M : ℕ}
noncomputable section

section
variable (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M)
/-- The loops with strictly positive signed vertical winding. -/
def positiveVerticalLoops  :
    Finset (Loop hN hM (rcSmoothing A)) :=
  univ.filter fun q => 0 < loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q

/-- The phase slots of all positive loops, with their actual winding multiplicity. -/
abbrev VerticalPhaseIndex  :=
  Σ q : (positiveVerticalLoops hN hM j A),
    Fin ((loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q.val).toNat)

theorem sum_vertical_winding_zero  :
    (∑ q : Loop hN hM (rcSmoothing A),
      loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q) = 0 := by
  rw [← Finset.sum_fiberwise univ (loopPrimalCluster hN hM A)
    (fun q => loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q)]
  simp only [sum_vertical_winding_at_cluster_zero,Finset.sum_const_zero]

/-- Positive winding, summed with multiplicity, is exactly U. -/
theorem sum_positive_vertical_winding_eq_U
     :
    (∑ q ∈ positiveVerticalLoops hN hM j A,
      (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).toNat) =
        rcVerticalWinding hN hM j A := by
  have hid (z : ℤ) : (z.natAbs : ℤ)+z = 2*(z.toNat : ℤ) := by
    omega
  have hs := Finset.sum_congr (s₁ := (univ : Finset (Loop hN hM (rcSmoothing A)))) rfl
    (fun q _ => hid (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q))
  rw [Finset.sum_add_distrib,sum_vertical_winding_zero,add_zero,← Finset.mul_sum] at hs
  have hnat : verticalMass _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j =
      2 * ∑ q : Loop hN hM (rcSmoothing A),
        (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).toNat := by
    exact_mod_cast hs
  have hU := two_mul_verticalWindingCount hN (checkerArrows N M) (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A)) j
  change 2 * rcVerticalWinding hN hM j A = _ at hU
  unfold positiveVerticalLoops
  rw [Finset.sum_filter]
  grind

/-- The number of phase slots is U, including all multiple windings. -/
theorem card_verticalPhaseIndex  :
    Fintype.card (VerticalPhaseIndex hN hM j A) = rcVerticalWinding hN hM j A := by
  simp
  exact (Finset.sum_coe_sort (positiveVerticalLoops hN hM j A)
    (fun q => (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).toNat)).trans
      (sum_positive_vertical_winding_eq_U hN hM j A)
end

section
variable (hN : Even N) (hM : Even M)
theorem width_pos_of_loop (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A)) : 0 < N := by
  induction q using Quotient.inductionOn with
  | h d => grind

/-- Distinct positive-winding loops are incident to distinct primal clusters. -/
theorem positive_vertical_loops_primalCluster_injective
    (j : Fin M) (A : RCConfig N M) :
    Function.Injective (fun q : positiveVerticalLoops hN hM j A => loopPrimalCluster hN hM A q.val) := by
  intro q r hqr
  by_contra hne
  have hq := (Finset.mem_filter.1 q.property).2
  have hr := (Finset.mem_filter.1 r.property).2
  let c := loopPrimalCluster hN hM A q.val
  let S := (univ : Finset (Loop hN hM (rcSmoothing A))).filter fun t =>
    loopPrimalCluster hN hM A t=c ∧
      loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j t ≠ 0
  have hsub : S ⊆ (windingLoopSet hN hM ⟨0,width_pos_of_loop hN hM A q.val⟩ j A).filter
      (fun t => loopPrimalCluster hN hM A t=c) := by
    grind [windingLoopSet]
  have hcard := (Finset.card_le_card hsub).trans
    (windingLoops_per_primalCluster_le_two hN hM ⟨0,width_pos_of_loop hN hM A q.val⟩ j A c)
  have hpair : ({q.val,r.val} : Finset (Loop hN hM (rcSmoothing A))) ⊆ S := by
    grind
  have hc : ({q.val,r.val} : Finset (Loop hN hM (rcSmoothing A))).card=2 := by simp_all
  have he := (Finset.eq_of_subset_of_card_le hpair (by omega)).symm
  have hsum : ∑ t ∈ S,
      loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j t = 0 := by
    have hS : S = (univ.filter fun t => loopPrimalCluster hN hM A t=c).filter
        (fun t => loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j t ≠ 0) := by
      grind
    rw [hS,Finset.sum_filter_ne_zero]
    exact sum_vertical_winding_at_cluster_zero hN hM j A c
  grind
end

end
end PottsDiscontinuity.TorusTopology
