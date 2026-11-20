module

public import PottsDiscontinuity.TorusLoops.WindingClusterCount
public import PottsDiscontinuity.TorusTopology.ClusterIntegralWinding

/-! The two possible nonzero vertical boundary values of one primal cluster.
Conservation and the proved incidence-degree bound suffice; no assertion that
these values are ±1 is made. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
open scoped Classical
variable {N M : ℕ}
noncomputable section

/-- Signed vertical winding is conserved at each original primal cluster. -/
theorem sum_vertical_winding_at_cluster_zero
    (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) :
    (∑ q with loopPrimalCluster q = c,
      loopVertical j q) = 0 := by
  have he := loopDisplacementY_primal_sum hN hM c
  simp only [loopDisplacementY,loop_vertical_displacement _ j,
    Int.cast_mul,Int.cast_natCast] at he
  rw [← Finset.mul_sum] at he
  have hn : (M : ℚ) ≠ 0 := by exact_mod_cast (Fin.pos j).ne'
  have hs := (mul_eq_zero.1 he).resolve_left hn
  exact_mod_cast hs

lemma values_of_support_card_le_two {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℤ) (hs : (S.filter fun x => f x ≠ 0).card ≤ 2)
    (hsum : ∑ x ∈ S, f x = 0) (q : α) (hq : q ∈ S) (hfq : f q ≠ 0) :
    ∀ r ∈ S, f r = 0 ∨ f r = f q ∨ f r = -f q := by
  intro r hr
  by_cases hfr : f r = 0
  · exact Or.inl hfr
  by_cases heq : q = r
  · grind
  have hp : ({q,r} : Finset α) ⊆ S.filter fun x => f x ≠ 0 := by
    grind
  have hc : ({q,r} : Finset α).card = 2 := by grind
  have he :=
    (Finset.eq_of_subset_of_card_le hp (by omega)).symm
  have hsum' : ∑ x ∈ S.filter (fun x => f x ≠ 0), f x = 0 := by
    grind [Finset.sum_filter_ne_zero]
  grind

variable (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A)) (hq : loopVertical j q ≠ 0)
include i hq

/-- All nonzero vertical loop windings at a cluster are the same up to sign.
Their common absolute value may exceed one, as required for helical classes. -/
theorem vertical_winding_values_at_cluster :
    ∀ r : Loop hN hM (rcSmoothing A), loopPrimalCluster r = loopPrimalCluster q →
      loopVertical j r = 0 ∨
      loopVertical j r =
        loopVertical j q ∨
      loopVertical j r =
        -loopVertical j q := by
  let c := loopPrimalCluster q
  let S := univ.filter fun r => loopPrimalCluster r = c
  let f := fun r : Loop hN hM (rcSmoothing A) =>
    loopVertical j r
  have hcard : (S.filter fun r => f r ≠ 0).card ≤ 2 := by
    apply (Finset.card_le_card ?_).trans (windingLoops_per_primalCluster_le_two hN hM i j A c)
    intro r hr
    obtain ⟨hrS,hrf⟩ := Finset.mem_filter.1 hr
    refine Finset.mem_filter.2 ⟨?_,(Finset.mem_filter.1 hrS).2⟩
    simp only [windingLoopSet,Finset.mem_filter,Finset.mem_univ,true_and]
    exact Or.inl hrf
  have hsum := sum_vertical_winding_at_cluster_zero hN hM j A c
  intro r hr
  exact values_of_support_card_le_two S f hcard hsum q (by grind) hq r (by grind)

/-- The winding of a vertically winding boundary loop divides the winding of
every integral conserved chain supported in its primal cluster. -/
theorem incident_vertical_winding_divides_integral_cycle
    (f : diamondCycleSpace hN hM A)
    (hs : SupportedOnDiamondCluster (loopPrimalCluster q) f)
    (hint : ∀ e : OpenDiamondEdge A, ∃ z : ℤ, f.val e = z) :
    ∃ z : ℤ, diamondWindingY f.val =
      ((loopVertical j q * z : ℤ) : ℚ) := by
  apply windingY_multiple_of_incident_loop_windings hN hM (Fin.pos j) j A _ ?_ f
    (all_cycles_mem_boundary_of_vertical_loop hN hM (Fin.pos i) (Fin.pos j) j A q hq f) hs hint
  intro r hr
  rcases vertical_winding_values_at_cluster hN hM i j A q hq r hr with h | h | h
  · simp [h]
  · rw [h]
  · simp [h]

end
end PottsDiscontinuity.TorusTopology
