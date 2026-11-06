module

public import PottsDiscontinuity.Torus.DiamondIntersectionLocality
public import PottsDiscontinuity.Torus.RibbonHandleIntersection

/-!
# Winding nets and the torus Euler relation

A net is a single actual open cluster carrying two conserved rational one-cycles
with independent lifted winding classes. The full cellular homology calculation
identifies those classes with the two displacement coordinates. The cellular
intersection criterion and cluster localization prove the net/handle equivalence.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The determinant of the two lifted displacement classes. -/
def diamondWindingDeterminant (A : RCConfig N M) (f g : OpenDiamondEdge A → ℚ) : ℚ :=
  diamondHorizontalDisplacement A f * diamondVerticalDisplacement A g -
    diamondVerticalDisplacement A f * diamondHorizontalDisplacement A g

/-- One actual cluster carries two independent torus winding classes.
Rational conserved one-cycles are the cellular homology model; the support premise
requires both classes to be carried by the same connected cluster. -/
def HasWindingNet (hN : Even N) (hM : Even M) (A : RCConfig N M) : Prop :=
  ∃ c : (diamondOpenGraph hN hM true A).ConnectedComponent,
    ∃ f g : diamondCycleSpace hN hM A,
      SupportedOnDiamondCluster hN hM A c f ∧ SupportedOnDiamondCluster hN hM A c g ∧
        diamondWindingDeterminant A f.val g.val ≠ 0

section
variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)
include hNp hMp
theorem ribbonIntersection_eq_zero_iff_windingDeterminant_zero (f g : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM A f g = 0 ↔ diamondWindingDeterminant A f.val g.val = 0 := by
  have he := ribbonIntersection_mul_area_subgraph hN hM hNp hMp A f g
  have hn : (N * M : ℚ) ≠ 0 := by positivity
  grind [ribbonIntersection, diamondWindingDeterminant]

theorem ribbonHandleCount_one_iff_net_of_pos  :
    ribbonHandleCount hN hM A = 1 ↔ HasWindingNet hN hM A := by
  constructor
  · intro hh
    obtain ⟨f, g, hfg⟩ := (ribbonHandleCount_one_iff_intersection_nonzero hN hM A).mp hh
    obtain ⟨c, hc⟩ := exists_cluster_intersection_nonzero hN hM A f g hfg
    refine ⟨c, diamondClusterCycle hN hM A c f, diamondClusterCycle hN hM A c g,
      diamondClusterCycle_supported hN hM A c f, diamondClusterCycle_supported hN hM A c g, ?_⟩
    simp_all [ribbonIntersection_eq_zero_iff_windingDeterminant_zero]
  · rintro ⟨c, f, g, _, _, hfg⟩
    apply (ribbonHandleCount_one_iff_intersection_nonzero hN hM A).mpr
    exact ⟨f, g, fun he => hfg ((ribbonIntersection_eq_zero_iff_windingDeterminant_zero
      hN hM hNp hMp A f g).mp he)⟩
end

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
/-- The genus-one component criterion is exactly the winding-defined net condition. -/
theorem ribbonHandleCount_one_iff_net  :
    ribbonHandleCount hN hM A = 1 ↔ HasWindingNet hN hM A := by
  by_cases hn : N = 0
  · subst N
    have ha : A = closedRCConfig 0 M := by funext v; grind
    have hh : ribbonHandleCount hN hM A = 0 := by rw [ha, ribbonHandleCount_closed]
    simp_all [HasWindingNet]
  · by_cases hm : M = 0
    · subst M
      have hh : ribbonHandleCount hN hM A = 0 := by rfl
      simp_all [HasWindingNet]
    grind [ribbonHandleCount_one_iff_net_of_pos]

/-- The paper's net indicator, defined through the actual cluster winding condition. -/
noncomputable def rcNetIndicator  : ℕ := by
  classical
  exact if HasWindingNet hN hM A then 1 else 0

theorem ribbonHandleCount_eq_netIndicator  :
    ribbonHandleCount hN hM A = rcNetIndicator hN hM A := by
  by_cases hn : HasWindingNet hN hM A
  · simp_all [ribbonHandleCount_one_iff_net, rcNetIndicator]
  · have hh := fun h => hn ((ribbonHandleCount_one_iff_net hN hM A).mp h)
    have hb := ribbonHandleCount_le_one hN hM A
    grind [ribbonHandleCount, rcNetIndicator]

/-- The torus Euler/net identity, using actual cluster, boundary-loop and open-edge counts. -/
theorem euler_netIndicator  :
    2 * clusterCount hN hM true A + openCount A =
      rcLoopCount hN hM A + N * M / 2 + 2 * rcNetIndicator hN hM A := by
  rw [← ribbonHandleCount_eq_netIndicator]
  exact euler_ribbonHandleCount hN hM A
end

end PottsDiscontinuity.Torus
