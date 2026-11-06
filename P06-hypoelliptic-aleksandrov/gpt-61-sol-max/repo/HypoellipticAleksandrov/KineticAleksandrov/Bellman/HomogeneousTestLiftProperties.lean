module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftScaling

/-! # The homogeneous-test-lift node with its literal operator chain rule -/

 public section


namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The actual radial integral is C² homogeneous with the required operator scaling. -/
theorem bellman_test_lift (alpha : ℝ) (_ha : 0 < alpha) (_ha1 : alpha < 1)
    (zeta : (ℝ × ℝ) → ℝ) (hz : ContDiffOn ℝ 2 zeta bellmanPuncturedSet)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
    IsBellmanHomogeneous alpha (lift alpha zeta) ∧
      ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet, ∀ b : ℝ,
        bellmanOperator b (fun z => zeta (bellmanPlaneDilation r z)) q =
          r ^ 2 * bellmanOperator b zeta (bellmanPlaneDilation r q) := (⟨⟨bellman_lift_contDiffOn alpha zeta hz hc hs, fun r hr q a => bellman_lift_scaling alpha zeta r hr q⟩,
  fun r hr q hq b => bellmanOperator_comp_dilation r hr zeta hz q hq b⟩)

end HypoellipticAleksandrov.KineticAleksandrov
