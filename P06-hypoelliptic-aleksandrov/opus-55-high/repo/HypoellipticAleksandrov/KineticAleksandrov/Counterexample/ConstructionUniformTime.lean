module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionJointSource

/-! # Uniform bounds for the time representative on compact time intervals -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set HypoellipticAleksandrov.Parabolic

/-- The time representative is bounded globally in space, uniformly over compact time. -/
theorem construction_extendedTimeJet_uniform_bound {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (r mu R a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ q,
      |constructionExtendedTimeJet h r mu R t q| ≤ C := by
  let K := Icc a b ×ˢ {q | profileFunction h q ≤ 1}
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_profile_unit_sublevel ha h)
  obtain ⟨C, hC, hb⟩ := construction_compact_scalar_bound K hK _
    (construction_rawTimeJet_joint_continuous h r mu R)
  refine ⟨C, hC, fun t ht q => ?_⟩
  by_cases hp : profileFunction h q < 1
  · have hq : q ∈ {y | profileFunction h y < 1} := hp
    rw [constructionExtendedTimeJet, indicator_of_mem hq]
    exact hb (t, q) ⟨ht, hp.le⟩
  · have hq : q ∉ {y | profileFunction h y < 1} := hp
    rw [constructionExtendedTimeJet, indicator_of_notMem hq, abs_zero]
    exact hC

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
