
import proofs.HordijkSteelThreshold.PeelingHistory
import proofs.HordijkSteelThreshold.CatalystPoolBlocks
import proofs.RAFEmergenceApprox.GenericHistory
import proofs.HordijkSteelThreshold.WordContourProbability
import proofs.HordijkSteelThreshold.WordEffectiveClosure




namespace HordijkSteelThreshold

open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

variable (p : I) (k : ℕ)

noncomputable def fixedPoolParameter   := σ (σ p^k)

theorem pool_column_map {X : Type*} [Fintype X] (p : I) (C : Finset X) :
    (RAFEmergenceApprox.Generic.colLaw X p).map (fun v => ∃ x ∈ C, v x) =
      ambientCoordLaw (fixedPoolParameter p C.card) := by
  apply probability_prop_eq_of_false
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton _)]
  have he : (fun v : X → Prop => ∃ x ∈ C, v x) ⁻¹' {False} =
      {v | ¬ ∃ x ∈ C, v x} := by  simp
  rw [he, RAFEmergenceApprox.Generic.closed_probability]
  simp [ambientCoordLaw, fixedPoolParameter, ← ENNReal.coe_pow]
  apply NNReal.eq
  simp

theorem catalystPool_statistic {X R : Type*} [Fintype X] [Fintype R]
    (p : R → I) (C : Finset X) (stat : Finset R → Prop) :
    RAFEmergenceApprox.Generic.law p {ω | stat (RAFEmergenceApprox.Generic.catalystActive ω C)} =
      (Measure.pi fun r => ambientCoordLaw (fixedPoolParameter (p r) C.card))
        {ω | stat (Finset.univ.filter ω)} := by
  simp_rw [← pool_column_map (C := C)]
  rw [← Measure.pi_map_pi (μ := fun r => RAFEmergenceApprox.Generic.colLaw X (p r))
    (f := fun _ v => ∃ x ∈ C, v x) (fun _ => (measurable_of_finite _).aemeasurable),
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  rfl

end HordijkSteelThreshold
