module

public import PottsDiscontinuity.Duality.WiredDomainComparison
public import PottsDiscontinuity.FK.BoxLimits
public import PottsDiscontinuity.Infra.CylinderUniqueness

/-! Wired limits along finite domains squeezed between consecutive square boxes. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK MeasureTheory Filter Topology
noncomputable section

/-- No new infinite-volume law is introduced by a one-layer enlargement of boxes. -/
theorem wiredDomainProbabilityMeasure_tendsto_of_box_sandwich
    {θ : Parameters} (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    {S : ℕ → Finset LatticeVertex}
    (hinner : ∀ n, latticeBox (0, 0) n ⊆ S n)
    (houter : ∀ n, S n ⊆ latticeBox (0, 0) (n + 1)) :
    Tendsto (fun n => wiredDomainProbabilityMeasure θ (S n)) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  obtain ⟨ν, hν⟩ := wiredBoxProbabilityMeasure_exists_limit θ
  have heq := rc_limit_unique hμ
    (isRCInfiniteVolumeLimit_of_wiredBox_tendsto hν)
  have heq' : (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration) = ν :=
    ProbabilityMeasure.toMeasure_injective heq
  rw [heq']
  apply cylinderCoordinates_embedding.tendsto_nhds_iff.2
  apply tendsto_pi_nhds.2
  intro F
  have hconv := LatticeConfiguration.tendsto_allOpen_of_weak hν F
  have hconv' := hconv.comp (tendsto_add_atTop_nat 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hconv' hconv
  · intro n
    simp only [Function.comp_apply, cylinderProbabilityCoordinates]
    apply ENNReal.coe_le_coe.1
    simpa only [Function.comp_apply, cylinderProbabilityCoordinates,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      wiredDomainProbabilityMeasure_box] using
      wiredDomainProbabilityMeasure_allOpen_antitone θ (houter n) F
  · intro n
    simp only [Function.comp_apply, cylinderProbabilityCoordinates]
    apply ENNReal.coe_le_coe.1
    simpa only [Function.comp_apply, cylinderProbabilityCoordinates,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      wiredDomainProbabilityMeasure_box] using
      wiredDomainProbabilityMeasure_allOpen_antitone θ (hinner n) F

end
end PottsDiscontinuity.Duality
