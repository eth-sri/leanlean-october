module

public import PottsDiscontinuity.FK.LimitTranslation

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCInfinite

open PottsDiscontinuity.FK

noncomputable section

variable (θ : Parameters) (μ : Measure LatticeConfiguration)

/-- Every frozen free limit is also the weak limit along each nested exhaustive
sequence of translated square boxes. -/
theorem free_box_exhaustion
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    {c : ℕ → LatticeVertex} {r : ℕ → ℕ}
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    (hexhaust : ∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) :
    Tendsto (fun n => boxProbabilityMeasure θ (c n) (r n)) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  obtain ⟨ν₀, hν₀, _⟩ := freeBoxLimit_existsUnique (q := θ)
  have hν₀origin :=
    hν₀ (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested
      origin_latticeBox_exhaustive
  have hRCν₀ :=
    isRCInfiniteVolumeLimit_of_freeBox_tendsto hν₀origin
  have hRCν : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 ν.toMeasure := hμ
  have hmeasure :=
    PottsDiscontinuity.rc_limit_unique hRCν hRCν₀
  have hprob := ProbabilityMeasure.toMeasure_injective hmeasure
  change Tendsto (fun n => boxProbabilityMeasure θ (c n) (r n)) atTop (𝓝 ν)
  rw [hprob]
  exact hν₀ c r hnest hexhaust

/-- Every frozen wired limit is also the weak limit along each nested exhaustive
sequence of translated square boxes. -/
theorem wired_box_exhaustion
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    {c : ℕ → LatticeVertex} {r : ℕ → ℕ}
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    (hexhaust : ∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) :
    Tendsto (fun n => wiredBoxProbabilityMeasure θ (c n) (r n)) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  obtain ⟨ν₀, hν₀, _⟩ := wiredBoxLimit_existsUnique θ
  have hν₀origin :=
    hν₀ (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested
      origin_latticeBox_exhaustive
  have hRCν₀ :=
    isRCInfiniteVolumeLimit_of_wiredBox_tendsto hν₀origin
  have hRCν : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 ν.toMeasure := hμ
  have hmeasure :=
    PottsDiscontinuity.rc_limit_unique hRCν hRCν₀
  have hprob := ProbabilityMeasure.toMeasure_injective hmeasure
  change Tendsto (fun n => wiredBoxProbabilityMeasure θ (c n) (r n)) atTop (𝓝 ν)
  rw [hprob]
  exact hν₀ c r hnest hexhaust


end
end PottsDiscontinuity.RCInfinite
