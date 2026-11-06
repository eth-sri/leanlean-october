module
public import Mathlib

public import PottsDiscontinuity.FK.LimitTranslation

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCInfinite

open PottsDiscontinuity.FK

noncomputable section

/-- Every frozen free limit is also the weak limit along each nested exhaustive
sequence of translated square boxes. -/
theorem free_box_exhaustion
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (c : ℕ → LatticeVertex) (r : ℕ → ℕ)
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    (hexhaust : ∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) :
    Tendsto (fun n => boxProbabilityMeasure θ (c n) (r n)) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  obtain ⟨ν₀, hν₀, _⟩ := freeBoxLimit_existsUnique (q := θ)
  
  
  
  
  
  change Tendsto (fun n => boxProbabilityMeasure θ (c n) (r n)) atTop (𝓝 ν)
  rw [ ProbabilityMeasure.toMeasure_injective (PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0
                                                   ν.toMeasure ν₀.toMeasure  hμ  (isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν₀ (hν₀ (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested
                                                                                                                                         origin_latticeBox_exhaustive))) ]
  exact hν₀ c r hnest hexhaust

/-- Every frozen wired limit is also the weak limit along each nested exhaustive
sequence of translated square boxes. -/
theorem wired_box_exhaustion
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (c : ℕ → LatticeVertex) (r : ℕ → ℕ)
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    (hexhaust : ∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) :
    Tendsto (fun n => wiredBoxProbabilityMeasure θ (c n) (r n)) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  obtain ⟨ν₀, hν₀, _⟩ := wiredBoxLimit_existsUnique θ
  
  
  
  
  
  change Tendsto (fun n => wiredBoxProbabilityMeasure θ (c n) (r n)) atTop (𝓝 ν)
  rw [ ProbabilityMeasure.toMeasure_injective (PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 1
                                                   ν.toMeasure ν₀.toMeasure  hμ  (isRCInfiniteVolumeLimit_of_wiredBox_tendsto θ ν₀ (hν₀ (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested
                                                                                                                                          origin_latticeBox_exhaustive))) ]
  exact hν₀ c r hnest hexhaust

/-- Translation invariance for every frozen limit, re-exported in the
infinite-volume random-cluster namespace. -/
theorem translation_invariant
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit p q i μ)
    (a : LatticeVertex) :
    μ.map (latticeConfigurationTranslate a) = μ :=
  PottsDiscontinuity.FK.isRCInfiniteVolumeLimit_translation_invariant
    p q hq i μ hμ a

end
end PottsDiscontinuity.RCInfinite
