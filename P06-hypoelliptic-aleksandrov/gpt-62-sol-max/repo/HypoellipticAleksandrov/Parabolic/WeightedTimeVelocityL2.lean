module

public import HypoellipticAleksandrov.Parabolic.SmoothGradientTimeEnergy
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import Mathlib.Analysis.Calculus.Deriv.Support

/-! Bounded multipliers for the weighted weak energy identities. -/

@[expose] public section
noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy

private theorem memLp_top_compact_comp {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β] {a : β → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a) {p : α → β} (hp : Measurable p) :
    MemLp (a ∘ p) ∞ μ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous ha
  exact memLp_top_of_bound (ha.measurable.comp hp).aestronglyMeasurable C
    (ae_of_all _ fun z => hC (p z))

section
variable {d : ℕ} (S : Set (TimeVelocity d))

/-- A separated weight inherits essential boundedness from the compactly supported factors. -/
theorem separated_multiplier_memLp_top_restrict
    (a : ℝ → ℝ) (ha : Continuous a) (haCompact : HasCompactSupport a)
    (c : PDE.Vec d → ℝ) (hc : Continuous c) (hcCompact : HasCompactSupport c) :
    MemLp (fun z : TimeVelocity d => a z.1 * c z.2) ∞ (timeVelocityVolumeOn S) :=
  (memLp_top_compact_comp ha haCompact measurable_fst).mul'
    (memLp_top_compact_comp hc hcCompact measurable_snd)

theorem supportIndicator_memLp_top
    (η : PDE.Vec d → ℝ) {ζ : ℝ → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) :
    MemLp (fun z : TimeVelocity d => ζ z.1 * (tsupport η).indicator (fun _ => (1 : ℝ)) z.2)
      ∞ (timeVelocityVolumeOn S) := by
  apply (memLp_top_compact_comp hζ hζc measurable_fst).mul' (q := ∞)
  apply memLp_top_of_bound ((measurable_const.indicator (isClosed_tsupport η).measurableSet).comp
    measurable_snd).aestronglyMeasurable 1
  exact ae_of_all _ fun z => by by_cases hz : z.2 ∈ tsupport η <;> simp [hz]

/-- Boundedness of the cutoff weights in the spatial and temporal energy pairings. -/
theorem energy_weights_memLp_top
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) :
    (∀ k : Fin d, MemLp (fun z : TimeVelocity d =>
      (-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial k η z.2)) ∞ (timeVelocityVolumeOn S)) ∧
    MemLp (fun z : TimeVelocity d => (-1 : ℝ) * ζ z.1 * η z.2 ^ 2) ∞ (timeVelocityVolumeOn S) ∧
    MemLp (fun z : TimeVelocity d => ζ z.1 * η z.2 ^ 2) ∞ (timeVelocityVolumeOn S) ∧
    MemLp (fun z : TimeVelocity d => deriv ζ z.1 * η z.2 ^ 2) ∞ (timeVelocityVolumeOn S) := by
  have hηsq : HasCompactSupport (fun y => η y ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hηc.mul_right (f' := η)
  have hsq := separated_multiplier_memLp_top_restrict S ζ hζ.continuous hζc _
    (hη.continuous.pow 2) hηsq
  refine ⟨fun k => ?_, ?_, hsq, separated_multiplier_memLp_top_restrict S _
    (hζ.continuous_deriv (by simp)) hζc.deriv _ (hη.continuous.pow 2) hηsq⟩
  · have hpartial : Continuous (spatialPartial k η) :=
      (hη.continuous_fderiv (by simp)).clm_apply continuous_const
    simpa only [mul_assoc, Pi.mul_apply, Pi.pow_apply] using (separated_multiplier_memLp_top_restrict S ζ hζ.continuous hζc _
      (hη.continuous.mul hpartial) hηc.mul_right).const_mul (-2 : ℝ)
  · simpa only [mul_assoc, Pi.mul_apply, Pi.pow_apply] using hsq.const_mul (-1 : ℝ)

/-- The cutoff-weighted divergence belongs to restricted `L²`. -/
theorem localizedGradientDivergence_memLp
    (QG : TimeVelocity d → PDE.Vec d) (QH : TimeVelocity d → PDE.Mat d)
    (hQG : ∀ k : Fin d, ParabolicMemLpOn S 2 (fun z => QG z k))
    (hQHdiag : ∀ k : Fin d, ParabolicMemLpOn S 2 (fun z => QH z k k))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) :
    ParabolicMemLpOn S 2 (fun z => ζ z.1 * localizedGradientDivergence η QG QH z) := by
  obtain ⟨hc, hs, -, -⟩ := energy_weights_memLp_top S η hη hηc ζ hζ hζc
  refine (memLp_congr_ae (ae_of_all _ fun z => ?_)).mp
    (memLp_finsetSum Finset.univ fun k _ => ((hc k).mul' (hQG k)).add (hs.mul' (hQHdiag k)))
  simp only [localizedGradientDivergence, ← Finset.sum_neg_distrib, Finset.mul_sum, Pi.add_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

end

end HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
