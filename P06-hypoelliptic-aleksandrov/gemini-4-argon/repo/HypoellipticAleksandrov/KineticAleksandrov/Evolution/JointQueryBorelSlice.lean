module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelFixedTest
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelCutoffSequence

/-! # Compact smooth time-state probes and their terminal slices -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Function Filter
open scoped Topology

/- Restrict a bounded Borel time-state probe to a terminal time. -/
def jointTerminalProbeSlice {n }
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n)) (τ : ℝ) :
    BoundedBorel (EvolutionAmbientState n) :=
  ⟨fun x => Φ (τ, x), Φ.measurable.comp (measurable_const.prodMk measurable_id), by
    obtain ⟨C, hC0, hC⟩ := Φ.exists_bound
    exact ⟨C, hC0, fun x => hC (τ, x)⟩⟩

/- Every slice of a smooth compact time-state probe is smooth and compactly supported. -/
theorem jointTerminalProbeSlice_regular {n }
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (jointTerminalProbeSlice Φ τ) ∧
      HasCompactSupport (jointTerminalProbeSlice Φ τ) := by
  refine ⟨hΦ.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  apply HasCompactSupport.intro (hc.image continuous_snd)
  intro x hx
  apply notMem_support.mp
  intro hnon
  exact hx ⟨(τ, x), subset_closure hnon, rfl⟩

/- Near a fixed terminal time, all neighboring slices of a compact graph-supported
probe are supported inside that fixed terminal fiber. -/
end HypoellipticAleksandrov.KineticAleksandrov
