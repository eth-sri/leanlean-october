module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelFixedTest
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelCutoffSequence
public import PDEFoundation.Calculus.RegularityOrder


/-! # Compact smooth time-state probes and their terminal slices -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set Function
open scoped Topology

variable {n : ℕ}

variable (Φ : BoundedBorel (ℝ × EvolutionAmbientState n))

/-- Restrict a bounded Borel time-state probe to a terminal time. -/
def jointTerminalProbeSlice
     (τ : ℝ) :
    BoundedBorel (EvolutionAmbientState n) :=
  ⟨fun x => Φ (τ, x), Φ.measurable.comp (measurable_const.prodMk measurable_id), by
    obtain ⟨C, hC0, hC⟩ := Φ.exists_bound
    exact ⟨C, hC0, fun x => hC (τ, x)⟩⟩

/-- Every slice of a smooth compact time-state probe is smooth and compactly supported. -/
theorem jointTerminalProbeSlice_regular

    (hΦ : ContDiff ℝ PDE.smoothOrder Φ) (hc : HasCompactSupport Φ) (τ : ℝ) :
    ContDiff ℝ PDE.smoothOrder (jointTerminalProbeSlice Φ τ) ∧
      HasCompactSupport (jointTerminalProbeSlice Φ τ) := by
  refine ⟨hΦ.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  apply HasCompactSupport.intro (hc.image continuous_snd)
  intro x hx
  apply notMem_support.mp
  intro hnon
  exact hx ⟨(τ, x), subset_closure hnon, rfl⟩

/-- Near a fixed terminal time, all neighboring slices of a compact graph-supported
probe are supported inside that fixed terminal fiber. -/
theorem eventually_jointTerminalProbeSlice_admissible
    {Ω : PDE.VelocityRegion n} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n}
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n))
    (hΦ : ContDiff ℝ PDE.smoothOrder Φ) (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ {q : ℝ × EvolutionAmbientState n |
      q.2 ∈ evolutionStateSet Ω γ q.1}) (τ : ℝ) :
    ∀ᶠ t in 𝓝 τ, IsSmoothCompactTerminalDatum Ω γ τ (jointTerminalProbeSlice Φ t) := by

  have hK : IsCompact (tsupport Φ ∩ {z | z.2 ∉ evolutionStateSet Ω γ τ}) := hc.inter_right
    (((isOpen_movingDomain hΩ τ).prod isOpen_univ).isClosed_compl.preimage continuous_snd)


  have hnear  := ((hK.image continuous_fst).isClosed).isOpen_compl.mem_nhds (by
      rintro ⟨z, hz, hzt⟩
      have hi := hs hz.1
      change z.2 ∈ evolutionStateSet Ω γ z.1 at hi
      rw [hzt] at hi
      exact hz.2 hi)
  filter_upwards [hnear] with t ht
  obtain ⟨hr, hcompact⟩ := jointTerminalProbeSlice_regular Φ hΦ hc t
  refine ⟨hr, hcompact, ?_⟩
  intro x hx
  by_contra hxu

  exact ht ⟨(t, x), ⟨(tsupport_comp_subset_preimage Φ (continuous_const.prodMk continuous_id) hx), hxu⟩, rfl⟩

end HypoellipticAleksandrov.KineticAleksandrov
