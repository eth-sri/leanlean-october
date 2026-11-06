module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelFixedTest
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelCutoffSequence

/-! # Compact smooth time-state probes and their terminal slices -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Function Filter
open scoped Topology

/-- Restrict a bounded Borel time-state probe to a terminal time. -/
def jointTerminalProbeSlice {n : ℕ}
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n)) (τ : ℝ) :
    BoundedBorel (EvolutionAmbientState n) :=
  ⟨fun x => Φ (τ, x), Φ.measurable.comp (measurable_const.prodMk measurable_id), by
    obtain ⟨C, hC0, hC⟩ := Φ.exists_bound
    grind⟩

variable {n : ℕ}

/-- Every slice of a smooth compact time-state probe is smooth and compactly supported. -/
theorem jointTerminalProbeSlice_regular 
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

/-- Near a fixed terminal time, all neighboring slices of a compact graph-supported
probe are supported inside that fixed terminal fiber. -/
theorem eventually_jointTerminalProbeSlice_admissible 
    {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n}
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ {q : ℝ × EvolutionAmbientState n |
      q.2 ∈ evolutionStateSet Ω γ q.1}) (τ : ℝ) :
    ∀ᶠ t in 𝓝 τ, IsSmoothCompactTerminalDatum Ω γ τ (jointTerminalProbeSlice Φ t) := by
  let K  :=
    tsupport Φ ∩ {z | z.2 ∉ evolutionStateSet Ω γ τ}
  have hK : IsCompact K := hc.inter_right
    (((isOpen_movingDomain hΩ τ).prod isOpen_univ).isClosed_compl.preimage continuous_snd)
  have hclosed  := (hK.image continuous_fst).isClosed
  have hnot : τ ∉ Prod.fst '' K := by
    rintro ⟨z, hz, hzt⟩
    grind
  have hnear : ∀ᶠ t in 𝓝 τ, t ∉ Prod.fst '' K := hclosed.isOpen_compl.mem_nhds hnot
  filter_upwards [hnear] with t ht
  obtain ⟨hr, hcompact⟩ := jointTerminalProbeSlice_regular Φ hΦ hc t
  refine ⟨hr, hcompact, ?_⟩
  intro x hx
  by_contra hxu
  have hxs : (t, x) ∈ tsupport Φ :=
    tsupport_comp_subset_preimage Φ (continuous_const.prodMk continuous_id) hx
  aesop

end HypoellipticAleksandrov.KineticAleksandrov
