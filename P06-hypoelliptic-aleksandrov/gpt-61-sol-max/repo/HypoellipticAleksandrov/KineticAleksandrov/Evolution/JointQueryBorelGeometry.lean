module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue

/-! # Compact terminal supports under a continuous moving boundary -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set
open scoped Topology

variable {n : ℕ} {Ω : PDE.VelocityRegion n}

variable (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n}

variable (hγ : Continuous γ)

include hΩ hγ in
/-- The time-state set of interior terminal states is open for a continuous motion. -/
theorem isOpen_terminal_state_graph    :
    IsOpen {q : ℝ × EvolutionAmbientState n | q.2 ∈ evolutionStateSet Ω γ q.1} := by

  convert hΩ.preimage ((continuous_fst.comp continuous_snd).sub (hγ.comp continuous_fst)) using 1
  ext q
  exact and_iff_left (mem_univ _ ) |>.trans mem_movingDomain_iff

section
variable {K : Set (EvolutionAmbientState n)} (hK : IsCompact K)

include hΩ hγ hK
/-- A compact interior terminal support remains interior for all nearby terminal times. -/
theorem IsCompact.eventually_subset_terminal_state

     {τ : ℝ}
    (hKT : K ⊆ evolutionStateSet Ω γ τ) :
    ∀ᶠ t in 𝓝 τ, K ⊆ evolutionStateSet Ω γ t := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  exact (isOpen_terminal_state_graph hΩ hγ).mem_nhds (hKT hx)

/-- The times at which a fixed compact set is an interior terminal support form an open set. -/
theorem IsCompact.isOpen_terminal_support_times

     :
    IsOpen {τ : ℝ | K ⊆ evolutionStateSet Ω γ τ} := by
  apply isOpen_iff_mem_nhds.mpr
  intro τ hτ
  exact IsCompact.eventually_subset_terminal_state hΩ hγ hK hτ
end



include hΩ hγ in
/-- A compact interior datum remains a valid terminal datum on a whole time window. -/
theorem IsSmoothCompactTerminalDatum.exists_terminal_window
       {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, dist t τ < δ →
      IsSmoothCompactTerminalDatum Ω γ t F := by
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp
    (IsCompact.eventually_subset_terminal_state hΩ hγ hF.2.1 hF.2.2)
  exact ⟨δ, hδ, fun t ht => ⟨hF.1, hF.2.1, hb ht⟩⟩

include hΩ in
/-- If a fixed datum is supported inside every fiber of a slab, it vanishes on each
lateral frontier of that slab. -/
theorem terminalDatum_zero_lateral_of_support

    {a T : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hs : ∀ t ∈ Icc a T, tsupport F ⊆ evolutionStateSet Ω γ t) :
    ∀ p ∈ movingClosedSlab Ω γ a T,
      p.position ∈ frontier (movingDomain Ω γ p.time) → F (p.position, p.velocity) = 0 := by
  intro p hp hfr
  apply Function.notMem_support.mp
  intro hnon

  rw [(isOpen_movingDomain hΩ p.time).frontier_eq] at hfr
  exact hfr.2 (hs p.time ⟨hp.1, hp.2.1⟩ (subset_closure hnon)).1

variable {γ : ℝ → PDE.Vec n}

/-- The actual kinetic starting point of a valid evolution query. -/
def evolutionQueryPoint
    (q : EvolutionQuery Ω γ) : KineticPoint n := ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩

/-- Extracting the actual starting point is continuous on the valid query subtype. -/
theorem continuous_evolutionQueryPoint
     : Continuous (@evolutionQueryPoint n Ω γ) := KineticPoint.continuous_mk (continuous_fst.comp continuous_subtype_val)
    (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))
    (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))

end HypoellipticAleksandrov.KineticAleksandrov
