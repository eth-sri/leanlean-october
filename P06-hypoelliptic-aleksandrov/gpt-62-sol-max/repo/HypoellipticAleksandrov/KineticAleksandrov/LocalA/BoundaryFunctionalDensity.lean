module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryFunctionalProbes
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure

/-! # Uniform density of ambient smooth traces on the actual closed boundary -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Evolution Topology
open scoped CompactlySupported Topology

/-- Every compact continuous datum on the closed trace is uniformly approximated by probes. -/
theorem boundaryProbeCc_dense {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ)
    (g : C_c(localTrace a T v₀ R, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : boundaryProbeSubmodule d,
      ∀ P, |boundaryProbeCcLinear a T v₀ R f P - g P| ≤ ε := by
  let j : localTrace a T v₀ R → ℝ × PDE.Vec d × PDE.Vec d :=
    fun P => (KineticPoint.homeomorphProd d) P.1
  have hj : IsClosedEmbedding j := (KineticPoint.homeomorphProd d).isClosedEmbedding.comp
    (isClosed_localTrace a T v₀ R).isClosedEmbedding_subtypeVal
  obtain ⟨f, hf, hclose⟩ := exists_smooth_compact_probe_close_embedding hj g ε hε
  exact ⟨⟨f, hf, f.hasCompactSupport⟩, hclose⟩

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
