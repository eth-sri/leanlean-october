module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalProbes
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense

/-! # Uniform density of smooth ambient restrictions on the closed exit carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Topology
open SectionTwo TheoremA Evolution
open scoped CompactlySupported Topology

section
variable (H : Interval) (T : ℝ)

/-- Restriction of an ambient smooth probe to the closed physical exit carrier. -/
def exitProbeCc (f : exitProbeSubmodule) :
    C_c(stripClosedExit H T, ℝ) where
  toFun p := exitProbePhysical f p.1
  continuous_toFun := (exitProbePhysical_continuous_compact f).1.comp continuous_subtype_val
  hasCompactSupport' := (exitProbePhysical_continuous_compact f).2.comp_isClosedEmbedding
    (isClosed_stripClosedExit H T).isClosedEmbedding_subtypeVal

/-- Exit restriction is a linear map on the ambient probe vector space. -/
def exitProbeCcLinear :
    exitProbeSubmodule →ₗ[ℝ] C_c(stripClosedExit H T, ℝ) where
  toFun := exitProbeCc H T
  map_add' f g := by ext p; rfl
  map_smul' c f := by ext p; rfl

/-- The dense restriction family is closed under squaring. -/
theorem exitProbeCc_sq (f : exitProbeSubmodule) :
    ∃ g : exitProbeSubmodule,
      exitProbeCcLinear H T g = exitProbeCcLinear H T f * exitProbeCcLinear H T f := by
  refine ⟨⟨fun x => f.1 x * f.1 x, f.2.1.mul f.2.1, f.2.2.mul_left⟩, ?_⟩
  ext p
  rfl

/-- Smooth compact ambient restrictions uniformly approximate every compact exit datum. -/
theorem exitProbeCc_dense (g : C_c(stripClosedExit H T, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : exitProbeSubmodule, ∀ p, |exitProbeCcLinear H T f p - g p| ≤ ε := by
  let j : stripClosedExit H T → EvolutionVec 1 :=
    fun p => reconstructionPhysicalHomeomorph.symm p.1
  have hj : IsClosedEmbedding j := reconstructionPhysicalHomeomorph.symm.isClosedEmbedding.comp
    (isClosed_stripClosedExit H T).isClosedEmbedding_subtypeVal
  obtain ⟨f, hf, hclose⟩ := exists_smooth_compact_probe_close_embedding hj g ε hε
  exact ⟨⟨f, hf, f.hasCompactSupport⟩, hclose⟩

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
