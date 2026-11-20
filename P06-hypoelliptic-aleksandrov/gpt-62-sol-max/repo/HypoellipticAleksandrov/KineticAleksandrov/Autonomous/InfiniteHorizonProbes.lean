module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonConsistency
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalDensity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense

/-! # Compact tests on the closed infinite-horizon velocity-face carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Topology
open SectionTwo TheoremA Evolution
open scoped CompactlySupported Topology

/-- The infinite exit carrier consists of the two genuine physical velocity faces. -/
def stripInfiniteFace (H : Interval) : Set Point :=
  {p | p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi}

/-- The infinite velocity-face carrier is closed in the physical point topology. -/
theorem isClosed_stripInfiniteFace (H : Interval) : IsClosed (stripInfiniteFace H) :=
  (isClosed_eq ((continuous_apply 0).comp continuous_velocity) continuous_const).union
    (isClosed_eq ((continuous_apply 0).comp continuous_velocity) continuous_const)

/-- The face carrier inherits local compactness from physical Euclidean coordinates. -/
instance stripInfiniteFace_locallyCompactSpace (H : Interval) :
    LocallyCompactSpace (stripInfiniteFace H) := by
  let : LocallyCompactSpace Point :=
    (KineticPoint.homeomorphProd 1).isClosedEmbedding.locallyCompactSpace
  exact (isClosed_stripInfiniteFace H).locallyCompactSpace

/-- The face carrier inherits a countable topological basis. -/
instance stripInfiniteFace_secondCountableTopology (H : Interval) :
    SecondCountableTopology (stripInfiniteFace H) := by
  let : SecondCountableTopology Point := (KineticPoint.homeomorphProd 1).secondCountableTopology
  infer_instance

section
variable (H : Interval)

/-- Restriction of an ambient smooth probe to the closed physical exit carrier. -/
def infiniteExitProbeCc (f : exitProbeSubmodule) :
    C_c(stripInfiniteFace H, ℝ) where
  toFun p := exitProbePhysical f p.1
  continuous_toFun := (exitProbePhysical_continuous_compact f).1.comp continuous_subtype_val
  hasCompactSupport' := (exitProbePhysical_continuous_compact f).2.comp_isClosedEmbedding
    (isClosed_stripInfiniteFace H).isClosedEmbedding_subtypeVal

/-- Exit restriction is a linear map on the ambient probe vector space. -/
def infiniteExitProbeCcLinear :
    exitProbeSubmodule →ₗ[ℝ] C_c(stripInfiniteFace H, ℝ) where
  toFun := infiniteExitProbeCc H
  map_add' f g := by ext p; rfl
  map_smul' c f := by ext p; rfl

/-- The dense restriction family is closed under squaring. -/
theorem infiniteExitProbeCc_sq (f : exitProbeSubmodule) :
    ∃ g : exitProbeSubmodule,
      infiniteExitProbeCcLinear H g = infiniteExitProbeCcLinear H f * infiniteExitProbeCcLinear H
        f := by
  refine ⟨⟨fun x => f.1 x * f.1 x, f.2.1.mul f.2.1, f.2.2.mul_left⟩, ?_⟩
  ext p
  rfl

/-- Smooth compact ambient restrictions uniformly approximate every compact exit datum. -/
theorem infiniteExitProbeCc_dense (g : C_c(stripInfiniteFace H, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : exitProbeSubmodule, ∀ p, |infiniteExitProbeCcLinear H f p - g p| ≤ ε := by
  let j : stripInfiniteFace H → EvolutionVec 1 :=
    fun p => reconstructionPhysicalHomeomorph.symm p.1
  have hj : IsClosedEmbedding j := reconstructionPhysicalHomeomorph.symm.isClosedEmbedding.comp
    (isClosed_stripInfiniteFace H).isClosedEmbedding_subtypeVal
  obtain ⟨f, hf, hclose⟩ := exists_smooth_compact_probe_close_embedding hj g ε hε
  exact ⟨⟨f, hf, f.hasCompactSupport⟩, hclose⟩

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
