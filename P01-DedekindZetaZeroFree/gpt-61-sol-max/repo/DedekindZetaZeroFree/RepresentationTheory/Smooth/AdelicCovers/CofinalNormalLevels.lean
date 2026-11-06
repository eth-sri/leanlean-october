module

public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalAndAdelicCovers
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPSmoothCofinalNormalLevels

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) 








open Filter Set
open scoped Topology































section NormalCoreHelpers

open Filter Set
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem compact_conjugation_nhds (S : Set G) (hS : IsCompact S)
    (U : OpenSubgroup G) :
    ∃ W ∈ 𝓝 (1 : G), ∀ g ∈ S, ∀ u ∈ W, g⁻¹ * u * g ∈ U := by
  have h : ∀ᶠ u in 𝓝 (1 : G), ∀ g ∈ S, g⁻¹ * u * g ∈ U := by
    apply hS.eventually_forall_of_forall_eventually
    intro g hg
    have hc : Continuous (fun p : G × G => p.2⁻¹ * p.1 * p.2) :=
      (continuous_snd.inv.mul continuous_fst).mul continuous_snd
    have hu : g⁻¹ * (1 : G) * g ∈ U := by simp
    exact hc.continuousAt.eventually (U.isOpen.mem_nhds hu)
  exact ⟨{u | ∀ g ∈ S, g⁻¹ * u * g ∈ U}, h, by tauto⟩

end NormalCoreHelpers

section CountableBasisHelpers
open Filter Set
open scoped Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end CountableBasisHelpers

section ActualFiniteTopology
open Filter Set Topology
open scoped Topology

end ActualFiniteTopology

section ActualCompactOpenBasis
open Filter Set Topology
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end ActualCompactOpenBasis





































end
end DedekindZetaZeroFree.KPSmoothCofinalNormalLevels
