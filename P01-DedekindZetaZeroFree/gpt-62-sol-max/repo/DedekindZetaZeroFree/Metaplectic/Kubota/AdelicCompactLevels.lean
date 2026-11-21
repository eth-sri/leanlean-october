module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicRationalSplitting
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualQuotientTopology.Cover
open Topology
open scoped Pointwise
open scoped NumberField Classical

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev RawCover := KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ

open NumberField IsDedekindDomain
open KPAdelicCoverRestrictedProduct
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
set_option maxHeartbeats 800000

theorem rawCover_secondCountable : SecondCountableTopology (RawCover F ζ hζ) := by
  letI : SecondCountableTopology (RestrictedCover F ζ hζ) :=
    KPAdelicCoverCertificatesRaw.restricted_secondCountable F ζ hζ
  letI : ∀ v : KPHilbert.Place F, IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    fun v => by
      cases v with
      | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
      | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q
          (depth F ζ hζ q) (depth_admissible F ζ hζ q)).2.2
  letI : Fact (∀ v, IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) :=
    ⟨compact_open F ζ hζ⟩
  haveI : IsTopologicalGroup (RestrictedCover F ζ hζ) := inferInstance
  haveI : SecondCountableTopology (CubicGL2Adelic F ζ hζ) := inferInstance
  infer_instance

end DedekindZetaZeroFree.ActualQuotientTopology.Cover

end
