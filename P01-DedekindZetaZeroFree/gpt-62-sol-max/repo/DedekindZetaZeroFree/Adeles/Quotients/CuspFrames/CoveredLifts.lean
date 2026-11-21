module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.Definitions
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CuspFrames

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames
open KPAdelicCoverRestrictedProduct
open KPMsGreenFlux
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
export KPMsActualCuspSource (arch_finite_factorization archRational rationalLift_finite_factor
  insertion_commutes archBasepoint_rational_mul)

variable {F ζ hζ}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)

theorem cuspLift_exists (j : Cusps A) (Y : ℝ)
    (x : X F ζ hζ) (hx : x ∈ cuspEnd A P j Y) :
    ∃ g : Cover F ζ hζ,
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g = x ∧
      AdmissibleFrame A j Y x g :=
  KPMsActualCuspSource.cuspLift_at A P j Y x hx

end DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames

end
