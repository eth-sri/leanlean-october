module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.AngularCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsActualAngularShellSource
open KPMsActualAngularSource
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (S : SourceRecipe F ζ hζ R P H) (U : Level F ζ hζ)

variable (D : Iwasawa F ζ hζ) (V : Level F ζ hζ)

theorem fullToLevel_continuous :
    Continuous (fullToLevel F ζ hζ D V) :=
  continuous_quotient_mk'.quotient_lift _

theorem fullToLevel_measurable :
    Measurable (fullToLevel F ζ hζ D V) := by
  letI : BorelSpace (FullOmega F ζ hζ D) := ⟨rfl⟩
  letI : BorelSpace (Omega F ζ hζ D V) := ⟨rfl⟩
  exact (fullToLevel_continuous D V).measurable

end DedekindZetaZeroFree.KPMsActualAngularShellSource

end
