module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.AngularHaarDisintegration

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsActualNativeHaarFamily

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)

def family : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P :=
  (KPMsFixedHaarDisintegration.disintegration_at_fixed_haar F ζ hζ R P).some

end DedekindZetaZeroFree.KPMsActualNativeHaarFamily

end
