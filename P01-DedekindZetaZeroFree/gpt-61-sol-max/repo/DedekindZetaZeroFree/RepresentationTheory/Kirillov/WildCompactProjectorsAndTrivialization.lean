module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.FiniteTensorSectionsAndTopology

@[expose] public section

section

noncomputable section

set_option maxHeartbeats 200000

set_option maxRecDepth 4096

namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov.GlobalEvaluation

open scoped NumberField Topology Classical

open NumberField IsDedekindDomain KPKirillovGenuineSectionCharts

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
  (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F v m)
  (ψ : Multiplicative (K F v) →* ℂˣ) (hψ : IsLocallyConstant ψ)

local notation "topology" => KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ v m




















































end DedekindZetaZeroFree.KPWildCompactProjectorKirillov.GlobalEvaluation

end

end

section

noncomputable section

set_option maxHeartbeats 1000000

set_option maxRecDepth 4096

namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov.GlobalEvaluation

open scoped NumberField Topology Classical

open NumberField IsDedekindDomain KPKirillovGenuineSectionCharts

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
  (m : ℕ) 
  (ψ : Multiplicative (K F v) →* ℂˣ) 





end DedekindZetaZeroFree.KPWildCompactProjectorKirillov.GlobalEvaluation

end

end

section

noncomputable section

set_option maxHeartbeats 200000

set_option maxRecDepth 4096

namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) 

variable (v : HeightOneSpectrum (RingOfIntegers F))



end DedekindZetaZeroFree.KPWildCompactProjectorKirillov

end

end
