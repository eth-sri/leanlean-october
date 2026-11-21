module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdditiveCoefficientEnergy

@[expose] public section

namespace DedekindZetaZeroFree
namespace PoissonProbe
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
open scoped NumberField Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

 theorem norm_pos (A : SArithmeticData F) (k : A.G) : 0 < A.norm k := by
  unfold SArithmeticData.norm
  apply mul_pos
  · exact Finset.prod_pos (fun w _ => pow_pos (norm_pos_iff.mpr (k.1 w).ne_zero) _)
  · exact Finset.prod_pos (fun v _ => norm_pos_iff.mpr (k.2 v).ne_zero)

 def normalizeShape (A : SArithmeticData F) (k : A.G) : A.G :=
  k / A.radialSection (A.norm k) (norm_pos A k)

end
end PoissonProbe
end DedekindZetaZeroFree
