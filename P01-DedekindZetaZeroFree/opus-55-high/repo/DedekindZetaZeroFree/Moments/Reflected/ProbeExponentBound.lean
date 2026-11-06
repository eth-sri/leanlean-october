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

 theorem norm_pos (A : SArithmeticData F) (k : A.G) : 0 < A.norm k := by apply DedekindZetaZeroFree.ProbeSheet.norm_pos <;> assumption

 def normalizeShape (A : SArithmeticData F) (k : A.G) : A.G :=
  k / A.radialSection (A.norm k) (norm_pos A k)
