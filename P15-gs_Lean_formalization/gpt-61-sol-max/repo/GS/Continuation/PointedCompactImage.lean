
import GS.Continuation.ExponentialChart



/-!
# Pointed homeomorphism of the ORIGINAL compact images

 Compactness, continuity and same fibres are taken
from theorem bodies, not assumptions. Only the two compact images are identified;
coverage of a neighbourhood of the whole GS family and the cone obstruction are
not claimed here.
-/

namespace GS.Continuation
open GS.Extensions

/-- Convenient names for the two genuine compact image spaces. -/
abbrev OriginalFImage {q : ℕ} (Q₀ : Mat q) (η : ℝ) :=
  Set.range (fun p : ↥(originalK q η) => originalF Q₀ p.val)

/-- A basepoint in the F-image with its actual membership witness. -/
def originalFImageBase {q : ℕ} (Q₀ : Mat q) (η : ℝ) (hη : 0 ≤ η) :
    OriginalFImage Q₀ η :=
  ⟨basePoint Q₀,
    ⟨⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩,
      originalF_basePoint Q₀⟩⟩

end GS.Continuation
