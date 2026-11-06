module

public import GS.Continuation.ExponentialChart

@[expose] public section


/-!
# Pointed homeomorphism of the ORIGINAL compact images

 Compactness, continuity and same fibres are taken
from theorem bodies, not assumptions. Only the two compact images are identified;
coverage of a neighbourhood of the whole GS family and the cone obstruction are
not claimed here.
-/

noncomputable section
namespace GS.Continuation
open GS.Extensions

section
variable {q : ℕ} (Q₀ : Mat q) (η : ℝ)
/-- Convenient names for the two genuine compact image spaces. -/
abbrev OriginalFImage :=
  Set.range (fun p : ↥(originalK q η) => originalF Q₀ p.val)

end

end GS.Continuation
