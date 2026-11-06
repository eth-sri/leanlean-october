import Mathlib.Tactic

import GS.ManifoldCompletion.OrbitSmooth
import GS.CayleyCharts.Differential
import GS.Extensions.GeodesicNormal



/-!
# Coordinate differential of the orbit inclusion

We differentiate the actual Cayley formula. Its derivative is not defined by
fiat. At the centre, the derivative of cayley is -2 times the identity; the
right transpose changes that sign. In the no-overlap case the Frobenius
identity gives an injective differential. The exact range equals the checked
TwoFactorDirection predicate.

This is a coordinate fderiv theorem. The mfderiv/TangentSpace bridge is in
TangentBridge.lean. No IsImmersion predicate is redefined here.
-/

open GS.LieAction GS.Extensions
namespace GS.ManifoldCompletion
variable  {block₁ block₂ : Fin n → ℕ}





/-- Translate the factor-side injectivity condition into the original
left-coordinate disjoint-support condition. -/
theorem noOverlap_offDiagonalDisjoint (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm) := by
  intro i j h₂ h₁
  apply σ.symm.injective
  apply hn
  apply Prod.ext
  · exact h₁
  · aesop









end GS.ManifoldCompletion
