import RequestProject.PresCylinderInclusionPi1
import RequestProject.RoseRootedLoops
import RequestProject.PresPosetReadingSurjective
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Inclusion of the genuine rose generator map is the actual marked free-group map. -/
theorem roseLoopHom_inclusion :
    (pi1Map (orderCxMap (iRose w) (iRose_monotone w)) Rose.base).comp
      (loopHom (roseGeneratorLoop (α := α))) = alphaFree w := by
  aesop

/-- The actual free-group marking surjects onto the presentation fundamental group. -/
theorem alphaFree_surjective (hpos : ∀ j, 0 < (w j).length) :
    Function.Surjective (alphaFree w) := by
  intro z
  cases' presRoseInclusion_pi1_surjective w hpos Rose.base z with q hq
  cases' roseLoopHom_surjective q with p hp
  have h := DFunLike.congr_fun (roseLoopHom_inclusion w) p
  aesop

variable (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

/-- The marked presentation comparison is surjective for actual nonempty relator words. -/
theorem alphaHomW_surjective (hpos : ∀ j, 0 < (w j).length) :
    Function.Surjective (alphaHomW ρ w hw) := by
  intro z
  cases' alphaFree_surjective w hpos z with p hp
  exact ⟨QuotientGroup.mk p, hp⟩

/-- Reading and marking are actual inverse maps on the presentation fundamental group. -/
theorem alphaHomW_readingPresW (hpos : ∀ j, 0 < (w j).length)
    z :
    alphaHomW ρ w hw (readingPresW ρ w hw z) = z := by
  obtain ⟨p, rfl⟩ := alphaHomW_surjective w ρ hw hpos z
  rw [readingPresW_alphaHomW]

/-- The actual presentation reading is injective, without a group-comparison premise. -/
theorem readingPresW_injective (hpos : ∀ j, 0 < (w j).length) :
    Function.Injective (readingPresW ρ w hw) :=
  Function.LeftInverse.injective (alphaHomW_readingPresW w ρ hw hpos)
