import Mathlib.Tactic

import RequestProject.GenusSpineMarking
import RequestProject.TruncatedCubePi1

/-! Factor the marked spine comparison through the genuine truncated face poset. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def genusSpineToTruncated  :=
  Hom.comp (orderCxMap (fun c : GenusSpineCell q => c.val) monotone_subtypeVal)
    (strictOrderIncl (GenusSpineCell q))

theorem genusSpineToOld_factor :
    genusSpineToOld q = Hom.comp truncatedRetractionHom (genusSpineToTruncated q) := rfl

theorem genusSpine_pi1_factor (z : Pi1 (genusSpineCx q) (spineBase q)) :
    pi1Map (genusSpineToOld q) (spineBase q) z =
      pi1Map truncatedRetractionHom ((genusSpineToTruncated q).onV (spineBase q))
        (pi1Map (genusSpineToTruncated q) (spineBase q) z) := by
  rcases z with ⟨p⟩
  apply congrArg Pi1.mk
  apply Subtype.ext
  simp [genusSpineToOld_factor, mapPath, Hom.comp]

/-- The remaining injectivity obligation is precisely the inclusion of the surviving spine
into the truncated complex, since truncation itself has already been proved harmless. -/
theorem genusSpine_pi1_injective_iff :
    Function.Injective (pi1Map (genusSpineToOld q) (spineBase q)) ↔
      Function.Injective (pi1Map (genusSpineToTruncated q) (spineBase q)) := by
  constructor
  · intro h x y hxy
    apply h
    rw [genusSpine_pi1_factor, genusSpine_pi1_factor, hxy]
  · intro h x y hxy
    apply h
    apply truncatedRetraction_pi1_injective_at
      ((genusSpineToTruncated q).onV (spineBase q))
    convert hxy using 1 <;> simp [← genusSpine_pi1_factor]

end FiniteChains.Davis.Genus
