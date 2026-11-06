import RequestProject.GenusSpineMarking
import RequestProject.TruncatedCubePi1
import RequestProject.Tac


/-! Factor the marked spine comparison through the genuine truncated face poset. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def genusSpineToTruncated :
    Hom (genusSpineCx q) (orderCx (GenusTruncatedCell q)) :=
  Hom.comp (orderCxMap (·.val) monotone_subtypeVal)
    (strictOrderIncl _)

theorem genusSpineToOld_factor :
    genusSpineToOld q = Hom.comp truncatedRetractionHom (genusSpineToTruncated q) := rfl

theorem genusSpine_pi1_factor z :
    pi1Map (genusSpineToOld q) (spineBase q) z =
      pi1Map truncatedRetractionHom ((genusSpineToTruncated q).onV (spineBase q))
        (pi1Map (genusSpineToTruncated q) (spineBase q) z) := by
  rcases z with ⟨p⟩
  apply congrArg Pi1.mk
  apply Subtype.ext
  simp [genusSpineToOld_factor, mapPath, Hom.comp, List.map_map, Function.comp_def]

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
      _
    simp_all [← genusSpine_pi1_factor]
