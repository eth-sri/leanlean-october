module

public import RequestProject.GenusSpineMarking
public import RequestProject.TruncatedCubePi1

@[expose] public section

/-! Factor the marked spine comparison through the genuine truncated face poset. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def genusSpineToTruncated :
    Hom (genusSpineCx q) (orderCx (GenusTruncatedCell q)) :=
  Hom.comp (orderCxMap (·.val) monotone_subtypeVal)
    (strictOrderIncl (GenusSpineCell q))

theorem genusSpineToTruncated_pi1_factor
    (z : Pi1 (genusSpineCx q) (spineBase q)) :
    pi1Map (genusSpineToTruncated q) (spineBase q) z =
      pi1Map (orderCxMap (fun c : GenusSpineCell q => c.1) monotone_subtypeVal)
        (spineBase q) (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q) z) := by
  exact pi1Map_comp_apply (strictOrderIncl _) (orderCxMap (·.1) monotone_subtypeVal) (spineBase q) z

theorem genusSpine_pi1_factor (z : Pi1 (genusSpineCx q) (spineBase q)) :
    pi1Map (genusSpineToOld q) (spineBase q) z =
      pi1Map truncatedRetractionHom ((genusSpineToTruncated q).onV (spineBase q))
        (pi1Map (genusSpineToTruncated q) (spineBase q) z) := by
  exact pi1Map_comp_apply (genusSpineToTruncated q) truncatedRetractionHom (spineBase q) z

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
    convert hxy using 1 <;> simp only [← genusSpine_pi1_factor]

end FiniteChains.Davis.Genus
