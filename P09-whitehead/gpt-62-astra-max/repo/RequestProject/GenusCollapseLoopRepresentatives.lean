module

public import RequestProject.GenusCollapseIteration


@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genusSpineToTruncated_pi1_surjective :
    Function.Surjective (pi1Map (genusSpineToTruncated q) (spineBase q)) := by
  rintro ⟨p⟩
  obtain ⟨r, hr, hrB, hh⟩ := (genusSpine_comparison q).2
    _ p.1 (spineBase q).2 p.2 (fun _ _ => ⟨trivial, trivial⟩)
  refine ⟨(strictOrderPi1Equiv (P := GenusSpineCell q) _).symm (Pi1.mk (⟨liftPathIn r hrB, isPath_liftPathIn r hrB (spineBase q).2 (spineBase q).2 hr⟩)), ?_⟩
  rw [genusSpineToTruncated_pi1_factor_weak, MulEquiv.apply_symm_apply]
  apply Quotient.sound
  change Htpy _ _ _
    (mapPath (subposetHom (fun c => c ∈ genusSpineCellSet q)) (liftPathIn r hrB)) p.1
  rw [mapPath_liftPathIn]
  exact hh.symm

theorem genusSpineToOld_pi1_surjective :
    Function.Surjective (pi1Map (genusSpineToOld q) (spineBase q)) := by
  intro z
  obtain ⟨v, hv⟩ := truncatedRetraction_pi1_surjective_at
    ((genusSpineToTruncated q).onV (spineBase q)) z
  obtain ⟨w, hw⟩ := genusSpineToTruncated_pi1_surjective q v
  exact ⟨w, by simp_all [genusSpine_pi1_factor, hw]⟩

noncomputable def genusSpineToOldPi1Equiv :=
  MulEquiv.ofBijective _
    ⟨genusSpineToOld_pi1_injective q, genusSpineToOld_pi1_surjective q⟩

end FiniteChains.Davis.Genus
