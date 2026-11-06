import Mathlib.Tactic

import RequestProject.GenusNamedSpine

/-! The genuine finite marked presentation compared with the previously verified block. -/
set_option backward.isDefEq.respectTransparency false
namespace FiniteChains.Comb
variable {X : Complex2} {a b : X.V}

 def pi1BaseEqEquiv (h : a = b) : Pi1 X a ≃* Pi1 X b := by
  subst b
  exact MulEquiv.refl _

 theorem pi1BaseEqEquiv_mk (h : a = b) (p : Loop X a) (q : Loop X b)
    (hpq : p.1 = q.1) : pi1BaseEqEquiv h (Pi1.mk p) = Pi1.mk q := by
  subst b
  have he  := Subtype.ext hpq
  subst q
  rfl
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def namedSpineToOldEquiv :
    PresGroup (namedSpinePresentation q) ≃*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q))))
        ((genusSpineToOld q).onV (spineBase q)) :=
  (namedSpinePi1Equiv q).symm.trans
    ((pi1BaseEqEquiv (markedSpineTree_root q)).trans
      ((markedSpinePi1Equiv q).trans (genusSpineToOldPi1Equiv q)))

variable (x : Fin q × Bool)
noncomputable def treeMarkedSpineLoop  :
    Loop (markedSpineCx q) (markedSpineTree q).root :=
  ⟨(markedSpineLoop q x).1, by grind [FiniteChains.Davis.Genus.markedSpineTree_root]⟩

theorem namedSpinePi1Equiv_marked  :
    namedSpinePi1Equiv q (Pi1.mk (treeMarkedSpineLoop q x)) =
      (QuotientGroup.mk (FreeGroup.of (Sum.inr x)) : PresGroup (namedSpinePresentation q)) := (namedSpine_generator q x).symm

/-- The distinguished names correspond exactly to the verified old block marking. -/
theorem namedSpineToOld_marked  :
    namedSpineToOldEquiv q (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x)) := by
  rw [← namedSpinePi1Equiv_marked q x]
  change (genusSpineToOldPi1Equiv q)
    ((markedSpinePi1Equiv q)
      (pi1BaseEqEquiv (markedSpineTree_root q)
        ((namedSpinePi1Equiv q).symm
          ((namedSpinePi1Equiv q) (Pi1.mk (treeMarkedSpineLoop q x)))))) = _
  rw [MulEquiv.symm_apply_apply,
    pi1BaseEqEquiv_mk (markedSpineTree_root q) (treeMarkedSpineLoop q x)
      (markedSpineLoop q x) rfl]
  change pi1Map (genusSpineToOld q) (spineBase q)
    (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)
      (Pi1.mk (markedSpineLoop q x))) = _
  rw [markedSpineLoop_inclusion_class]

end FiniteChains.Davis.Genus
