module

public import RequestProject.GenusNamedSpine

@[expose] public section

/-! The genuine finite marked presentation compared with the previously verified block. -/
namespace FiniteChains.Comb
variable {X : Complex2} {a b : X.V}

 variable (h : a = b)

def pi1BaseEqEquiv : Pi1 X a ≃* Pi1 X b := by
  aesop

 theorem pi1BaseEqEquiv_mk (p : Loop X a) (q : Loop X b)
    (hpq : p.1 = q.1) : pi1BaseEqEquiv h (Pi1.mk p) = Pi1.mk q := by
  subst b
  have he := Subtype.ext hpq
  solve_by_elim
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def namedSpineToOldEquiv :=
  (namedSpinePi1Equiv q).symm.trans
    ((pi1BaseEqEquiv (markedSpineTree_root q)).trans
      ((markedSpinePi1Equiv q).trans (genusSpineToOldPi1Equiv q)))

variable (x : Fin q × Bool)

noncomputable def treeMarkedSpineLoop :
    Loop (markedSpineCx q) (markedSpineTree q).root :=
  ⟨(markedSpineLoop q x).1, by grind [markedSpineTree_root]⟩

theorem namedSpinePi1Equiv_marked :
    namedSpinePi1Equiv q (Pi1.mk (treeMarkedSpineLoop q x)) =
      (QuotientGroup.mk (FreeGroup.of (Sum.inr x)) : PresGroup (namedSpinePresentation q)) := (namedSpine_generator q x).symm

/-- The distinguished names correspond exactly to the verified old block marking. -/
theorem namedSpineToOld_marked :
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
  simp [markedSpineLoop_inclusion_class]

end FiniteChains.Davis.Genus
