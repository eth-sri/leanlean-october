import RequestProject.GenusNamedSpine
noncomputable section


/-! The genuine finite marked presentation compared with the previously verified block. -/
namespace FiniteChains.Comb
variable {X : Complex2} {a b : X.V}

 def pi1BaseEqEquiv (h : a = b) : Pi1 X a ≃* Pi1 X b := by
  subst b
  exact MulEquiv.refl _

 theorem pi1BaseEqEquiv_mk h (p : Loop X a) (q : Loop X b)
    (hpq : p.1 = q.1) : pi1BaseEqEquiv h (Pi1.mk p) = Pi1.mk q := by
  subst b
  have he := Subtype.ext hpq
  subst q
  rfl
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def namedSpineToOldEquiv :=
  (namedSpinePi1Equiv q).symm.trans
    ((pi1BaseEqEquiv (markedSpineTree_root q)).trans
      ((markedSpinePi1Equiv q).trans (genusSpineToOldPi1Equiv q)))

def treeMarkedSpineLoop (x : Fin q × Bool) :
    Loop (markedSpineCx q) (markedSpineTree q).root :=
  ⟨(markedSpineLoop q x).1, by grind [markedSpineTree_root]⟩

theorem namedSpinePi1Equiv_marked x :
    namedSpinePi1Equiv q (Pi1.mk (treeMarkedSpineLoop q x)) =
      (QuotientGroup.mk (FreeGroup.of (Sum.inr x)) : PresGroup (namedSpinePresentation q)) := (namedSpine_generator q x).symm

/-- The distinguished names correspond exactly to the verified old block marking. -/
theorem namedSpineToOld_marked x :
    namedSpineToOldEquiv q (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x)) := by
  rw [← namedSpinePi1Equiv_marked q x]
  change (genusSpineToOldPi1Equiv q)
    ((markedSpinePi1Equiv q)
      (pi1BaseEqEquiv (markedSpineTree_root q)
        ((namedSpinePi1Equiv q).symm
          ((namedSpinePi1Equiv q) (Pi1.mk (treeMarkedSpineLoop q x)))))) = _
  rw [MulEquiv.symm_apply_apply,
    pi1BaseEqEquiv_mk (markedSpineTree_root q) _
      _ rfl]
  change pi1Map _ (spineBase q)
    (pi1Map (componentIncl _ _) _
      (Pi1.mk (markedSpineLoop q x))) = _
  rw [markedSpineLoop_inclusion_class]
