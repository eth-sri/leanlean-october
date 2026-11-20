module

public import RequestProject.GenusSpinePresentation
public import RequestProject.GenusCollapseLoopRepresentatives
public import RequestProject.NamedPresentation

@[expose] public section

/-! The finite marked block presentation of the actual surviving genus spine. -/
noncomputable section

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev NamedSpineGen := SpinePresentationGen q ⊕ (Fin q × Bool)
abbrev NamedSpineRel := SpinePresentationRel q ⊕ (Fin q × Bool)

instance : Finite (NamedSpineGen q) := inferInstance
instance : Finite (NamedSpineRel q) := inferInstance

def namedSpinePresentation :=
  NamedPresentation.rel (spinePresentation q) (spinePresentationMarkedWord q)

def namedSpineGroupEquiv :
    PresGroup (spinePresentation q) ≃* PresGroup (namedSpinePresentation q) :=
  NamedPresentation.groupEquiv _ _

/-- Each distinguished generator represents its actual geometric marking word. -/
theorem namedSpine_generator (x : Fin q × Bool) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      namedSpineGroupEquiv q
        (QuotientGroup.mk (spinePresentationMarkedWord q x)) :=
  by apply NamedPresentation.name_eq_word

/-- The formal surface word fills in the genuine finite marked block presentation. -/
theorem namedSpine_surface_filling :
    commWord (fun x : Fin q × Bool =>
      (QuotientGroup.mk (FreeGroup.of (Sum.inr x)) : PresGroup (namedSpinePresentation q)))
      (finitePairs q) = 1 := by
  rw [commWord_congr (namedSpine_generator q)]
  change commWord (fun x => (namedSpineGroupEquiv q).toMonoidHom
    _) _ = 1
  rw [← map_commWord]
  exact (congrArg _
    (spinePresentationMarkedWord_hfilling q)).trans (map_one _)

def namedSpinePi1Equiv :=
  (spinePresentationPi1Equiv q).trans (namedSpineGroupEquiv q)

end FiniteChains.Davis.Genus
