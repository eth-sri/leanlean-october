import RequestProject.GenusSpinePresentation
import RequestProject.GenusCollapseLoopRepresentatives
import RequestProject.NamedPresentation
noncomputable section


/-! The finite marked block presentation of the actual surviving genus spine. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev NamedSpineGen := SpinePresentationGen q ⊕ (Fin q × Bool)
abbrev NamedSpineRel := SpinePresentationRel q ⊕ (Fin q × Bool)

instance : Finite (NamedSpineRel q) := inferInstance

def namedSpinePresentation : NamedSpineRel q → FreeGroup (NamedSpineGen q) :=
  NamedPresentation.rel (spinePresentation q) (spinePresentationMarkedWord q)

def namedSpineGroupEquiv :
    PresGroup (spinePresentation q) ≃* PresGroup (namedSpinePresentation q) :=
  NamedPresentation.groupEquiv _ _

/-- Each distinguished generator represents its actual geometric marking word. -/
theorem namedSpine_generator x :
    (QuotientGroup.mk (FreeGroup.of (Sum.inr x)) : PresGroup (namedSpinePresentation q)) =
      namedSpineGroupEquiv q
        (QuotientGroup.mk (spinePresentationMarkedWord q x)) :=
  NamedPresentation.name_eq_word _ _ x

/-- The formal surface word fills in the genuine finite marked block presentation. -/
theorem namedSpine_surface_filling :
    commWord (fun x =>
      (QuotientGroup.mk (FreeGroup.of (Sum.inr x)) : PresGroup (namedSpinePresentation q)))
      (finitePairs q) = 1 := by
  rw [commWord_congr (namedSpine_generator q)]
  change commWord (fun x => (namedSpineGroupEquiv q).toMonoidHom
    (QuotientGroup.mk (spinePresentationMarkedWord q x))) (finitePairs q) = 1
  rw [← map_commWord]
  exact (congrArg _
    (spinePresentationMarkedWord_hfilling q)).trans (map_one _)

def namedSpinePi1Equiv :=
  (spinePresentationPi1Equiv q).trans (namedSpineGroupEquiv q)
