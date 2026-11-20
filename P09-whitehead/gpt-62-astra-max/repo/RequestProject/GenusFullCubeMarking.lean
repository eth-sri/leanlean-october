module

public import RequestProject.SurfaceFullCubeFilling
public import RequestProject.GenusSpinePresentation
public import RequestProject.ZeroPi2Descent

@[expose] public section

/-! The actual surviving-spine marking contracts in the full cube quotient. -/

noncomputable section

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def oldToFullCube :
    Hom (orderCx (QOld (cmpRel (GenusVertex q))))
      (orderCx (QCube (cmpRel (GenusVertex q)))) :=
  orderCxMap Subtype.val (fun _ _ h => h)

def markedSpineToFullCube :
    Hom (markedSpineCx q) (orderCx (QCube (cmpRel (GenusVertex q)))) :=
  Hom.comp (oldToFullCube q)
    (Hom.comp (genusSpineToOld q) (componentIncl (genusSpineCx q) (spineBase q)))

/-- The constructed map sends each actual capping loop to a null-homotopic loop. -/
theorem markedSpineToFullCube_mark_null (x : Fin q × Bool) :
    Htpy _
      ((markedSpineToFullCube q).onV (markedSpineBase q))
      ((markedSpineToFullCube q).onV (markedSpineBase q))
      (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) [] := by
  have hf := surfaceFullCube_loop_null _
    (isPath_gSig q (x.1.val, x.2))
  have hh := (mapPath_htpy (oldToFullCube q) (spineMarkedLoop_toOld_htpy q x)).trans hf; erw [← mapPath_comp, ← mapPath_comp, markedSpineLoop_inclusion]; exact hh

def spineFreeToFullCube :=
  (pi1Map (markedSpineToFullCube q) _).comp
    (SpanningTree.freeToPi1 (markedSpineTree q))

/-- All actual capped presentation relators die in the full cube quotient. -/
theorem spineFreeToFullCube_capped_rel
    (m : SpinePresentationRel q ⊕ (Fin q × Bool)) :
    spineFreeToFullCube q (cappedSpinePresentation q m) = 1 := by
  cases m with
  | inl f =>
      change pi1Map _ _
        (SpanningTree.freeToPi1 (markedSpineTree q)
          (SpanningTree.treeRel (markedSpineTree q) f)) = 1
      simp_all [SpanningTree.freeToPi1_treeRel]
  | inr x =>
      change pi1Map _ _
        _ = 1
      erw [SpanningTree.freeToPi1_pathWord _ (markedSpineLoop q x).2]
      change pi1Map _ _
        (pi1Conj ((markedSpineTree q).treePath_isPath (markedSpineBase q))
          (Pi1.mk (markedSpineLoop q x))) = 1
      erw [pi1Map_pi1Conj]
      have hz : pi1Map _ _
          (Pi1.mk (markedSpineLoop q x)) = 1 :=
        Quotient.sound (markedSpineToFullCube_mark_null q x)
      simp_all

/-- The genuine capped presentation maps to the full-cube fundamental group. -/
def cappedPresentationToFullCube :
    PresGroup (cappedSpinePresentation q) →*
      Pi1 _
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  QuotientGroup.lift _ (spineFreeToFullCube q) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    exact spineFreeToFullCube_capped_rel q m)

@[simp] theorem cappedPresentationToFullCube_mk (w : FreeGroup _) :
    cappedPresentationToFullCube q (QuotientGroup.mk w) = spineFreeToFullCube q w := rfl

end FiniteChains.Davis.Genus
