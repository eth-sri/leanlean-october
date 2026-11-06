import RequestProject.SurfaceFullCubeFilling
import RequestProject.GenusSpinePresentation
import RequestProject.ZeroPi2Descent
import RequestProject.Tac
noncomputable section


/-! The actual surviving-spine marking contracts in the full cube quotient. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def oldToFullCube :
    Hom (orderCx (QOld (cmpRel (GenusVertex q))))
      (orderCx (QCube (cmpRel (GenusVertex q)))) :=
  orderCxMap Subtype.val (by tauto)

def markedSpineToFullCube :
    Hom (markedSpineCx q) (orderCx (QCube (cmpRel (GenusVertex q)))) :=
  Hom.comp (oldToFullCube q)
    (Hom.comp (genusSpineToOld q) (componentIncl _ _))

/-- The constructed map sends each actual capping loop to a null-homotopic loop. -/
theorem markedSpineToFullCube_mark_null x :
    Htpy (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineBase q))
      ((markedSpineToFullCube q).onV (markedSpineBase q))
      (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) [] := by
  have h := mapPath_htpy (oldToFullCube q) (spineMarkedLoop_toOld_htpy q x)
  have hf := surfaceFullCube_loop_null _
    (isPath_gSig q (x.1.val, x.2))
  have hh := h.trans hf
  unfold markedSpineToFullCube
  rwd [← mapPath_comp, ← mapPath_comp, markedSpineLoop_inclusion]
  exact hh

def spineFreeToFullCube :
    FreeGroup (SpinePresentationGen q) →*
      Pi1 (orderCx (QCube (cmpRel (GenusVertex q))))
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  (pi1Map _ _).comp
    (SpanningTree.freeToPi1 _)

/-- All actual capped presentation relators die in the full cube quotient. -/
theorem spineFreeToFullCube_capped_rel
    m :
    spineFreeToFullCube q (cappedSpinePresentation q m) = 1 := by
  cases m with
  | inl f =>
      change pi1Map _ _
        (SpanningTree.freeToPi1 _
          (SpanningTree.treeRel _ f)) = 1
      simp [SpanningTree.freeToPi1_treeRel, map_one]
  | inr x =>
      change pi1Map _ _
        (SpanningTree.freeToPi1 _
          (SpanningTree.pathWord _ (markedSpineLoop q x).1)) = 1
      rwd [SpanningTree.freeToPi1_pathWord _ (markedSpineLoop q x).2]
      change pi1Map _ _
        (pi1Conj ((markedSpineTree q).treePath_isPath _)
          (Pi1.mk (markedSpineLoop q x))) = 1
      rwd [pi1Map_pi1Conj]
      have hz : pi1Map _ _
          (Pi1.mk (markedSpineLoop q x)) = 1 :=
        Quotient.sound (markedSpineToFullCube_mark_null q x)
      simp_all

/-- The genuine capped presentation maps to the full-cube fundamental group. -/
def cappedPresentationToFullCube :
    PresGroup (cappedSpinePresentation q) →*
      Pi1 (orderCx (QCube (cmpRel (GenusVertex q))))
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  QuotientGroup.lift _ (spineFreeToFullCube q) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    exact spineFreeToFullCube_capped_rel q m)

@[simp] theorem cappedPresentationToFullCube_mk w :
    cappedPresentationToFullCube q (QuotientGroup.mk w) = spineFreeToFullCube q w := rfl
