module

public import RequestProject.DiskPresentationExtensionHomeomorph
public import RequestProject.PresWordDiskNaturality

@[expose] public section

/-! Every genuine labelled presentation-word embedding is realized as
an actual relative attachment of its new generators and new relators.
All compatibility inputs of the generic construction are discharged by
the previously constructed circle and rose naturality maps. -/

noncomputable section
namespace FiniteChains.PresModel.PresWordEmbedding
open RelativeAttachment ClassicalGraphModel
open scoped Classical

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
    (h : PresWordEmbedding w v) (hw : ∀ j, w j ≠ []) (hv : ∀ k, v k ≠ [])

def classicalDiskExtension :
    Whitehead.DiskExtensionModel (ClassicalPresWordDisks w hw) (ClassicalPresWordDisks v hv) :=
  DiskPresentationExtension.extensionModel h.gen h.cell
    (classicalPresWordAttaching w hw) (classicalPresWordAttaching v hv)
    (h.classicalPresWordAttaching_natural hw hv)

theorem classicalDiskExtension_map : (h.classicalDiskExtension hw hv).map =
    h.classicalWordDiskMap hw hv := by
  change (DiskPresentationExtension.extensionModel h.gen h.cell
    (classicalPresWordAttaching w hw) (classicalPresWordAttaching v hv)
    (h.classicalPresWordAttaching_natural hw hv)).map = _
  rw [DiskPresentationExtension.extensionModel_map]
  apply hom_ext (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J _)
  · intro x
    rfl
  · intro d
    rw [DiskPresentationExtension.sourceMap_cell, classicalWordDiskMap_cell]

theorem classicalDiskExtension_nonempty_of_generator (b : B) (hb : b ∉ Set.range h.gen) :
    Nonempty (h.classicalDiskExtension hw hv).oneCells := ⟨⟨b, hb⟩⟩

theorem classicalDiskExtension_nonempty_of_relator (k : K) (hk : k ∉ Set.range h.cell) :
    Nonempty (h.classicalDiskExtension hw hv).twoCells := ⟨⟨k, hk⟩⟩

theorem classicalDiskExtension_finite [Finite B] [Finite K] :
    Finite (h.classicalDiskExtension hw hv).oneCells ∧
      Finite (h.classicalDiskExtension hw hv).twoCells :=
  ⟨inferInstanceAs (Finite {b : B // b ∉ Set.range h.gen}),
    inferInstanceAs (Finite {k : K // k ∉ Set.range h.cell})⟩
