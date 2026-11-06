import RequestProject.DiskPresentationExtensionHomeomorph
import RequestProject.PresWordDiskNaturality


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
    _ _
    (h.classicalPresWordAttaching_natural hw hv)




theorem classicalDiskExtension_finite [Finite B] [Finite K] :
    Finite (h.classicalDiskExtension hw hv).oneCells ∧
      Finite (h.classicalDiskExtension hw hv).twoCells :=
  ⟨inferInstanceAs (Finite {b : B // b ∉ Set.range h.gen}),
    inferInstanceAs (Finite {k : K // k ∉ Set.range h.cell})⟩
