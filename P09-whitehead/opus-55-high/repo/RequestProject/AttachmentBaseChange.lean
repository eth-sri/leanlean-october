import RequestProject.AttachmentHomotopyExtension
import Mathlib.Topology.Homotopy.Equiv
import RequestProject.Tac


/-! Actual maps under change of the base of a cell attachment. The first
homotopy inverse is constructed from disk homotopy extension. This file does
not assume that the induced map on attachments is an equivalence. -/

noncomputable section

bwd

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {A D P K Z : Type u}
variable [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace P]
variable [TopologicalSpace K] [TopologicalSpace Z]

def attachmentBaseMap a (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) :=
  desc a i ((⟨old _ i, old_continuous _ i⟩ : C(K, Space (e ∘ a) i)).comp e)
    ⟨cell _ i, cell_continuous _ i⟩
    (fun b => (cell_boundary (e ∘ a) i hi b).symm)


omit [TopologicalSpace A] in
@[simp] theorem attachmentBaseMap_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (e : C(P, K)) (d : D) :
    attachmentBaseMap a i hi e (cell a i d) = cell (e ∘ a) i d := by
  unfold attachmentBaseMap
  rw [desc_cell]
  rfl

omit [TopologicalSpace A] in
theorem attachmentBaseMap_comp {Q : Type u} [TopologicalSpace Q]
    (a : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) (g : C(K, Q)) :
    (attachmentBaseMap (e ∘ a) i hi g).comp (attachmentBaseMap a i hi e) =
      attachmentBaseMap a i hi (g.comp e) := by
  apply hom_ext a i
  · intro p
    rfl
  · intro d
    simp [ContinuousMap.comp_apply, attachmentBaseMap_cell]
    exact (attachmentBaseMap_cell a i hi (g.comp e) d).symm

/-- A jointly continuous pasting on the attachment. The target is curried
in the compact time coordinate, so the base need not be locally compact. -/
def attachmentHomotopyPasting a (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) : C(I × Space a i, Z) :=
  (desc a i ((H.comp ⟨Prod.swap, continuous_swap⟩).curry)
    ((G.comp ⟨Prod.swap, continuous_swap⟩).curry)
    (by aesop)).uncurry.comp
      ⟨Prod.swap, continuous_swap⟩


omit [TopologicalSpace A] in
@[simp] theorem attachmentHomotopyPasting_cell (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) (t : I) (d : D) :
    attachmentHomotopyPasting a i H G h (t, cell a i d) = G (t, d) := by
  simp [attachmentHomotopyPasting, ContinuousMap.comp_apply, ContinuousMap.uncurry_apply, ContinuousMap.coe_mk, Function.uncurry, Prod.swap, desc_cell]
