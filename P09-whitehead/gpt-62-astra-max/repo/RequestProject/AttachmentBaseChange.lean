module

public import RequestProject.AttachmentHomotopyExtension
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-! Actual maps under change of the base of a cell attachment. The first
homotopy inverse is constructed from disk homotopy extension. This file does
not assume that the induced map on attachments is an equivalence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {A D P K Z : Type u}
variable [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace P]
variable [TopologicalSpace K] [TopologicalSpace Z]

variable (a : A → P) (i : A → D) (hi : Function.Injective i) (e : C(P, K))

def attachmentBaseMap :=
  desc a i ((⟨old (e ∘ a) i, old_continuous (e ∘ a) i⟩ : C(K, Space (e ∘ a) i)).comp e)
    ⟨cell (e ∘ a) i, cell_continuous (e ∘ a) i⟩
    (fun b => (cell_boundary (e ∘ a) i hi b).symm)

omit [TopologicalSpace A] in
@[simp] theorem attachmentBaseMap_old (p : P) :
    attachmentBaseMap a i hi e (old a i p) = old _ i (e p) := rfl

omit [TopologicalSpace A] in
@[simp] theorem attachmentBaseMap_cell (d : D) :
    attachmentBaseMap a i hi e (cell a i d) = cell _ i d := by
  unfold attachmentBaseMap
  rw [desc_cell]
  rfl

omit [TopologicalSpace A] in
theorem attachmentBaseMap_comp {Q : Type u} [TopologicalSpace Q]
    (a : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) (g : C(K, Q)) :
    (attachmentBaseMap _ i hi g).comp (attachmentBaseMap a i hi e) =
      attachmentBaseMap a i hi (g.comp e) := by
  apply hom_ext a i
  · solve_by_elim
  · intro d
    simp only [ContinuousMap.comp_apply, attachmentBaseMap_cell]
    exact (attachmentBaseMap_cell a i hi (g.comp e) d).symm

variable (a : A → P)
    (i : A → D)
    (H : C(I × P, Z))
    (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b))

/-- A jointly continuous pasting on the attachment. The target is curried
in the compact time coordinate, so the base need not be locally compact. -/
def attachmentHomotopyPasting :=
  (desc a i ((H.comp ⟨Prod.swap, continuous_swap⟩).curry)
    ((G.comp ⟨Prod.swap, continuous_swap⟩).curry)
    (fun b => ContinuousMap.ext (fun t => h t b))).uncurry.comp
      ⟨Prod.swap, continuous_swap⟩

variable (t : I)

omit [TopologicalSpace A] in
@[simp] theorem attachmentHomotopyPasting_old (p : P) :
    attachmentHomotopyPasting a i H G h (t, old a i p) = H (t, p) := rfl

omit [TopologicalSpace A] in
@[simp] theorem attachmentHomotopyPasting_cell (d : D) :
    attachmentHomotopyPasting a i H G h (t, cell a i d) = G (t, d) := by
  change desc (Z := C(I, Z)) a i _ _ _ (cell a i d) t = _
  rw [desc_cell]
  rfl

end FiniteChains.RelativeAttachment
