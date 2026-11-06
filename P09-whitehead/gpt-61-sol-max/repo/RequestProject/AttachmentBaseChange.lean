import Mathlib.Tactic

import RequestProject.AttachmentHomotopyExtension
import Mathlib.Topology.Homotopy.Equiv

/-! Actual maps under change of the base of a cell attachment. The first
homotopy inverse is constructed from disk homotopy extension. This file does
not assume that the induced map on attachments is an equivalence. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

variable {A D P K Z : Type u}
  [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace P]
  [TopologicalSpace K] [TopologicalSpace Z]

def attachmentBaseMap (a : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K))  :=
  desc a i ((⟨old (e ∘ a) i, old_continuous (e ∘ a) i⟩ : C(K, Space (e ∘ a) i)).comp e)
    ⟨cell (e ∘ a) i, cell_continuous (e ∘ a) i⟩
    (fun b => (cell_boundary (e ∘ a) i hi b).symm)

section
omit [TopologicalSpace A]


@[simp] theorem attachmentBaseMap_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (e : C(P, K)) (d : D) :
    attachmentBaseMap a i hi e (cell a i d) = cell (e ∘ a) i d := by
  unfold attachmentBaseMap
  rw [desc_cell]
  rfl

theorem attachmentBaseMap_comp {Q : Type u} [TopologicalSpace Q]
    (a : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) (g : C(K, Q)) :
    (attachmentBaseMap (e ∘ a) i hi g).comp (attachmentBaseMap a i hi e) =
      attachmentBaseMap a i hi (g.comp e) := by
  aesop (add unsafe apply [FiniteChains.RelativeAttachment.hom_ext, FiniteChains.RelativeAttachment.attachmentBaseMap_cell, symm])
end

/-- A jointly continuous pasting on the attachment. The target is curried
in the compact time coordinate, so the base need not be locally compact. -/
def attachmentHomotopyPasting (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b))  :=
  (desc a i ((H.comp ⟨Prod.swap, continuous_swap⟩).curry)
    ((G.comp ⟨Prod.swap, continuous_swap⟩).curry)
    (fun b => ContinuousMap.ext (fun t => h t b))).uncurry.comp
      ⟨Prod.swap, continuous_swap⟩

section
omit [TopologicalSpace A]


@[simp] theorem attachmentHomotopyPasting_cell (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) (t : I) (d : D) :
    attachmentHomotopyPasting a i H G h (t, cell a i d) = G (t, d) := by simp_all [attachmentHomotopyPasting]
end

end FiniteChains.RelativeAttachment
