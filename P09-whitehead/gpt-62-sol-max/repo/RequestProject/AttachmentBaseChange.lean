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

def attachmentBaseMap (a : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) : C(Space a i, Space (e ∘ a) i) :=
  desc a i ((Space.oldMap (e ∘ a) i).comp e)
    (Space.cellMap (e ∘ a) i)
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
    simp only [ContinuousMap.comp_apply, attachmentBaseMap_cell]
    exact (attachmentBaseMap_cell a i hi (g.comp e) d).symm

/-- A jointly continuous pasting on the attachment. The target is curried
in the compact time coordinate, so the base need not be locally compact. -/
def attachmentHomotopyPasting (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) : C(I × Space a i, Z) :=
  (desc a i (H.comp .prodSwap).curry
    (G.comp .prodSwap).curry
    (fun b => ContinuousMap.ext (fun t => h t b))).uncurry.comp .prodSwap


omit [TopologicalSpace A] in
@[simp] theorem attachmentHomotopyPasting_cell (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) (t : I) (d : D) :
    attachmentHomotopyPasting a i H G h (t, cell a i d) = G (t, d) := by
  simp [attachmentHomotopyPasting, ContinuousMap.comp_apply, ContinuousMap.uncurry_apply, desc_cell]

/-- Compatible homotopies on the base and the new cell paste to a homotopy on the attachment. -/
def attachmentHomotopy (a : A → P) (i : A → D) {f g : C(Space a i, Z)}
    (H : C(I × P, Z)) (G : C(I × D, Z)) (h : ∀ t b, H (t, a b) = G (t, i b))
    (h₀ : (∀ p, H (0, p) = f (old a i p)) ∧ ∀ d, G (0, d) = f (cell a i d))
    (h₁ : (∀ p, H (1, p) = g (old a i p)) ∧ ∀ d, G (1, d) = g (cell a i d)) : f.Homotopy g where
  toContinuousMap := attachmentHomotopyPasting a i H G h
  map_zero_left z := by
    exact attachment_induction z h₀.1 fun d =>
      (attachmentHomotopyPasting_cell a i H G h 0 d).trans (h₀.2 d)
  map_one_left z := by
    exact attachment_induction z h₁.1 fun d =>
      (attachmentHomotopyPasting_cell a i H G h 1 d).trans (h₁.2 d)

end FiniteChains.RelativeAttachment
