import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.ExplicitRelativeAttachment

/-! An isomorphism of actual attaching diagrams gives an actual
homeomorphism of their attachment spaces. Both old and cell maps are
specified exactly, which is needed for the later relative construction. -/

noncomputable section
namespace FiniteChains.RelativeAttachment


variable {A A' P P' D D' : Type u}
  [TopologicalSpace P] [TopologicalSpace P']
  [TopologicalSpace D] [TopologicalSpace D']
  (r : A → P) (i : A → D) (r' : A' → P') (i' : A' → D')
  (eA : A ≃ A') (eP : P ≃ₜ P') (eD : D ≃ₜ D')
  (hr : ∀ a, eP (r a) = r' (eA a))
  (hi : ∀ a, eD (i a) = i' (eA a))
  (hi' : Function.Injective i')

def attachmentDiagramMap  :=
  desc r i
    ((⟨old r' i', old_continuous r' i'⟩ : C(P', Space r' i')).comp eP.toContinuousMap)
    ((⟨cell r' i', cell_continuous r' i'⟩ : C(D', Space r' i')).comp eD.toContinuousMap)
    (fun a => by
      simp_all [FiniteChains.RelativeAttachment.cell_boundary])

@[simp] theorem attachmentDiagramMap_old (p : P) :
    attachmentDiagramMap r i r' i' eA eP eD hr hi hi' (old r i p) =
      old r' i' (eP p) := rfl

@[simp] theorem attachmentDiagramMap_cell (d : D) :
    attachmentDiagramMap r i r' i' eA eP eD hr hi hi' (cell r i d) =
      cell r' i' (eD d) := desc_cell ..

include hr in
theorem attachmentDiagram_inverse_old (a' : A') :
    eP.symm (r' a') = r (eA.symm a') := by
  apply eP.injective
  rw [eP.apply_symm_apply, hr, eA.apply_symm_apply]

include hi in
theorem attachmentDiagram_inverse_boundary (a' : A') :
    eD.symm (i' a') = i (eA.symm a') := by
  apply eD.injective
  rw [eD.apply_symm_apply, hi, eA.apply_symm_apply]

variable (hi₀ : Function.Injective i)
def attachmentDiagramHomeomorph  : Space r i ≃ₜ Space r' i' where
  toFun := attachmentDiagramMap r i r' i' eA eP eD hr hi hi'
  invFun := attachmentDiagramMap r' i' r i eA.symm eP.symm eD.symm
    (attachmentDiagram_inverse_old r r' eA eP hr)
    (attachmentDiagram_inverse_boundary i i' eA eD hi) hi₀
  left_inv z := by
    obtain ⟨z, rfl⟩ := quotientMap_surjective r i z
    cases z with
    | inl p =>
        dsimp [FiniteChains.RelativeAttachment.quotientMap]
        simp 
    | inr d =>
        dsimp [FiniteChains.RelativeAttachment.quotientMap]
        simp only [attachmentDiagramMap_cell, Homeomorph.symm_apply_apply]
  right_inv z := by
    obtain ⟨z, rfl⟩ := quotientMap_surjective r' i' z
    cases z with
    | inl p =>
        dsimp [FiniteChains.RelativeAttachment.quotientMap]
        simp 
    | inr d =>
        dsimp [FiniteChains.RelativeAttachment.quotientMap]
        simp only [attachmentDiagramMap_cell, Homeomorph.apply_symm_apply]
  continuous_toFun := (attachmentDiagramMap r i r' i' eA eP eD hr hi hi').continuous
  continuous_invFun := (attachmentDiagramMap r' i' r i eA.symm eP.symm eD.symm
    (attachmentDiagram_inverse_old r r' eA eP hr)
    (attachmentDiagram_inverse_boundary i i' eA eD hi) hi₀).continuous

@[simp] theorem attachmentDiagramHomeomorph_old  (p : P) :
    attachmentDiagramHomeomorph r i r' i' eA eP eD hr hi hi' hi₀ (old r i p) =
      old r' i' (eP p) := rfl

@[simp] theorem attachmentDiagramHomeomorph_cell  (d : D) :
    attachmentDiagramHomeomorph r i r' i' eA eP eD hr hi hi' hi₀ (cell r i d) =
      cell r' i' (eD d) := attachmentDiagramMap_cell r i r' i' eA eP eD hr hi hi' d

/-- Change each member of a topological sum by a specified homeomorphism. -/
def sigmaFiberHomeomorph {J : Type u} {X Y : J → Type u}
    [∀ j, TopologicalSpace (X j)] [∀ j, TopologicalSpace (Y j)]
    (e : ∀ j, X j ≃ₜ Y j) : (Σ j, X j) ≃ₜ (Σ j, Y j) where
  toFun z := ⟨z.1, e z.1 z.2⟩
  invFun z := ⟨z.1, (e z.1).symm z.2⟩
  left_inv := by grind [Homeomorph.symm_apply_apply]
  right_inv := by grind [Homeomorph.apply_symm_apply]
  continuous_toFun := continuous_sigma (fun j => continuous_sigmaMk.comp (e j).continuous)
  continuous_invFun := continuous_sigma (fun j => continuous_sigmaMk.comp (e j).symm.continuous)

end FiniteChains.RelativeAttachment
