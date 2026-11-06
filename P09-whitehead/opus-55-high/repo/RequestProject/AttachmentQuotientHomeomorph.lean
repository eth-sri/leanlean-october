import RequestProject.ExplicitRelativeAttachment


/-! Identify the explicit attachment with an actual quotient covered by
an old piece and disk pieces. Boundary identifications and separation of
the new interiors are sufficient; closedness of an infinite union is
never assumed. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open Topology

universe u
variable {A B D Y : Type u} [TopologicalSpace B] [TopologicalSpace D]
  [TopologicalSpace Y] (r : A → B) (i : A → D)
  (f : C(B, Y)) (g : C(D, Y))
  (hbd : ∀ a, f (r a) = g (i a))
  (hf : Function.Injective f)
  (hsep : ∀ d, g d ∈ Set.range f ↔ d ∈ Set.range i)
  (hnew : ∀ d e, d ∉ Set.range i → e ∉ Set.range i → g d = g e → d = e)
  (hq : IsQuotientMap (Sum.elim f g))

def attachmentQuotientHomeomorph : Space r i ≃ₜ Y := by
  let F := desc r i f g hbd
  have hcomp : F ∘ quotientMap r i = Sum.elim f g := by
    funext z
    rcases z with b | d
    · rfl
    · exact desc_cell r i f g hbd d
  have hFq := IsQuotientMap.of_comp
    (quotientMap_continuous r i) F.continuous (hcomp.symm ▸ hq)
  have hFi : Function.Injective F := by
    rintro (b | d) (c | e) he
    · tauto
    · have hd : g e.val ∈ Set.range f := by tauto
      grind
    · have hd : g d.val ∈ Set.range f := by tauto
      grind
    · exact congrArg Sum.inr (Subtype.ext (hnew d.val e.val d.property e.property he))
  let E := Equiv.ofBijective F ⟨hFi, hFq.surjective⟩
  refine { E with continuous_toFun := F.continuous, continuous_invFun := ?_ }
  apply hFq.continuous_iff.mpr
  change Continuous (E.symm ∘ F)
  have he : E.symm ∘ F = id := funext E.symm_apply_apply
  rw [he]
  exact continuous_id

@[simp] theorem attachmentQuotientHomeomorph_old b :
    attachmentQuotientHomeomorph r i f g hbd hf hsep hnew hq (old r i b) = f b :=
  by rfl

@[simp] theorem attachmentQuotientHomeomorph_cell d :
    attachmentQuotientHomeomorph r i f g hbd hf hsep hnew hq (cell r i d) = g d :=
  desc_cell r i f g hbd d
