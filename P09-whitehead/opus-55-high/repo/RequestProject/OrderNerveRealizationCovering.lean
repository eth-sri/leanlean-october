import RequestProject.OrderNerveRealizationStarSheets
import Mathlib.Topology.Covering.Basic


/-! Actual topological coverings obtained from the already constructed open-star sheets. -/

namespace FiniteChains.Comb
open Topology
open scoped Classical

theorem open_iff_of_sheet {E X}
    [TopologicalSpace E] [TopologicalSpace X] (f : C(E, X))
    {U} {V} (hU : IsOpen U) (hV : IsOpen V)
    (e : U ≃ₜ V) (he : ∀ z, (e z).val = f z.val)
    {W} (hW : W ⊆ V) :
    IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U) := by
  constructor
  · intro h
    exact (h.preimage f.continuous).inter hU
  · intro h
    have hp : IsOpen (e ⁻¹' (Subtype.val ⁻¹' W)) := by
      have hh := h.preimage (continuous_subtype_val : Continuous (Subtype.val : U → E))
      convert hh using 1
      grind
    have hv := e.isOpen_preimage.mp hp
    have hi := hV.isOpenMap_subtype_val _ hv
    have hr : (Subtype.val : V → X) '' (Subtype.val ⁻¹' W) = W := by
      simp_all
    simp_all

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A sheet over a chosen lifted vertex, with its target identified with the chosen base star. -/
noncomputable def realizationSheetHomeomorph (hf : IsPosetCover f) q
    (v : {p : P // f p = q}) :
    orderNerveRealizationOpenStar P v.val ≃ₜ orderNerveRealizationOpenStar Q q :=
  (hf.vertexOpenStarHomeomorph v.val).trans
    (Homeomorph.setCongr (by grind))

theorem realizationSheetHomeomorph_coe (hf : IsPosetCover f) q
    v z :
    (hf.realizationSheetHomeomorph q v z).val = orderNerveRealizationMap f hf.mono z.val :=
  hf.vertexOpenStarHomeomorph_coe v.val z

set_option maxHeartbeats 600000 in
/-- Every actual open vertex star is an evenly covered neighborhood. -/
theorem realizationMap_evenlyCovered (hf : IsPosetCover f) (q : Q)
    (x : orderNerveRealization Q) (hx : x ∈ orderNerveRealizationOpenStar Q q) :
    IsEvenlyCovered (orderNerveRealizationMap f hf.mono) x
      (orderNerveRealizationMap f hf.mono ⁻¹' {x}) := by
  let I := {p : P // f p = q}
  letI : TopologicalSpace I := ⊥
  letI : DiscreteTopology I := ⟨rfl⟩
  cases' hf.surj q with v hv
  letI : Nonempty I := by tauto
  letI : Nonempty (orderNerveRealization P) := ⟨orderNerveRealizationVertex v⟩
  let F : C(orderNerveRealization P, orderNerveRealization Q) :=
    ⟨orderNerveRealizationMap f hf.mono, (orderNerveRealizationMap f hf.mono).hom.continuous⟩
  let U : I → Set (orderNerveRealization P) := fun i => orderNerveRealizationOpenStar P i.val
  let V := orderNerveRealizationOpenStar Q q
  let e : ∀ i, U i ≃ₜ V := hf.realizationSheetHomeomorph q
  have he : ∀ i z, (e i z).val = F z.val :=
    hf.realizationSheetHomeomorph_coe q
  let t := IsOpen.trivializationDiscrete (f := F) U V
    (orderNerveRealizationOpenStar_isOpen Q q)
    (fun i {_} hW => open_iff_of_sheet F (orderNerveRealizationOpenStar_isOpen P i.val)
      (orderNerveRealizationOpenStar_isOpen Q q) _ (he i) hW)
    (by
      intro i a ha b hb hab
      have hh : e i ⟨a, ha⟩ = e i ⟨b, hb⟩ :=
        by grind
      simp_all)
    (by
      intro i y hy
      refine ⟨((e i).symm ⟨y, hy⟩).val, by simp, ?_⟩
      rw [← he i, (e i).apply_symm_apply])
    (by
      intro i j hij
      exact hf.realizationOpenStar_disjoint (by grind)
        (i.property.trans j.property.symm))
    (by
      intro y hy
      obtain ⟨p, hp, hyp⟩ := (orderNerveRealizationMap_mem_openStar_iff f hf.mono y q).mp hy
      aesop)
  exact (IsEvenlyCovered.of_trivialization (t := t) hx).to_isEvenlyCovered_preimage

/-- The realization of every poset covering is a genuine Mathlib covering map. -/
theorem realizationMap_isCoveringMap (hf : IsPosetCover f) :
    IsCoveringMap (orderNerveRealizationMap f hf.mono) := by
  intro x
  cases' orderNerveRealizationOpenStar_cover Q x with q hq
  exact hf.realizationMap_evenlyCovered q x hq
