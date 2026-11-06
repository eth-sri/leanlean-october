import Mathlib.Tactic

import RequestProject.Statement
import RequestProject.OrderNerveRealizationCovering

/-! Regularity on actual topological fibers, deduced from order deck transformations. -/

namespace FiniteChains.Comb.IsPosetCover




variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

  (hf : IsPosetCover f)
/-- The realized projection is injective on each of its open-star sheets. -/
theorem realizationMap_injOn_openStar  (v : P) :
    (orderNerveRealizationOpenStar P v).InjOn (orderNerveRealizationMap f hf.mono) := by
  intro x hx y hy hxy
  have hh : hf.vertexOpenStarHomeomorph v ⟨x, hx⟩ =
      hf.vertexOpenStarHomeomorph v ⟨y, hy⟩ := by
    classical grind [FiniteChains.Comb.IsPosetCover.mono, FiniteChains.Comb.IsPosetCover.vertexOpenStarHomeomorph_coe]
  exact congrArg Subtype.val ((hf.vertexOpenStarHomeomorph v).injective hh)

/-- An order deck transformation realizes to a genuine topological deck transformation. -/
theorem realization_deck_commutes  (e : P ≃o P)
    (he : ∀ p, f (e p) = f p) (x : orderNerveRealization P) :
    orderNerveRealizationMap f hf.mono (orderNerveRealizationOrderIso e x) =
      orderNerveRealizationMap f hf.mono x := by
  change orderNerveRealizationMap f hf.mono
    (orderNerveRealizationMap e e.monotone x) = _
  rw [orderNerveRealizationMap_comp]
  have h : (f ∘ e : P → Q) = f := funext he
  simp [h]

/-- Transitivity of order deck transformations on vertex fibers implies regularity
of the actual covering, on all points of all topological fibers. -/
theorem realizationMap_regular 
    (hdeck : ∀ v w : P, f v = f w →
      ∃ e : P ≃o P, (∀ p, f (e p) = f p) ∧ e v = w) :
    Whitehead.Regular
      ⟨orderNerveRealizationMap f hf.mono,
        (orderNerveRealizationMap f hf.mono).hom.continuous⟩ := by
  intro x y hxy
  obtain ⟨v, hxv⟩ := orderNerveRealizationOpenStar_cover P x
  have hx  :=
    (orderNerveRealizationMap_mem_openStar_iff f hf.mono x (f v)).mpr ⟨v, rfl, hxv⟩
  have hy  := hxy ▸ hx
  obtain ⟨w, hw, hyw⟩ :=
    (orderNerveRealizationMap_mem_openStar_iff f hf.mono y (f v)).mp hy
  obtain ⟨e, he, hev⟩ := hdeck v w hw.symm
  refine ⟨orderNerveRealizationOrderIso e, hf.realization_deck_commutes e he, ?_⟩
  have hxe : orderNerveRealizationOrderIso e x ∈ orderNerveRealizationOpenStar P w := by
    rw [← hev]
    change 0 < orderNerveRealizationCoordinates P
      (orderNerveRealizationMap e e.monotone x) (e v)
    rw [orderNerveRealizationCoordinates_map_injective e e.monotone e.injective]
    exact hxv
  exact hf.realizationMap_injOn_openStar w hxe hyw
    ((hf.realization_deck_commutes e he x).trans hxy)

end FiniteChains.Comb.IsPosetCover

