module

public import RequestProject.OrderNerveLowerCone
public import Mathlib.Order.Hom.WithTopBot

@[expose] public section

/-! The actual radial cone/disk identification commutes with a relabelling
of its boundary poset when the boundary parametrizations agree. -/

noncomputable section
namespace FiniteChains.Comb
open RelativeAttachment
open scoped Classical unitInterval

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q)

theorem orderNerveRadialCone_natural (r : I) (x : orderNerveRealization P) :
    orderNerveRealizationOrderIso e.withTopCongr (orderNerveRadialCone P (r, x)) =
      orderNerveRadialCone Q (r, orderNerveRealizationOrderIso e x) := by
  apply orderNerveRealizationCoordinates_injective (WithTop Q)
  funext q
  obtain ⟨p, rfl⟩ := e.withTopCongr.surjective q
  change orderNerveRealizationCoordinates _
      (orderNerveRealizationMap e.withTopCongr e.withTopCongr.monotone
        (orderNerveRadialCone P (r, x))) (e.withTopCongr p) = _
  rw [orderNerveRealizationCoordinates_map_injective _ _ e.withTopCongr.injective]
  induction p using WithTop.recTopCoe with
  | top =>
      simp
  | coe p =>
      change orderNerveRealizationCoordinates _ (orderNerveRadialCone P _) p =
        orderNerveRealizationCoordinates _
          (orderNerveRadialCone Q _) (e p)
      rw [orderNerveRadialCone_coordinate, orderNerveRadialCone_coordinate]
      exact congrArg _
        (orderNerveRealizationCoordinates_map_injective e e.monotone e.injective x p).symm

variable [Fintype P] [Nonempty P] [Fintype Q] [Nonempty Q]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  (bP : orderNerveRealization P ≃ₜ UnitBoundary E)
  (bQ : orderNerveRealization Q ≃ₜ UnitBoundary E)
  (hb : ∀ x, bQ (orderNerveRealizationOrderIso e x) = bP x)

include hb in
theorem orderNerveWithTopBallHomeomorph_natural (x : orderNerveRealization (WithTop P)) :
    orderNerveWithTopBallHomeomorph bQ (orderNerveRealizationOrderIso e.withTopCongr x) =
      orderNerveWithTopBallHomeomorph bP x := by
  obtain ⟨⟨r, y⟩, rfl⟩ := orderNerveRadialCone_surjective P x
  simp [orderNerveRadialCone_natural, orderNerveWithTopBallHomeomorph_radial, hb]

end FiniteChains.Comb
