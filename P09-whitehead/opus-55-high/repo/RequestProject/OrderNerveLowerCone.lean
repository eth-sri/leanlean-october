import RequestProject.OrderNerveConeBall
import RequestProject.OrderNervePosetCoverVertexStars
import RequestProject.PosetCoverLowerInterval


/-! A closed principal lower ideal is literally the order cone on its strict
lower interval. The realized identification respects the boundary inclusion. -/

noncomputable section
namespace FiniteChains.Comb
open scoped Classical

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] (v : Q)
    (e : P ≃o StrictBelow v)

def lowerConeMap : WithTop P → Set.Iic v := WithTop.recTopCoe
  ⟨v, le_rfl⟩ (fun p => ⟨(e p).val, (e p).property.le⟩)


theorem lowerConeMap_bijective : Function.Bijective (lowerConeMap v e) := by
  constructor
  · intro a b h
    induction a using WithTop.recTopCoe with
    | top =>
        induction b using WithTop.recTopCoe with
        | top => rfl
        | coe b => exact ((ne_of_lt (e b).property)
            (congrArg Subtype.val h).symm).elim
    | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact ((ne_of_lt (e a).property) (congrArg Subtype.val h)).elim
        | coe b =>
            exact congrArg _
              (e.injective (Subtype.ext (congrArg (·.val) h)))
  · intro x
    by_cases hx : x.val = v
    · exact ⟨⊤, Subtype.ext hx.symm⟩
    · let p : StrictBelow v := ⟨x.val, lt_of_le_of_ne x.property hx⟩
      exact ⟨(e.symm p), Subtype.ext
        (congrArg (·.val) (e.apply_symm_apply p))⟩

def lowerConeOrderIso : WithTop P ≃o Set.Iic v where
  toEquiv := Equiv.ofBijective (lowerConeMap v e) (lowerConeMap_bijective v e)
  map_rel_iff' := by
    intro a b
    induction a using WithTop.recTopCoe with
    | top =>
        induction b using WithTop.recTopCoe with
        | top => simp
        | coe b =>
            exact iff_of_false (not_le_of_gt (e b).property) (not_le_of_gt (WithTop.coe_lt_top b))
    | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact iff_of_true (e a).property.le le_top
        | coe b =>
            exact e.map_rel_iff.trans WithTop.coe_le_coe.symm

def lowerConeBoundary : P →o Set.Iic v where
  toFun p := ⟨(e p).val, (e p).property.le⟩
  monotone' := fun _ _ h => e.monotone h

theorem lowerConeRealization_boundary x :
    orderNerveRealizationOrderIso (lowerConeOrderIso v e) (orderNerveConeBase P x) =
      orderNerveRealizationMap (lowerConeBoundary v e) (lowerConeBoundary v e).monotone x := by
  change orderNerveRealizationMap _ (lowerConeOrderIso v e).monotone
      (orderNerveRealizationMap _ WithTop.coe_mono x) = _
  rw [orderNerveRealizationMap_comp]
  rfl

variable [Fintype P] [Nonempty P]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (b : orderNerveRealization P ≃ₜ RelativeAttachment.UnitBoundary E)

def lowerConeBallHomeomorph :=
  (orderNerveRealizationOrderIso (lowerConeOrderIso v e)).symm.trans
    (orderNerveWithTopBallHomeomorph b)

theorem lowerConeBallHomeomorph_boundary x :
    lowerConeBallHomeomorph v e b
      (orderNerveRealizationMap (lowerConeBoundary v e) (lowerConeBoundary v e).monotone x) =
      RelativeAttachment.unitBoundaryInclusion E (b x) := by
  rw [← lowerConeRealization_boundary]
  change orderNerveWithTopBallHomeomorph b
      ((orderNerveRealizationOrderIso (lowerConeOrderIso v e)).symm
        (orderNerveRealizationOrderIso (lowerConeOrderIso v e) (orderNerveConeBase P x))) = _
  rw [Homeomorph.symm_apply_apply, orderNerveWithTopBallHomeomorph_boundary]
