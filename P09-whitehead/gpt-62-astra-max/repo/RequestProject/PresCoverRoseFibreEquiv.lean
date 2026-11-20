module

public import RequestProject.PresCylinderRoseCover
public import RequestProject.ConeAdjBaseCover

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w)

/-- The actual rose-preimage fibre is exactly the corresponding presentation-cover fibre. -/
noncomputable def presCoverRoseFibreEquiv (x : Rose α) :
    {p : cylinderCoverRoseSet w _ //
      cylinderCoverRoseEnd w (coneAdjCoverBaseEnd f) p = x} ≃
    {p : P // f p = iRose w x} where
  toFun p := ⟨p.val.val.val, by
    have h := cylinderCoverRoseEnd_projection w _ p.val
    rw [p.property] at h
    exact (coneAdjCoverBaseEnd_spec f p.val.val).symm.trans (congrArg ConeAdj.inc h.symm)⟩
  invFun p := by
    let b : {p : P // f p ∈ coneAdjBaseSet} :=
      ⟨p.val, cylIn _ x, p.property.symm⟩
    have hb :=
      Sum.inl.inj ((coneAdjCoverBaseEnd_spec f b).trans p.property)
    let q : cylinderCoverRoseSet w _ := ⟨b, x, hb⟩
    refine ⟨q, ?_⟩
    grind [cylIn_injective, cylinderCoverRoseEnd_projection]
  left_inv p := rfl
  right_inv p := rfl

end FiniteChains.PresModel
