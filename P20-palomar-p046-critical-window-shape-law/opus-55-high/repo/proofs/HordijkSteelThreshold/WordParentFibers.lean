module

public import proofs.HordijkSteelThreshold.WordGraphCuts

public section

namespace HordijkSteelThreshold
open Classical

variable {L N : ℕ}

variable (u v : BoundedFoodWord L N)

theorem boundedFoodLeft_preimage
    (hv : v ≠ boundedFoodRoot L N) (hp : boundedFoodLeft u = v) :
    ∃ b : Bool, u.val = b :: v.val := by
  have he : foodWordLeft L u.val = v.val := congrArg Subtype.val hp
  have hn : v.val ≠ [] := fun h => hv $ Subtype.ext h
  unfold foodWordLeft at he
  split_ifs at he
  · exact absurd he.symm hn
  · cases hu : u.val <;> simp_all

theorem boundedFoodRight_preimage
    (hv : v ≠ boundedFoodRoot L N) (hp : boundedFoodRight u = v) :
    ∃ b : Bool, u.val = v.val ++ [b] := by
  have he : foodWordRight L u.val = v.val := congrArg Subtype.val hp
  have hn : v.val ≠ [] := fun h => hv $ Subtype.ext h
  unfold foodWordRight at he
  split_ifs at he
  · exact absurd he.symm hn
  · exact ⟨u.val.getLast $ by grind, he ▸ (List.dropLast_append_getLast _).symm⟩


/-- Only nonroot fibers are bounded: contraction gives the food root a large fiber. -/
theorem boundedFoodLeft_fiber_card  (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodLeft u = v)).card ≤ 2 :=
  (Finset.card_le_card_of_injOn Subtype.val (t := Finset.univ.image (· :: v.val)) (fun u hu => by
    obtain ⟨b, hb⟩ := boundedFoodLeft_preimage u v hv (Finset.mem_filter.mp hu).2
    grind) Subtype.val_injective.injOn).trans $ Finset.card_image_le.trans $ by simp

theorem boundedFoodRight_fiber_card  (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodRight u = v)).card ≤ 2 :=
  (Finset.card_le_card_of_injOn Subtype.val (t := Finset.univ.image (v.val ++ [·])) (fun u hu => by
    obtain ⟨b, hb⟩ := boundedFoodRight_preimage u v hv (Finset.mem_filter.mp hu).2
    grind) Subtype.val_injective.injOn).trans $ Finset.card_image_le.trans $ by simp

end HordijkSteelThreshold
