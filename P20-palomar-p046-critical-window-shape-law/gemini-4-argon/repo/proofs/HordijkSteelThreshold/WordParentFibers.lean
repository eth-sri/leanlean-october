module

public import proofs.HordijkSteelThreshold.WordGraphCuts

@[expose] public section

namespace HordijkSteelThreshold
open Classical

theorem boundedFoodLeft_preimage {L N : ℕ} (u v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) (hp : boundedFoodLeft u = v) :
    ∃ b : Bool, u.val = b :: v.val := by
  have he : foodWordLeft L u.val = v.val := congrArg Subtype.val hp
  have hs : ¬ u.val.length ≤ L + 1 := fun h => hv (Subtype.ext (by simpa [foodWordLeft, h, boundedFoodRoot] using he.symm))
  rw [foodWordLeft, ite_eq_right hs] at he
  cases hu : u.val with
  | nil => simp [hu] at hs
  | cons b t => exact ⟨b, by simpa [hu] using congrArg (List.cons b) he⟩

theorem boundedFoodRight_preimage {L N : ℕ} (u v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) (hp : boundedFoodRight u = v) :
    ∃ b : Bool, u.val = v.val ++ [b] := by
  have he : foodWordRight L u.val = v.val := congrArg Subtype.val hp
  have hs : ¬ u.val.length ≤ L + 1 := fun h => hv (Subtype.ext (by simpa [foodWordRight, h, boundedFoodRoot] using he.symm))
  rw [foodWordRight, ite_eq_right hs] at he
  have hu : u.val ≠ [] := fun h => by simp [h] at hs
  exact ⟨u.val.getLast hu, he ▸ (List.dropLast_append_getLast hu).symm⟩

theorem boundedFoodLeft_fiber_card {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodLeft u = v)).card ≤ 2 := by
  refine (Finset.card_le_card_of_injOn Subtype.val (t := (Finset.univ : Finset Bool).image fun b => b :: v.val)
    (fun u hu => ?_) fun _ _ _ _ h => Subtype.ext h).trans (Finset.card_image_le.trans (by decide))
  obtain ⟨b, hb⟩ := boundedFoodLeft_preimage u v hv (Finset.mem_filter.mp hu).2
  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb.symm⟩

theorem boundedFoodRight_fiber_card {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodRight u = v)).card ≤ 2 := by
  refine (Finset.card_le_card_of_injOn Subtype.val (t := (Finset.univ : Finset Bool).image fun b => v.val ++ [b])
    (fun u hu => ?_) fun _ _ _ _ h => Subtype.ext h).trans (Finset.card_image_le.trans (by decide))
  obtain ⟨b, hb⟩ := boundedFoodRight_preimage u v hv (Finset.mem_filter.mp hu).2
  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb.symm⟩

end HordijkSteelThreshold
