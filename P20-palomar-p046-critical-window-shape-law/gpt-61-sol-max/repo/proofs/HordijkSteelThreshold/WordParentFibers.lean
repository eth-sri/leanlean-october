import proofs.HordijkSteelThreshold.WordGraphCuts

namespace HordijkSteelThreshold
variable {L N : ℕ} (u v : BoundedFoodWord L N)
theorem boundedFoodParent_preimage (b : Bool)
    (hv : v ≠ boundedFoodRoot L N) (hp : wordEdgeParent (u,b) = v) :
    ∃ bit : Bool, u.val = if b then v.val ++ [bit] else bit :: v.val := by
  have he := congrArg Subtype.val hp
  have hs : ¬ u.val.length ≤ L + 1 := by
    grind [wordEdgeParent, boundedFoodLeft, boundedFoodRight, foodWordLeft, foodWordRight, boundedFoodRoot]
  cases b
  · change foodWordLeft L u.val = v.val at he
    rw [foodWordLeft, ite_eq_right hs] at he
    cases hu : u.val <;> simp_all

  · change foodWordRight L u.val = v.val at he
    rw [foodWordRight, ite_eq_right hs] at he
    have hu : u.val ≠ [] := by intro h; simp_all
    refine ⟨u.val.getLast hu, ?_⟩
    simpa [← he] using (List.dropLast_append_getLast hu).symm

theorem boundedFoodParent_fiber_card (hv : v ≠ boundedFoodRoot L N) (b : Bool) :
    (Finset.univ.filter (fun u : _ => wordEdgeParent (u,b) = v)).card ≤ 2 := by
  let target := Finset.univ.image fun bit : Bool => if b then v.val ++ [bit] else bit :: v.val
  have hc : (Finset.univ.filter fun u : _ => wordEdgeParent (u,b) = v).card ≤
      target.card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro u hu
      simpa [target, eq_comm, or_comm] using
        boundedFoodParent_preimage u v b hv (Finset.mem_filter.mp hu).2
    · exact Set.injOn_subtype_val

  exact hc.trans (Finset.card_image_le.trans (by decide))
end HordijkSteelThreshold
